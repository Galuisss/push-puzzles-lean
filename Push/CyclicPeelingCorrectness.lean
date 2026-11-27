/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicPeelingProgram
public import Push.CyclicPeelingCompleteness

/-! Full one-round physical equivalence with the actual next quota vector and every future source scan. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem turn_holes (w h : ℕ) (s : State w h) :
    holes ((turnGeometry w h).state s) = (holes s).map (turnEmbedding w h) := by
  ext q
  obtain ⟨p, rfl⟩ := (turnGeometry w h).cells.surjective q
  simp only [mem_holes, GridIsometry.mem_boxes, Finset.mem_map, turnEmbedding,
    Equiv.toEmbedding_apply, (turnGeometry w h).cells.injective.eq_iff, exists_eq_right]

/-- The complete actual dock trajectory turns into the literal next live source trajectory. -/
theorem turn_dock_reachable (r : ColumnScan.Input)
    {finish : State (dock r).outputWidth (dock r).outputHeight}
    (hf : Reachable (dock r).compile.board none (dock r).compile.initial finish) :
    Reachable (nextSource r).board none (nextSource r).initial
      ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state finish) := by
  let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
  have h := (e.reachable hf).reboard (B' := (nextSource r).board) (by
    simp only [GridIsometry.board, Push.Instance.board, Push.Instance.toStorage]
    rfl)
  have hi : e.state (dock r).compile.initial = (nextSource r).initial := by
    exact (GridIsometry.state_trans _ _ _).symm
  exact hi ▸ h

/-- Every original source witness gives one next-source corner accepting all prescribed later scans. -/
private theorem next_peeling_complete (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    {s : State r.width r.height} (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hp : s.player = r.sourceCorner)
    (haccept : Scan.Accepts
      (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows) ++ tail) (holes s)) :
    ∃ t : State (dock r).outputHeight (dock r).outputWidth,
      Reachable (nextSource r).board none (nextSource r).initial t ∧
      t.player = (nextSource r).target ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail) (holes t) := by
  rw [List.append_assoc] at haccept
  obtain ⟨E, hread, htail⟩ := (Scan.accepts_append_iff _ _ _).mp haccept
  obtain ⟨finish, hf, hfp, ha⟩ := peeling_complete r hr hp hread rows hlen tail hbound htail
  let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
  refine ⟨e.state finish, turn_dock_reachable r hf, congrArg e.cells hfp, ?_⟩
  have ht := (accepts_turn_iff _ (unturnedProgram_bounded r rows hlen tail hbound) _).mpr ha
  have hh := turn_holes (dock r).outputWidth (dock r).outputHeight finish
  have ht' : Scan.Accepts (peeledProgram r rows tail) (holes (e.state finish)) := hh.symm ▸ ht
  unfold Scan.Accepts at ht' ⊢
  simpa only [peeledProgram_eval r rows hlen tail] using ht'

/-- Peeling one read round preserves the complete corner-acceptance language in both directions. -/
theorem next_peeling_iff (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i) :
    (∃ t : State (dock r).outputHeight (dock r).outputWidth,
      Reachable (nextSource r).board none (nextSource r).initial t ∧
      t.player = (nextSource r).target ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail) (holes t)) ↔
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows) ++ tail) (holes s) := by
  constructor
  · rintro ⟨t, hr, hp, ha⟩
    apply peeling_sound r rows hlen tail hbound hr hp
    unfold Scan.Accepts at ha ⊢
    simpa only [peeledProgram_eval r rows hlen tail] using ha
  · rintro ⟨s, hr, hp, ha⟩
    exact next_peeling_complete r rows hlen tail hbound hr hp ha

end PushPuzzle.Push.Cyclic
