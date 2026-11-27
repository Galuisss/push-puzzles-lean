/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeTransport
public import Push.CyclicStaticSuffix

/-! Whole-run overpayments project through the actual translated source rectangle. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction Adjacent)
open Push.Cyclic

variable (r : Push.ColumnScan.Input)

private theorem source_adjacent (d : Direction) {p q : Cell r.width r.height} (ha : Adjacent d p q) :
    Adjacent d (sourceEmbedding r p) (sourceEmbedding r q) := by
  apply (PushFS.adjacent_iff_coordinates d _ _).mpr
  constructor
  · rw [sourceEmbedding_lane, sourceEmbedding_lane]
    exact congrArg (sourceLane d) ha.lane
  · have hh := ha.position
    cases d <;> simp only [Direction.position, sourceEmbedding_x, sourceEmbedding_y] at hh ⊢ <;> omega

private theorem source_adjacent_reflect (d : Direction) {p q : Cell r.width r.height}
    (ha : Adjacent d (sourceEmbedding r p) (sourceEmbedding r q)) : Adjacent d p q := by
  apply (PushFS.adjacent_iff_coordinates d _ _).mpr
  have hl := ha.lane
  have hp := ha.position
  constructor
  · cases d <;> simp only [Direction.lane, sourceEmbedding_x, sourceEmbedding_y] at hl ⊢ <;> omega
  · cases d <;> simp only [Direction.position, sourceEmbedding_x, sourceEmbedding_y] at hp ⊢ <;> omega

private theorem Read.source_lift {side : Direction} {lane quota : ℕ}
    {E F : Finset (Cell r.width r.height)} (H : Read side lane quota E F)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hoff : ∀ q ∈ A, side.lane q ≠ sourceLane side lane) :
    Read side (sourceLane side lane) quota
      (E.map (sourceEmbedding r) ∪ A) (F.map (sourceEmbedding r) ∪ A) := by
  constructor
  · rw [read_source_with_aux r side lane quota E A hoff, H.eval]
    rfl
  · intro p hp q hq ha
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    have hpmap : p ∈ E.map (sourceEmbedding r) :=
      (Finset.mem_union.mp hp).resolve_right (fun h => hpnot (Finset.mem_union_right _ h))
    obtain ⟨p, hp0, rfl⟩ := Finset.mem_map.mp hpmap
    have hpnot' : p ∉ F := fun hf => hpnot
      (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p, hf, rfl⟩))
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨q, hq0, rfl⟩ := Finset.mem_map.mp hq
      exact H.no_split p (Finset.mem_sdiff.mpr ⟨hp0, hpnot'⟩) q hq0
        (source_adjacent_reflect r side.opposite ha)
    · have hpLane : side.lane p = lane := by
        by_contra hn
        exact hpnot' ((Push.Scan.Instruction.read_outside H.eval hn).mpr hp0)
      apply hoff q hq
      have hline : side.lane q = side.lane (sourceEmbedding r p) := by cases side <;> exact ha.lane
      rw [hline, sourceEmbedding_lane, hpLane]

theorem LooseExec.source_lift (program : List (Push.Scan.Instruction r.width r.height))
    {E F : Finset (Cell r.width r.height)} (H : LooseExec program E F)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hoff : ∀ i ∈ program, SourceOff r A i) :
    LooseExec (program.map (sourceInstruction r))
      (E.map (sourceEmbedding r) ∪ A) (F.map (sourceEmbedding r) ∪ A) := by
  induction H with
  | nil => exact .nil _
  | cons paid head _ ih =>
    exact .cons paid (head.source_lift r A (hoff _ (List.mem_cons_self ..)))
      (ih (fun i hi => hoff i (List.mem_cons_of_mem _ hi)))

private theorem Read.source {side : Direction} {lane quota : ℕ}
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : Read side (sourceLane side lane) quota E F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hoff : ∀ q ∈ auxData r E, side.lane q ≠ sourceLane side lane) :
    Read side lane quota (sourceData r E) (sourceData r F) := by
  have he := read_source_with_aux r side lane quota (sourceData r E) (auxData r E) hoff
  rw [← source_data_decomposition r E hrows, H.eval] at he
  obtain ⟨K, hK, hF⟩ := Option.map_eq_some_iff.mp he.symm
  have hdata : sourceData r F = K := by
    rw [← hF]
    exact sourceData_frame r K _ (fun q hq => (Finset.mem_filter.mp hq).2)
  refine ⟨hdata.symm ▸ hK, ?_⟩
  intro p hp q hq ha
  have hp' : sourceEmbedding r p ∈ E \ F := by
    simpa only [sourceData, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  have hq' : sourceEmbedding r q ∈ F := (Finset.mem_filter.mp hq).2
  exact H.no_split _ hp' _ hq' (source_adjacent r side.opposite ha)

private theorem sourceOff_mono
    {A B : Finset (Cell (dock r).outputWidth (dock r).outputHeight)} (hsub : B ⊆ A)
    (instruction : Push.Scan.Instruction r.width r.height) (H : SourceOff r A instruction) :
    SourceOff r B instruction := by
  cases instruction with
  | read side lane quota => exact fun q hq => H q (hsub hq)
  | clear side lanes => exact fun q hq => H q (hsub hq)

theorem LooseExec.source (program : List (Push.Scan.Instruction r.width r.height))
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : LooseExec (program.map (sourceInstruction r)) E F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hoff : ∀ i ∈ program, SourceOff r (auxData r E) i) :
    LooseExec program (sourceData r E) (sourceData r F) := by
  induction program generalizing E with
  | nil => cases H; exact .nil _
  | cons instruction program ih =>
    cases instruction with
    | clear side lanes => cases H
    | read side lane quota =>
      cases H with
      | @cons _ _ _ actual _ E G F paid head tail =>
        have hhead := head.source r hrows (hoff _ (List.mem_cons_self ..))
        refine .cons paid hhead (ih tail (fun q hq hy => hrows q (head.subset hq) hy) ?_)
        intro i hi
        apply sourceOff_mono r _ i (hoff i (List.mem_cons_of_mem _ hi))
        intro q hq
        obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨head.subset hq, hy⟩

theorem LooseExec.source_rows (rows : List ℕ) (hlen : rows.length = r.height)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : LooseExec ((Push.Scan.lines .west (Push.Scan.ofQuotas rows)).map (sourceInstruction r)) E F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2) :
    LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows)) (sourceData r E) (sourceData r F) := by
  apply H.source r _ hrows
  intro instruction hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  intro q hq he
  have hj : j.val < r.height := j.isLt.trans_eq hlen
  have hy := (Finset.mem_filter.mp hq).2
  change q.2.val = j.val at he
  omega

end PushPuzzle.PushPush.WholeScan
