/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicTwoRoundCompletenessReader
public import Push.CornerDockForwardFrame

/-! The exact first-reader remainder and the whole wide room survive docking and rotation. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem turn_hole {w h : ℕ} (s : State w h) (q : Cell w h) :
    (turnGeometry w h).cells q ∈ holes ((turnGeometry w h).state s) ↔ q ∈ holes s := by
  simp only [mem_holes, GridIsometry.mem_boxes]

/-- An exact first read reaches the next source corner with every surviving source hole and every reserve hole. -/
theorem first_round_ready (r : ColumnScan.Input) {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hcorner : s.player = r.sourceCorner) {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E) :
    ∃ t : State (nextSource r).width (nextSource r).height,
      Reachable (nextSource r).board none (nextSource r).initial t ∧ t.player = (nextSource r).target ∧
      (∀ p ∈ E, sourceEmbed r p ∈ holes t) ∧
      ∀ q : Fin (r.width + 2) × Fin ((wideReader r).outputHeight - r.height),
        reserveEmbed r q ∈ holes t := by
  obtain ⟨a, ha, hap, hsource, hroom⟩ := first_round_exact (wideReader r) hr hcorner heval
  obtain ⟨b, hfull, hbp, hframe⟩ := (dock r).compile_run_frame (ha.reboard rfl) hap
  let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
  have hturn : Reachable (nextSource r).board none (nextSource r).initial (e.state b.toState) := by
    have h := (e.reachable hfull).reboard (B' := (nextSource r).board) (by
      change Finset.map e.cells.toEmbedding (dock r).compile.board.walls = (nextSource r).board.walls
      rw [Push.Instance.walls_empty, Push.Instance.walls_empty]
      exact Finset.map_empty _)
    have hi : e.state (dock r).compile.initial = (nextSource r).initial := by
      exact (GridIsometry.state_trans _ _ _).symm
    exact hi ▸ h
  refine ⟨e.state b.toState, hturn, ?_, ?_, ?_⟩
  · change e.cells b.player = e.cells (dock r).target
    exact congrArg e.cells hbp
  · intro p hp
    apply (turn_hole b.toState ((dock r).embed ((wideReader r).embed p))).mpr
    rw [b.holes_toState]
    exact (hframe ((wideReader r).embed p)).mpr ((hsource p).mpr hp)
  · intro q
    apply (turn_hole b.toState ((dock r).embed (reserveCell r q))).mpr
    rw [b.holes_toState]
    apply (hframe (reserveCell r q)).mpr
    apply hroom
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change r.width < r.width + 1 + q.1.val
      omega
    · change r.height ≤ r.height + q.2.val
      omega

end PushPuzzle.Push.Cyclic
