/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisUpdates
public import PushS.LinePush
import all PushS.PortGateAxisUpdates

/-! The actual three-port middle-axis bit flip is a genuine complete vertical box-train push. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- Flip an actual middle-axis signal on the complete marked board, retaining every other hole. -/
theorem encodedSegments_gate_axis_step (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hport : upper.port = g.left + 1)
    (gain : Bool) (hi : g.left + 1 < state.axes.length)
    (hbefore : state.axes.getD (g.left + 1) false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (p.x (g.left + 1), if gain then readDepth p upper.level + 1 else p.H - (readDepth p 1 + 1)))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with axes := state.axes.set (g.left + 1) gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (p.x (g.left + 1), if gain then readDepth p upper.level + 2 else p.H - (readDepth p 1 + 2)) := by
  obtain ⟨hup, huc, hlp, hlc, hH⟩ := gate_axis_geometry l p hl hM hu
  let q : Cell (p.W + 1) (p.H + 1) := (s.player.1,
    ⟨if gain then readDepth p upper.level + 2 else p.H - (readDepth p 1 + 2), by split <;> omega⟩)
  let z : Cell (p.W + 1) (p.H + 1) := (s.player.1,
    ⟨if gain then p.H - (readDepth p 1 + 2) else readDepth p upper.level + 2, by split <;> omega⟩)
  have hpx : s.player.1.val = p.x (g.left + 1) := congrArg Prod.fst hp
  have hpy : s.player.2.val = if gain then readDepth p upper.level + 1 else p.H - (readDepth p 1 + 1) :=
    congrArg Prod.snd hp
  have htarget := gate_axis_update l p hl hM ha state hg hk hu hsu hport gain hi hbefore q z hpx hpx rfl rfl
  let t : HoleState (p.W + 1) (p.H + 1) := {
    player := q
    empty := SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.encodedSegments p {state with axes := state.axes.set (g.left + 1) gain})
    player_empty := by rw [htarget]; exact Finset.mem_insert_self _ _ }
  have hzR := gate_axis_transfer_inside l p hl hM hu (g := g) (q := z) hpx
    (by cases gain <;> simp [z])
  have hmove : Move B none (if gain then .south else .north) s.toState t.toState := by
    apply HoleState.move_to_first_hole s t (if gain then .south else .north) z
      (p.H - (readDepth p upper.level + readDepth p 1 + 4)) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ B hB
    · cases gain <;> rfl
    · cases gain <;> simp only [Direction.position, Bool.false_eq_true, ite_false, ite_true, z] at hpy ⊢ <;> omega
    · intro r hLane hlo hhi hrH
      have hrx : r.1.val = p.x (g.left + 1) := by cases gain <;> exact hLane.trans hpx
      have hrRail : r ∈ gateAxis p (g.left + 1) := by
        cases gain <;> simp only [Direction.position, Bool.false_eq_true, ite_false, ite_true, z] at hlo hhi hpy <;>
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrx, by omega, by omega⟩
      rw [hempty, l.encodedSegments_gateAxis_mem p hl hM ha state hg hk hu hsu hport hrRail] at hrH
      cases gain <;> simp only [Bool.not_false, Bool.not_true] at hbefore <;>
        simp only [Direction.position, Bool.false_eq_true, ite_false, ite_true, z] at hlo hhi hpy <;>
        simp only [hbefore, Bool.toNat_false, Bool.toNat_true] at hrH <;> omega
    · rw [hempty, l.encodedSegments_gateAxis_mem p hl hM ha state hg hk hu hsu hport hzR]
      cases gain <;> simp only [Bool.not_false, Bool.not_true] at hbefore <;>
        simp only [hbefore, Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false, Bool.toNat_true, z] <;> omega
    · cases gain <;> simp only [Adjacent, Bool.false_eq_true, ite_false, ite_true, t, q] at hpy ⊢ <;>
        constructor <;> first | omega | trivial
    · change _ = insert q (s.empty.erase z)
      rw [hempty]
      exact htarget
  exact ⟨t, ⟨_, hmove⟩, rfl, by change (s.player.1.val, _) = _; rw [hpx]⟩

end PushPuzzle.PushS.PortLayout
