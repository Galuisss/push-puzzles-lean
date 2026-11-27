/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockTrace
import all Push.CornerDockLift
import all Push.CornerDockReverse

/-! The fixed outside inventory of an open-entry dock prefix. -/

@[expose] public section
namespace PushPuzzle.PushPush.CornerDock

open PushFS (Cell State)

variable (r : Push.CornerDock.Input)

theorem liftState_mem_boxes (s : State r.width r.height) (p : Cell r.width r.height) :
    r.embed p ∈ (r.liftState s).boxes ↔ p ∈ s.boxes := r.lift_mem_boxes s p

theorem sourceState_liftState (s : State r.width r.height) :
    r.sourceState (r.liftState s) = s := by
  apply State.ext
  · apply r.embed_injective
    exact r.sourceState_player (by
      change 2 ≤ s.player.1.val + 2 ∧ s.player.2.val < r.height
      exact ⟨by omega, s.player.2.isLt⟩)
  · ext p
    exact (sourceState_boxes r _ p).trans (r.lift_mem_boxes s p)

theorem liftState_outside (s t : State r.width r.height) (q : Cell r.outputWidth r.outputHeight)
    (hq : ¬(2 ≤ q.1.val ∧ q.2.val < r.height)) :
    q ∈ (r.liftState s).boxes ↔ q ∈ (r.liftState t).boxes := by
  have hoff (u : State r.width r.height) : q ∉ u.boxes.map r.placement.cells := by
    intro hh
    obtain ⟨a, _, he⟩ := Finset.mem_map.mp hh
    apply hq
    rw [← he]
    exact ⟨by change 2 ≤ a.1.val + 2; omega, a.2.isLt⟩
  simp only [Push.CornerDock.Input.liftState, PushFS.GridEmbedding.extend,
    Finset.mem_union, hoff, false_or]

private theorem outside_boxes_prefix {s : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (he : r.entry ∈ PushS.holes s) (q : Cell r.outputWidth r.outputHeight)
    (hq : ¬(2 ≤ q.1.val ∧ q.2.val < r.height)) :
    q ∈ s.boxes ↔ q ∈ r.compile.initial.boxes := by
  revert he
  induction hpre with
  | refl => intro _; rfl
  | @tail u v hpre hm ih =>
    intro he
    have heu := r.entry_hole_source (Relation.ReflTransGen.single hm) he
    have hi := ih heu
    obtain ⟨⟨d, hm⟩, _⟩ := hm
    cases hm with
    | walk _ _ _ _ hb => simpa only [hb] using hi
    | push _ _ _ run hp hb =>
      have hin := r.run_inside hpre (r.sourceInside_prefix hpre) run hb he
      have hn (i) : q ≠ run.cell i := fun hh => hq (hh ▸ hin i)
      constructor
      · intro hh
        rw [hb] at hh
        rcases Finset.mem_insert.mp hh with hh | hh
        · exact False.elim (hn _ hh)
        · exact hi.mp (Finset.mem_erase.mp hh).2
      · intro hh
        rw [hb]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hn _, hi.mpr hh⟩)

/-- Before the first exit, an open entry makes the entire outside board canonical. -/
theorem liftState_sourceState {s : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (he : r.entry ∈ PushS.holes s) : r.liftState (r.sourceState s) = s := by
  apply State.ext
  · exact r.sourceState_player (r.sourceInside_prefix hpre)
  · ext q
    by_cases hi : 2 ≤ q.1.val ∧ q.2.val < r.height
    · let p := cropCell r q hi
      have hp : r.embed p = q := embed_cropCell r q hi
      rw [← hp, r.lift_mem_boxes]
      exact sourceState_boxes r s p
    · rw [liftState_outside r _ r.initial.toState q hi,
        r.liftState_toState r.initial]
      exact (outside_boxes_prefix r hpre he q hi).symm

end PushPuzzle.PushPush.CornerDock
