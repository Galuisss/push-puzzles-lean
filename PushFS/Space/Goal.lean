/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.Queries
public import PushFS.Space.StateDecoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! A polynomial-time goal test on arbitrary state words. -/

@[expose] public section

namespace PushPuzzle.PushFS.Machine


open Turing.MultiTapeTM ComputableInPolyTime

/-- A goal is a well-formed, legal state with exactly the goal cells occupied. -/
def goal (q : Instance × List Bool) : Bool :=
  State.codeValid (q.1.area, q.2) && valid q &&
    (q.2.take q.1.area == flags Encoding.Tile.goal q.1)

@[fun_prop] theorem goal_polyTime :
    ComputableInPolyTime goal (encPair encoding encBits) encBool := by
  have hc : ComputableInPolyTime
      (fun q : Instance × List Bool => State.codeValid (q.1.area, q.2))
      (encPair encoding encBits) encBool :=
    State.codeValid_computable.comp ((area_polyTime.comp (fst _ _)).prod (snd _ _))
  have hg := flags_polyTime Encoding.Tile.goal
  unfold goal
  fun_prop

/-- Comparing the two dense bitmaps is exactly finite-set equality. -/
theorem goalFlags_correct (I : Instance) (s : State I.width I.height) :
    s.boxBits = flags Encoding.Tile.goal I ↔ s.boxes = I.board.goals := by
  rw [flags_eq_ofFn]
  change (List.ofFn fun i => decide (State.cellAt i ∈ s.boxes)) =
    (List.ofFn fun i => decide (State.cellAt i ∈ I.board.goals)) ↔ s.boxes = I.board.goals
  constructor
  · intro heq
    ext p
    have hp := congrFun (List.ofFn_injective heq) (finProdFinEquiv p.swap)
    simpa only [State.cellAt_index, decide_eq_decide] using hp
  · intro hs
    rw [hs]

theorem goal_state_correct (I : Instance) (s : State I.width I.height) :
    goal (I, s.bits) = true ↔ s.Valid I.board ∧ s.boxes = I.board.goals := by
  have hc : State.codeValid (I.area, s.bits) = true :=
    (State.codeValid_correct s.bits).mpr ⟨s, rfl⟩
  have ht : s.bits.take I.area = s.boxBits := by simp [State.bits, Instance.area]
  simp only [goal, hc, Bool.true_and, Bool.and_eq_true, beq_iff_eq, ht,
    valid_correct, goalFlags_correct]

/-- Arbitrary words pass precisely when they encode a legal solved state. -/
theorem goal_correct (I : Instance) (word : List Bool) :
    goal (I, word) = true ↔ ∃ s : State I.width I.height,
      s.bits = word ∧ s.Valid I.board ∧ s.boxes = I.board.goals := by
  constructor
  · intro hg
    have hparts := hg
    simp only [goal, Bool.and_eq_true] at hparts
    have hc : State.codeValid (I.area, word) = true := hparts.1.1
    obtain ⟨s, hs⟩ := (State.codeValid_correct (w := I.width) (h := I.height) word).mp hc
    subst word
    exact ⟨s, rfl, (goal_state_correct I s).mp hg⟩
  · rintro ⟨s, rfl, hv, hs⟩
    exact (goal_state_correct I s).mpr ⟨hv, hs⟩

end PushPuzzle.PushFS.Machine
