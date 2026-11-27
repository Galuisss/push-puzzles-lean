/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Encoding
public import PushFS.Space.Goal
public import PushFS.Space.Edge

/-! Polynomial-time checks for the ordinary player destination. -/

@[expose] public section
namespace PushPuzzle.Push.Machine

open Turing.MultiTapeTM ComputableInPolyTime
open PushFS (State)

@[fun_prop] theorem data_polyTime :
    ComputableInPolyTime Encoding.data encoding
      (encPair PushFS.encoding (encPair encUnary encUnary)) :=
  of_eq fun _ => rfl

@[fun_prop] theorem toStorage_polyTime :
    ComputableInPolyTime Instance.toStorage encoding PushFS.encoding :=
  (fst _ _).comp data_polyTime

@[fun_prop] theorem area_polyTime :
    ComputableInPolyTime Instance.area encoding encUnary :=
  PushFS.Machine.area_polyTime.comp toStorage_polyTime

@[fun_prop] theorem target_polyTime :
    ComputableInPolyTime (fun I : Instance => PushFS.Machine.rawCell I.target)
      encoding PushFS.Machine.encRawCell :=
  (snd _ _).comp data_polyTime

/-- Accept exactly valid state codes whose player is at the designated target. -/
def goal (q : Instance × List Bool) : Bool :=
  State.codeValid (q.1.area, q.2) && PushFS.Machine.valid (q.1.toStorage, q.2) &&
    PushFS.Machine.playerAt (q.1.toStorage, q.2, PushFS.Machine.rawCell q.1.target)

@[fun_prop] theorem goal_polyTime :
    ComputableInPolyTime goal (encPair encoding encBits) encBool := by
  have hc : ComputableInPolyTime
      (fun q : Instance × List Bool => State.codeValid (q.1.area, q.2))
      (encPair encoding encBits) encBool :=
    State.codeValid_computable.comp ((area_polyTime.comp (fst _ _)).prod (snd _ _))
  have hv : ComputableInPolyTime
      (fun q : Instance × List Bool => PushFS.Machine.valid (q.1.toStorage, q.2))
      (encPair encoding encBits) encBool :=
    PushFS.Machine.valid_polyTime.comp
      ((toStorage_polyTime.comp (fst _ _)).prod (snd _ _))
  have hp : ComputableInPolyTime
      (fun q : Instance × List Bool =>
        PushFS.Machine.playerAt (q.1.toStorage, q.2, PushFS.Machine.rawCell q.1.target))
      (encPair encoding encBits) encBool :=
    PushFS.Machine.playerAt_polyTime.comp
      ((toStorage_polyTime.comp (fst _ _)).prod
        ((snd _ _).prod (target_polyTime.comp (fst _ _))))
  unfold goal
  fun_prop

theorem goal_state_correct (I : Instance) (s : State I.width I.height) :
    goal (I, s.bits) = true ↔ s.Valid I.board ∧ s.player = I.target := by
  have hc : State.codeValid (I.area, s.bits) = true :=
    (State.codeValid_correct s.bits).mpr ⟨s, rfl⟩
  have hv : PushFS.Machine.valid (I.toStorage, s.bits) = true ↔ s.Valid I.board :=
    PushFS.Machine.valid_correct I.toStorage s
  have hp : PushFS.Machine.playerAt (I.toStorage, s.bits, PushFS.Machine.rawCell I.target) =
      decide (I.target = s.player) :=
    PushFS.Machine.playerAt_correct I.toStorage s I.target
  simp only [goal, hc, Bool.true_and, Bool.and_eq_true]
  rw [hv, hp, decide_eq_true_eq]
  exact and_congr_right fun _ => eq_comm

/-- Arbitrary words pass precisely when they encode a valid state at the target. -/
theorem goal_correct (I : Instance) (word : List Bool) :
    goal (I, word) = true ↔ ∃ s : State I.width I.height,
      s.bits = word ∧ s.Valid I.board ∧ s.player = I.target := by
  constructor
  · intro hg
    have hparts := hg
    simp only [goal, Bool.and_eq_true] at hparts
    obtain ⟨s, hs⟩ :=
      (State.codeValid_correct (w := I.width) (h := I.height) word).mp hparts.1.1
    subst word
    exact ⟨s, rfl, (goal_state_correct I s).mp hg⟩
  · rintro ⟨s, rfl, hv, hs⟩
    exact (goal_state_correct I s).mpr ⟨hv, hs⟩

/-- The original complete-run step checker with the unlimited push cap. -/
def edge (q : Instance × List Bool × List Bool) : Bool :=
  PushFS.Machine.edge none (q.1.toStorage, q.2)

@[fun_prop] theorem edge_polyTime :
    ComputableInPolyTime edge (encPair encoding (encPair encBits encBits)) encBool := by
  unfold edge
  fun_prop

theorem edge_correct (I : Instance) (u v : List Bool) :
    edge (I, u, v) = true ↔ ∃ s t : State I.width I.height,
      s.bits = u ∧ t.bits = v ∧ PushFS.Step I.board none s t :=
  PushFS.Machine.edge_correct none I.toStorage u v

@[fun_prop] theorem initial_polyTime :
    ComputableInPolyTime (fun I : Instance => I.initial.bits) encoding encBits :=
  PushFS.Machine.initial_state_encoding_polyTime.comp toStorage_polyTime

end PushPuzzle.Push.Machine
