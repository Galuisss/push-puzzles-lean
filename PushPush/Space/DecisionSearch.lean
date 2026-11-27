/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Space.Edge
public import CslibFrontier.Algorithms.Reachability.Savitch
public import CslibFrontier.Foundations.Data.BitString.WordsOfLength
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability

/-! Polynomial-space reachability for a polynomial-time state edge and terminal test. -/

public section
namespace PushPuzzle.PushPush.DecisionSearch

open PushFS (State)
open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Complexity

variable {α : Type}

/-- A state relation with its exact Boolean edge checker. -/
structure System (store : α → PushFS.Instance) where
  step : (I : α) → State (store I).width (store I).height →
    State (store I).width (store I).height → Prop
  edge : α × List Bool × List Bool → Bool
  correct : ∀ I u v, edge (I, u, v) = true ↔
    ∃ s t : State (store I).width (store I).height,
      s.bits = u ∧ t.bits = v ∧ step I s t

variable (store : α → PushFS.Instance) (goal : α × List Bool → Bool) (sys : System store)

/-- A reached state satisfies the supplied terminal test. -/
@[expose] def Language : Set α :=
  {I | ∃ s, Relation.ReflTransGen (sys.step I) (store I).initial s ∧ goal (I, s.bits) = true}

/-- One tag bit and the box/player bitmaps. -/
private def width (I : α) : ℕ := 2 * (store I).area + 1

/-- A unique terminal vertex. -/
private def accept (I : α) : List Bool := true :: List.replicate (2 * (store I).area) false

/-- Tagged graph edges check state syntax, the supplied relation, and the terminal test. -/
private def wordEdge (q : α × List Bool × List Bool) : Bool :=
  let (I, u, v) := q
  !u.headD true &&
    ((!v.headD true && sys.edge (I, u.tail, v.tail)) ||
      (v == accept store I &&
        State.codeValid ((store I).area, u.tail) && goal (I, u.tail)))

private theorem wordEdge_correct (I : α) (u v : List Bool) :
    wordEdge store goal sys (I, u, v) = true ↔ ∃ s : State (store I).width (store I).height,
      u = false :: s.bits ∧
      ((∃ t, v = false :: t.bits ∧ sys.step I s t) ∨
        (v = accept store I ∧ goal (I, s.bits) = true)) := by
  constructor
  · intro he
    obtain ⟨hu, hnext⟩ := Bool.and_eq_true_iff.mp he
    obtain ⟨ut, rfl⟩ := List.head?_eq_some_iff.mp
      (show u.head? = some false by simpa [Option.getD_eq_iff] using hu)
    rcases Bool.or_eq_true_iff.mp hnext with hmove | hgoal
    · obtain ⟨hv, hm⟩ := Bool.and_eq_true_iff.mp hmove
      obtain ⟨vt, rfl⟩ := List.head?_eq_some_iff.mp
        (show v.head? = some false by simpa [Option.getD_eq_iff] using hv)
      obtain ⟨s, t, hs, ht, hst⟩ := (sys.correct I ut vt).mp hm
      exact ⟨s, by simp [hs], Or.inl ⟨t, by simp [ht], hst⟩⟩
    · obtain ⟨hab, hg⟩ := Bool.and_eq_true_iff.mp hgoal
      obtain ⟨hv, hc⟩ := Bool.and_eq_true_iff.mp hab
      obtain ⟨s, hs⟩ :=
        (State.codeValid_correct (w := (store I).width) (h := (store I).height) ut).mp hc
      exact ⟨s, by simp [hs], Or.inr ⟨by simpa using hv, by simpa [hs] using hg⟩⟩
  · rintro ⟨s, rfl, ⟨t, rfl, hst⟩ | ⟨rfl, hg⟩⟩
    · have he := (sys.correct I s.bits t.bits).mpr ⟨s, t, rfl, rfl, hst⟩
      simp [wordEdge, he]
    · have hc : State.codeValid ((store I).area, s.bits) = true :=
        (State.codeValid_correct _).mpr ⟨s, rfl⟩
      simp [wordEdge, accept, hc, hg]

@[simp] private theorem wordEdge_accept (I : α) (v : List Bool) :
    wordEdge store goal sys (I, accept store I, v) = false := by simp [wordEdge, accept]

@[simp] private theorem length_node (I : α) (s : State (store I).width (store I).height) :
    (false :: s.bits).length = width store I := by simp [width, PushFS.Instance.area]

@[simp] private theorem length_accept (I : α) :
    (accept store I).length = width store I := by simp [accept, width]

private theorem wordEdge_lengths (I : α) {u v : List Bool}
    (he : wordEdge store goal sys (I, u, v) = true) :
    u.length = width store I ∧ v.length = width store I := by
  obtain ⟨s, rfl, ⟨t, rfl, _⟩ | ⟨rfl, _⟩⟩ := (wordEdge_correct store goal sys I u v).mp he <;>
    simp [width, PushFS.Instance.area]

private theorem reachable_invariant (I : α) {v : List Bool}
    (hr : Relation.ReflTransGen (fun u v => wordEdge store goal sys (I, u, v) = true)
      (false :: (store I).initial.bits) v) :
    (∃ s : State (store I).width (store I).height,
      v = false :: s.bits ∧ Relation.ReflTransGen (sys.step I) (store I).initial s) ∨
      (v = accept store I ∧ I ∈ Language store goal sys) := by
  induction hr with
  | refl => exact Or.inl ⟨(store I).initial, rfl, .refl⟩
  | @tail u v hr he ih =>
    rcases ih with ⟨s, rfl, hs⟩ | ⟨rfl, _⟩
    · obtain ⟨s', hsrc, ⟨t, rfl, ht⟩ | ⟨rfl, hg⟩⟩ :=
        (wordEdge_correct store goal sys I _ v).mp he
      · have heq : s = s' := State.bits_injective (List.cons.inj hsrc).2
        subst s'
        exact Or.inl ⟨t, rfl, hs.tail ht⟩
      · have heq : s = s' := State.bits_injective (List.cons.inj hsrc).2
        subst s'
        exact Or.inr ⟨rfl, s, hs, hg⟩
    · simp at he

private theorem reachable_of_moves (I : α) {s t : State (store I).width (store I).height}
    (hr : Relation.ReflTransGen (sys.step I) s t) :
    Relation.ReflTransGen (fun u v => wordEdge store goal sys (I, u, v) = true)
      (false :: s.bits) (false :: t.bits) := by
  induction hr with
  | refl => exact .refl
  | @tail u v hr he ih =>
    exact ih.tail ((wordEdge_correct store goal sys I _ _).mpr ⟨u, rfl, Or.inl ⟨v, rfl, he⟩⟩)

private theorem reachable_accept_iff (I : α) :
    Relation.ReflTransGen (fun u v => wordEdge store goal sys (I, u, v) = true)
      (false :: (store I).initial.bits) (accept store I) ↔ I ∈ Language store goal sys := by
  constructor
  · intro hr
    rcases reachable_invariant store goal sys I hr with ⟨s, hs, _⟩ | ⟨_, hs⟩
    · simp [accept] at hs
    · exact hs
  · rintro ⟨s, hr, hg⟩
    exact (reachable_of_moves store goal sys I hr).tail
      ((wordEdge_correct store goal sys I _ _).mpr ⟨s, rfl, Or.inr ⟨rfl, hg⟩⟩)

/-- Savitch's explicit-stack search. -/
private def solve (I : α) : Bool :=
  Cslib.Reachability.savitch (fun u v => wordEdge store goal sys (I, u, v))
    (width store I) (width store I) (false :: (store I).initial.bits) (accept store I)

private theorem solve_correct (I : α) :
    solve store goal sys I = true ↔ I ∈ Language store goal sys := by
  have hlen : ∀ v, Relation.ReflTransGen (fun u v => wordEdge store goal sys (I, u, v) = true)
      (false :: (store I).initial.bits) v → v.length = width store I := by
    intro v hr
    induction hr with
    | refl => exact length_node store I (store I).initial
    | tail _ he _ => exact (wordEdge_lengths store goal sys I he).2
  have hcard : {v | Relation.ReflTransGen (fun u v => wordEdge store goal sys (I, u, v) = true)
      (false :: (store I).initial.bits) v}.encard ≤ 2 ^ width store I + 1 := by
    have hsub : {v | Relation.ReflTransGen (fun u v => wordEdge store goal sys (I, u, v) = true)
        (false :: (store I).initial.bits) v} ⊆ {v : List Bool | v.length = width store I} :=
      fun v hv => hlen v hv
    exact (Set.encard_le_encard hsub).trans
      ((Cslib.BitString.encard_setOf_length_eq _).le.trans le_self_add)
  have hrel : (fun u v : List Bool =>
      u.length = width store I ∧ v.length = width store I ∧
        wordEdge store goal sys (I, u, v) = true) =
      (fun u v => wordEdge store goal sys (I, u, v) = true) := by
    funext u v
    apply propext
    exact ⟨fun h => h.2.2,
      fun h => ⟨(wordEdge_lengths store goal sys I h).1, (wordEdge_lengths store goal sys I h).2, h⟩⟩
  rw [solve, Cslib.Reachability.savitch_iff
    (length_node store I (store I).initial) (length_accept store I), hrel,
    ← Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard,
    reachable_accept_iff]

variable {enc : α ↪ List Bool}

private theorem wordEdge_polyTime
    (hs : ComputableInPolyTime store enc PushFS.encoding)
    (hg : ComputableInPolyTime goal (encPair enc encBits) encBool)
    (he : ComputableInPolyTime sys.edge (encPair enc (encPair encBits encBits)) encBool) :
    ComputableInPolyTime (wordEdge store goal sys)
      (encPair enc (encPair encBits encBits)) encBool := by
  have ha : ComputableInPolyTime (fun I => (store I).area) enc encUnary :=
    PushFS.Machine.area_polyTime.comp hs
  have hac : ComputableInPolyTime (accept store) enc encBits := by unfold accept; fun_prop
  have hc : ComputableInPolyTime
      (fun q : α × List Bool => State.codeValid ((store q.1).area, q.2))
      (encPair enc encBits) encBool :=
    State.codeValid_computable.comp ((ha.comp (fst _ _)).prod (snd _ _))
  have he' : ComputableInPolyTime
      (fun q : α × List Bool × List Bool =>
        sys.edge (q.1, q.2.1.tail, q.2.2.tail))
      (encPair enc (encPair encBits encBits)) encBool :=
    he.comp (g := fun q : α × List Bool × List Bool =>
      (q.1, q.2.1.tail, q.2.2.tail)) (by fun_prop)
  have hc' : ComputableInPolyTime
      (fun q : α × List Bool × List Bool =>
        State.codeValid ((store q.1).area, q.2.1.tail))
      (encPair enc (encPair encBits encBits)) encBool :=
    hc.comp (g := fun q : α × List Bool × List Bool => (q.1, q.2.1.tail)) (by fun_prop)
  have hg' : ComputableInPolyTime
      (fun q : α × List Bool × List Bool => goal (q.1, q.2.1.tail))
      (encPair enc (encPair encBits encBits)) encBool :=
    hg.comp (g := fun q : α × List Bool × List Bool => (q.1, q.2.1.tail)) (by fun_prop)
  unfold wordEdge
  fun_prop

theorem language_mem_PSPACE
    (hs : ComputableInPolyTime store enc PushFS.encoding)
    (hg : ComputableInPolyTime goal (encPair enc encBits) encBool)
    (he : ComputableInPolyTime sys.edge (encPair enc (encPair encBits encBits)) encBool) :
    Language store goal sys ∈ PSPACE enc := by
  have ha : ComputableInPolyTime (fun I => (store I).area) enc encUnary :=
    PushFS.Machine.area_polyTime.comp hs
  have hw : ComputableInPolyTime (width store) enc encUnary := by unfold width; fun_prop
  have hac : ComputableInPolyTime (accept store) enc encBits := by unfold accept; fun_prop
  have hi : ComputableInPolyTime (fun I => (store I).initial.bits) enc encBits :=
    PushFS.Machine.initial_state_encoding_polyTime.comp hs
  have hargs : ComputableInPolyTime
      (fun I => (I, width store I, width store I,
        false :: (store I).initial.bits, accept store I)) enc
      (Cslib.Reachability.encArgs enc) := by
    unfold Cslib.Reachability.encArgs
    fun_prop
  obtain ⟨t, s, hbound, hmachine⟩ :=
    Cslib.Reachability.exists_polyBounded_space_savitch
      (edge := fun I u v => wordEdge store goal sys (I, u, v))
      (wordEdge_polyTime store goal sys hs hg he) hargs
      (by intro I; simp [width, PushFS.Instance.area])
      (by intro I; simp [accept, width])
  exact mem_PSPACE_of_computableInTimeAndSpace hbound hmachine
    (fun I => (solve_correct store goal sys I).symm)

end PushPuzzle.PushPush.DecisionSearch
