/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.Space.Goal
public import CslibFrontier.Algorithms.Reachability.Savitch
public import CslibFrontier.Foundations.Data.BitString.WordsOfLength

/-! A fixed-width configuration graph with a single accepting node. -/

@[expose] public section

namespace PushPuzzle.Push.SearchGraph

open PushFS (State Step Reachable)


/-- One tag bit and two dense cell bitmaps. -/
def width (I : Instance) : ℕ := 2 * I.area + 1

/-- A single terminal node, with the same width as an ordinary node. -/
def accept (I : Instance) : List Bool := true :: List.replicate (2 * I.area) false

/-- The total Boolean edge test, including the terminal-node branch. -/
def wordEdge (q : Instance × List Bool × List Bool) : Bool :=
  !q.2.1.headD true &&
    ((!q.2.2.headD true && Machine.edge (q.1, q.2.1.tail, q.2.2.tail)) ||
      (q.2.2 == accept q.1 && Machine.goal (q.1, q.2.1.tail)))

private theorem head_false_iff (u : List Bool) :
    !u.headD true = true ↔ ∃ tail, u = false :: tail := by
  cases u with
  | nil => simp
  | cons b u => cases b <;> simp

/-- Every raw edge has one of the two intended meanings, with no malformed nodes. -/
private theorem wordEdge_correct (I : Instance) (u v : List Bool) :
    wordEdge (I, u, v) = true ↔ ∃ s : State I.width I.height,
      u = false :: s.bits ∧
      ((∃ t, v = false :: t.bits ∧ Step I.board none s t) ∨
        (v = accept I ∧ s.Valid I.board ∧ (s.player = I.target))) := by
  constructor
  · intro he
    obtain ⟨hu, hnext⟩ := Bool.and_eq_true_iff.mp he
    obtain ⟨ut, rfl⟩ := (head_false_iff u).mp hu
    rcases Bool.or_eq_true_iff.mp hnext with hmove | hgoal
    · obtain ⟨hv, hm⟩ := Bool.and_eq_true_iff.mp hmove
      obtain ⟨vt, rfl⟩ := (head_false_iff v).mp hv
      obtain ⟨s, t, hs, ht, hst⟩ := (Machine.edge_correct I ut vt).mp hm
      exact ⟨s, by simp [hs], Or.inl ⟨t, by simp [ht], hst⟩⟩
    · obtain ⟨hv, hg⟩ := Bool.and_eq_true_iff.mp hgoal
      obtain ⟨s, hs, hvalid, hsolved⟩ := (Machine.goal_correct I ut).mp hg
      exact ⟨s, by simp [hs], Or.inr ⟨by simpa using hv, hvalid, hsolved⟩⟩
  · rintro ⟨s, rfl, ⟨t, rfl, hst⟩ | ⟨rfl, hvalid, hsolved⟩⟩
    · have he := (Machine.edge_correct I s.bits t.bits).mpr ⟨s, t, rfl, rfl, hst⟩
      simp [wordEdge, he]
    · have hg := (Machine.goal_correct I s.bits).mpr ⟨s, rfl, hvalid, hsolved⟩
      simp [wordEdge, accept, hg]

@[simp] theorem wordEdge_accept (I : Instance) (v : List Bool) :
    wordEdge (I, accept I, v) = false := by simp [wordEdge, accept]

@[simp] theorem length_node (I : Instance) (s : State I.width I.height) :
    (false :: s.bits).length = width I := by simp [width, Instance.area]

@[simp] theorem length_accept (I : Instance) : (accept I).length = width I := by
  simp [accept, width]

/-- Both endpoints of an edge have the width used by midpoint enumeration. -/
private theorem wordEdge_lengths (I : Instance) {u v : List Bool} (he : wordEdge (I, u, v) = true) :
    u.length = width I ∧ v.length = width I := by
  obtain ⟨s, rfl, ⟨t, rfl, _⟩ | ⟨rfl, _, _⟩⟩ := (wordEdge_correct I u v).mp he <;> simp [width, Instance.area]

/-- Reachability in the word graph does not introduce new puzzle behaviour. -/
private theorem reachable_invariant (I : Instance) {v : List Bool}
    (hr : Relation.ReflTransGen (fun u v => wordEdge (I, u, v) = true)
      (false :: I.initial.bits) v) :
    (∃ s : State I.width I.height, v = false :: s.bits ∧ Reachable I.board none I.initial s) ∨
      (v = accept I ∧ I.Solvable) := by
  induction hr with
  | refl => exact Or.inl ⟨I.initial, rfl, .refl⟩
  | @tail u v hr he ih =>
    rcases ih with ⟨s, rfl, hs⟩ | ⟨rfl, _⟩
    · obtain ⟨s', hsrc, ⟨t, rfl, ht⟩ | ⟨rfl, _, hgoal⟩⟩ :=
        (wordEdge_correct I _ v).mp he
      · have heq : s = s' := State.bits_injective (List.cons.inj hsrc).2
        subst s'
        exact Or.inl ⟨t, rfl, hs.tail ht⟩
      · have heq : s = s' := State.bits_injective (List.cons.inj hsrc).2
        subst s'
        exact Or.inr ⟨rfl, s, hs, hgoal⟩
    · simp at he

/-- A genuine puzzle trajectory lifts to the tagged word graph. -/
private theorem reachable_of_moves (I : Instance) {s t : State I.width I.height}
    (hr : Reachable I.board none s t) :
    Relation.ReflTransGen (fun u v => wordEdge (I, u, v) = true)
      (false :: s.bits) (false :: t.bits) := by
  induction hr with
  | refl => exact .refl
  | @tail u v hr he ih =>
    exact ih.tail ((wordEdge_correct I _ _).mpr ⟨u, rfl, Or.inl ⟨v, rfl, he⟩⟩)

/-- Entering the sole accepting node is equivalent to solving the actual puzzle. -/
private theorem reachable_accept_iff (I : Instance) :
    Relation.ReflTransGen (fun u v => wordEdge (I, u, v) = true)
      (false :: I.initial.bits) (accept I) ↔ I.Solvable := by
  constructor
  · intro hr
    rcases reachable_invariant I hr with ⟨s, hs, _⟩ | ⟨_, hs⟩
    · simp [accept] at hs
    · exact hs
  · rintro ⟨s, hr, hgoal⟩
    exact (reachable_of_moves I hr).tail ((wordEdge_correct I _ _).mpr
      ⟨s, rfl, Or.inr ⟨rfl, hr.valid I.initial_valid, hgoal⟩⟩)

/-- The executable, explicit-stack Savitch algorithm used in the machine proof. -/
def solve (I : Instance) : Bool :=
  Cslib.Reachability.savitch (fun u v => wordEdge (I, u, v))
    (width I) (width I) (false :: I.initial.bits) (accept I)

/-- Savitch's finite graph search exactly decides the original problem. -/
theorem solve_correct (I : Instance) : solve I = true ↔ I.Solvable := by
  have hlen : ∀ v, Relation.ReflTransGen (fun u v => wordEdge (I, u, v) = true)
      (false :: I.initial.bits) v → v.length = width I := by
    intro v hr
    induction hr with
    | refl => exact length_node I I.initial
    | tail _ he _ => exact (wordEdge_lengths I he).2
  have hcard : {v | Relation.ReflTransGen (fun u v => wordEdge (I, u, v) = true)
      (false :: I.initial.bits) v}.encard ≤ 2 ^ width I + 1 := by
    have hsub : {v | Relation.ReflTransGen (fun u v => wordEdge (I, u, v) = true)
        (false :: I.initial.bits) v} ⊆ {v : List Bool | v.length = width I} :=
      fun v hv => hlen v hv
    refine (Set.encard_le_encard hsub).trans ?_
    exact (Cslib.BitString.encard_setOf_length_eq _).le.trans le_self_add
  have hrel : (fun u v : List Bool =>
      u.length = width I ∧ v.length = width I ∧ wordEdge (I, u, v) = true) =
      (fun u v => wordEdge (I, u, v) = true) := by
    funext u v
    apply propext
    exact ⟨fun h => h.2.2, fun h => ⟨(wordEdge_lengths I h).1, (wordEdge_lengths I h).2, h⟩⟩
  rw [solve, Cslib.Reachability.savitch_iff (length_node I I.initial) (length_accept I), hrel,
    ← Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard, reachable_accept_iff]

end PushPuzzle.Push.SearchGraph
