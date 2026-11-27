/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Normalizing asynchronous NCL propagation

An edge in transit contributes no inflow to either endpoint. Any completion of
a legal partial orientation is legal. A partial step changing at most one edge
can therefore be completed by zero or one ordinary reversal. Full endpoints
recover exactly the upstream NCL reachability relation.

## Main results

* `full_reachable_iff`: asynchronous propagation and ordinary NCL agree on full endpoints.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.NCL.Asynchronous

open Cslib.Complexity Cslib.Complexity.NCL

variable {V E : Type*}

/-- An unassigned edge is in transit and supplies neither endpoint. -/
abbrev Orientation (E : Type*) := E → Option Bool

/-- A full orientation regarded as a partial one. -/
def full (s : E → Bool) : Orientation E := fun e => some (s e)

/-- A completion respects every assigned edge direction. -/
def Extends (s : E → Bool) (p : Orientation E) : Prop :=
  ∀ e b, p e = some b → s e = b

private theorem extends_full_iff (s t : E → Bool) : Extends s (full t) ↔ s = t := by
  constructor
  · intro h
    exact funext (fun e => h e (t e) rfl)
  · rintro rfl e b hb
    exact Option.some.inj hb

/-- Partial inflow counts only assigned ports directed inward. -/
def inflow (v : Vertex E) (p : Orientation E) : ℕ :=
  (v.ports.map fun port => if p port.port.edge = some port.port.dir then port.weight else 0).sum

/-- All vertex constraints hold using only assigned inflow. -/
def Legal (G : ConstraintGraph V E) (p : Orientation E) : Prop :=
  ∀ v, (G v).minInflow ≤ inflow (G v) p

theorem legal_full (G : ConstraintGraph V E) (s : E → Bool) :
    Legal G (full s) ↔ G.Legal s := by
  simp only [Legal, inflow, full, Option.some.injEq, ConstraintGraph.Legal,
    Vertex.Sat, Vertex.inflow, Port.In]
  rfl

/-- Completing an edge only adds inflow. -/
private theorem inflow_le_of_extends (v : Vertex E) {s : E → Bool} {p : Orientation E}
    (he : Extends s p) : inflow v p ≤ v.inflow s := by
  apply List.sum_le_sum
  intro port _
  by_cases hin : p port.port.edge = some port.port.dir
  · simp only [hin, ite_true, Port.In, he _ _ hin, le_refl]
  · simp only [hin, ite_false, Nat.zero_le]

private theorem legal_of_extends {G : ConstraintGraph V E} {s : E → Bool} {p : Orientation E}
    (hp : Legal G p) (he : Extends s p) : G.Legal s :=
  fun v => (hp v).trans (inflow_le_of_extends (G v) he)

/-- A partial step changes at most one edge and preserves all partial inflows. -/
def Step (G : ConstraintGraph V E) (p q : Orientation E) : Prop :=
  Legal G p ∧ Legal G q ∧ ∃ e, ∀ f, f ≠ e → q f = p f

variable [DecidableEq E]

/-- One partial step lifts to zero or one ordinary reversal from any completion. -/
private theorem Step.complete {G : ConstraintGraph V E} {p q : Orientation E} {s : E → Bool}
    (hs : Step G p q) (he : Extends s p) :
    ∃ t, Extends t q ∧ (s = t ∨ G.Step s t) := by
  obtain ⟨hp, hq, e, hsame⟩ := hs
  cases hb : q e with
  | none =>
    refine ⟨s, ?_, Or.inl rfl⟩
    intro f b hf
    by_cases hfe : f = e
    · subst f
      simp only [hb, reduceCtorEq] at hf
    · exact he f b ((hsame f hfe).symm.trans hf)
  | some b =>
    let t : E → Bool := Function.update s e b
    have ht : Extends t q := by
      intro f a hf
      by_cases hfe : f = e
      · subst f
        have ha : b = a := Option.some.inj (hb.symm.trans hf)
        simpa only [t, Function.update_self] using ha
      · simpa only [t, Function.update_of_ne hfe] using he f a ((hsame f hfe).symm.trans hf)
    refine ⟨t, ht, ?_⟩
    by_cases hsb : s e = b
    · exact Or.inl (by simp only [t, ← hsb, Function.update_eq_self])
    · have hflip : b = !(s e) := by cases hse : s e <;> cases b <;> simp_all
      have htReverse : t = reverse s e := by
        change Function.update s e b = Function.update s e (!(s e))
        rw [hflip]
      exact Or.inr ⟨legal_of_extends hp he, legal_of_extends hq ht, e, htReverse⟩

/-- Carry a full completion through every partial state of a path. -/
private theorem reachable_complete {G : ConstraintGraph V E} {p q : Orientation E} {s : E → Bool}
    (hr : Relation.ReflTransGen (Step G) p q) (he : Extends s p) :
    ∃ t, Extends t q ∧ G.Reachable s t := by
  induction hr with
  | refl => exact ⟨s, he, .refl⟩
  | tail _ hs ih =>
    obtain ⟨u, hu, hsu⟩ := ih
    obtain ⟨t, ht, hut | hut⟩ := hs.complete hu
    · exact ⟨t, ht, hut ▸ hsu⟩
    · exact ⟨t, ht, hsu.tail hut⟩

private theorem ordinary_step_partial {G : ConstraintGraph V E} {s t : E → Bool}
    (hs : G.Step s t) : Step G (full s) (full t) := by
  obtain ⟨hs, ht, e, rfl⟩ := hs
  exact ⟨(legal_full G s).mpr hs, (legal_full G _).mpr ht, e,
    fun f hf => by simp only [full, reverse, Function.update_of_ne hf]⟩

/-- Arbitrary asynchronous propagation preserves exactly ordinary NCL reachability at full endpoints. -/
theorem full_reachable_iff {G : ConstraintGraph V E} {s t : E → Bool} :
    Relation.ReflTransGen (Step G) (full s) (full t) ↔ G.Reachable s t := by
  constructor
  · intro hr
    obtain ⟨t', ht', hreach⟩ := reachable_complete hr ((extends_full_iff s s).mpr rfl)
    exact (extends_full_iff t' t).mp ht' ▸ hreach
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (ordinary_step_partial hs)

end PushPuzzle.NCL.Asynchronous
