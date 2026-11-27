/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Subdivision
import all CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Subdivision
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Fin.Basic

/-!
# Cursors on subdivided edges

A cursor records the number of true segments on each subdivided edge. Joint legality with
positive weights characterizes these prefix orientations uniquely. On a loop-free graph,
moving one cursor between two legal configurations follows the segment chain while fixing
every other old edge.

## Main definitions

* `Cursor`: one bounded cursor position per old edge.
* `PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.directions`: the actual orientation of `Subdivision.graph`.
* `PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.set`: change the cursor on one old edge.

## Main results

* `PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.existsUnique_of_joint_sat`: joint-legal orientations have a unique cursor encoding.
* `PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.legal_set_between`: all intermediate positions between two legal cursors are legal.
* `PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.reachable_set`: the interval is a path in the actual subdivision graph.

## References

This cursor parametrization and interval argument are original supporting lemmas for subdivision.
-/

public section

namespace PushPuzzle.NCL.ConstraintGraph.Subdivision

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.ConstraintGraph Cslib.Complexity.NCL.ConstraintGraph.Subdivision Cslib

variable {V E : Type*} {n : E → ℕ}

/-- Number of true segments on each old edge, from zero to the full chain length. -/
@[ext] structure Cursor (n : E → ℕ) where
  /-- Prefix length in the segment chain of an old edge. -/
  position (e : E) : Fin (n e + 2)

namespace Cursor

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.ConstraintGraph Cslib.Complexity.NCL.ConstraintGraph.Subdivision

/-- Orient precisely the segments before the cursor toward the true endpoint. -/
@[expose] def directions (c : Cursor n) : Segment n → Bool :=
  fun i => decide (i.2.val < (c.position i.1).val)

/-- Recover the cursor by counting true segments on each old edge. -/
@[expose] def ofDirections (s : Segment n → Bool) : Cursor n where
  position e := ⟨(Finset.univ.filter fun j : Fin (n e + 1) => s ⟨e, j⟩ = true).card,
    lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

private theorem ofDirections_directions (c : Cursor n) : ofDirections c.directions = c := by
  ext e
  change (Finset.univ.filter fun j : Fin (n e + 1) =>
    decide (j.val < (c.position e).val) = true).card = (c.position e).val
  simp only [decide_eq_true_eq, Fin.card_filter_val_lt]
  exact Nat.min_eq_right (by have := (c.position e).isLt; omega)

/-- Different cursor positions give different actual segment orientations. -/
private theorem directions_injective : Function.Injective (directions (n := n)) :=
  Function.LeftInverse.injective ofDirections_directions

private theorem directions_ofDirections {s : Segment n → Bool}
    (hs : ∀ (e : E) (j : Fin (n e)), s ⟨e, j.succ⟩ ≤ s ⟨e, j.castSucc⟩) :
    (ofDirections s).directions = s := by
  funext ⟨e, j⟩
  have ha : Antitone fun k : Fin (n e + 1) => s ⟨e, k⟩ :=
    Fin.antitone_iff_succ_le.2 (hs e)
  apply Bool.eq_iff_iff.2
  change decide (j.val < (Finset.univ.filter fun k : Fin (n e + 1) =>
    s ⟨e, k⟩ = true).card) = true ↔ s ⟨e, j⟩ = true
  rw [decide_eq_true_eq]
  exact Fin.lt_card_filter_univ_iff_apply_of_imp _ fun a b hab h =>
    Bool.eq_true_of_true_le (by simpa only [h] using ha hab)

/-- Positive-weight joint legality characterizes an orientation by a unique cursor. -/
theorem existsUnique_of_joint_sat (G : ConstraintGraph V E) (w : E → ℕ)
    (hw : ∀ e, 0 < w e) {s : Segment n → Bool}
    (hs : ∀ j : Joint n, (graph G n w (.inr j)).Sat s) :
    ∃! c : Cursor n, c.directions = s := by
  have heq : (ofDirections s).directions = s := directions_ofDirections fun e j =>
    (sat_wire_iff (w e) (hw e) _ _ s).1 (hs ⟨e, j⟩)
  exact ⟨ofDirections s, heq, fun _ hc => directions_injective (hc.trans heq.symm)⟩

/-- The false original endpoint receives this edge exactly at cursor zero. -/
private theorem first_eq_false_iff (c : Cursor n) (e : E) :
    c.directions (first n e) = false ↔ c.position e = 0 := by
  change decide (0 < (c.position e).val) = false ↔ c.position e = 0
  rw [decide_eq_false_iff_not, Fin.ext_iff]
  simp only [Fin.val_zero]
  omega

/-- The true original endpoint receives this edge exactly at the full-chain cursor. -/
private theorem last_eq_true_iff (c : Cursor n) (e : E) :
    c.directions (last n e) = true ↔ c.position e = Fin.last (n e + 1) := by
  change decide (n e < (c.position e).val) = true ↔ c.position e = Fin.last (n e + 1)
  rw [decide_eq_true_eq, Fin.ext_iff]
  simp only [Fin.val_last]
  have := (c.position e).isLt
  omega

/-- Every inserted joint is satisfied by a cursor orientation. -/
theorem joint_sat (G : ConstraintGraph V E) (w : E → ℕ)
    (c : Cursor n) (e : E) (j : Fin (n e)) :
    (graph G n w (.inr ⟨e, j⟩)).Sat c.directions := by
  by_cases hzero : w e = 0
  · change w e ≤ _
    rw [hzero]
    exact Nat.zero_le _
  apply (sat_wire_iff (w e) (by omega) _ _ c.directions).2
  intro h
  have hj : j.val + 1 < (c.position e).val := of_decide_eq_true h
  exact decide_eq_true (by change j.val < (c.position e).val; omega)

variable [DecidableEq E]

/-- Change one old edge's cursor, leaving the other cursor positions fixed. -/
@[expose] def set (c : Cursor n) (e : E) (k : Fin (n e + 2)) : Cursor n :=
  ⟨Function.update c.position e k⟩

/-- Changing a cursor leaves every segment on the other old edges unchanged. -/
private theorem directions_set_of_ne (c : Cursor n) (e : E) (k : Fin (n e + 2))
    {i : Segment n} (hi : i.1 ≠ e) : (c.set e k).directions i = c.directions i := by
  simp only [directions, set, Function.update_of_ne hi]

/-- Adjacent cursor positions reverse precisely the intervening real segment edge. -/
private theorem directions_set_succ (c : Cursor n) (e : E) (k : Fin (n e + 1)) :
    (c.set e k.succ).directions = reverse (c.set e k.castSucc).directions ⟨e, k⟩ := by
  funext ⟨f, j⟩
  by_cases hf : f = e
  · subst f
    have h := congrFun (ramp_succ n (fun _ => false) e k.val k.isLt) ⟨e, j⟩
    simpa only [reverse, Function.update_apply, directions, set, Function.update_self,
      Fin.val_succ, Fin.val_castSucc, ramp, ite_true, eq_self] using h
  · have hne : (⟨f, j⟩ : Segment n) ≠ ⟨e, k⟩ := fun h => hf (congrArg Sigma.fst h)
    rw [reverse_of_ne _ hne, directions_set_of_ne c e _ hf, directions_set_of_ne c e _ hf]

private theorem port_set_between (c : Cursor n) (e : E) (a b k : Fin (n e + 2))
    (hak : a ≤ k) (hkb : k ≤ b) (p : Port E) (d : Bool)
    (hd : p.edge = e → p.dir = d) :
    (port n p).In (c.set e (if d then a else b)).directions →
      (port n p).In (c.set e k).directions := by
  rcases p with ⟨f, dir⟩
  by_cases hf : f = e
  · subst f
    have hdir := hd rfl
    change dir = d at hdir
    subst dir
    cases d with
    | false =>
      change (c.set e b).directions (first n e) = false →
        (c.set e k).directions (first n e) = false
      rw [first_eq_false_iff, first_eq_false_iff]
      simp only [set, Function.update_self, Fin.ext_iff, Fin.val_zero]
      change a.val ≤ k.val at hak
      change k.val ≤ b.val at hkb
      omega
    | true =>
      change (c.set e a).directions (last n e) = true →
        (c.set e k).directions (last n e) = true
      rw [last_eq_true_iff, last_eq_true_iff]
      simp only [set, Function.update_self, Fin.ext_iff, Fin.val_last]
      have := k.isLt
      change a.val ≤ k.val at hak
      omega
  · intro hin
    have hne : (port n ⟨f, dir⟩).edge.1 ≠ e := by cases dir <;> exact hf
    change (c.set e (if d then a else b)).directions (port n ⟨f, dir⟩).edge = dir at hin
    change (c.set e k).directions (port n ⟨f, dir⟩).edge = dir
    rw [directions_set_of_ne c e _ hne] at hin
    rwa [directions_set_of_ne c e _ hne]

private theorem vertex_set_between (v : Vertex E) (hl : (v.ports.map (·.1.edge)).Nodup)
    (c : Cursor n) (e : E) (a b k : Fin (n e + 2)) (hak : a ≤ k) (hkb : k ≤ b)
    (ha : (vertex n v).Sat (c.set e a).directions)
    (hb : (vertex n v).Sat (c.set e b).directions) :
    (vertex n v).Sat (c.set e k).directions := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Bool, ∀ q ∈ v.ports, q.1.edge = e → q.1.dir = d := by
    by_cases he : ∃ q ∈ v.ports, q.1.edge = e
    · obtain ⟨q₀, hq₀, he₀⟩ := he
      refine ⟨q₀.1.dir, fun q hq he => ?_⟩
      have hqeq := List.inj_on_of_nodup_map hl hq hq₀ (he.trans he₀.symm)
      exact congrArg (fun q : WeightedPort E => q.1.dir) hqeq
    · exact ⟨true, fun q hq heq => (he ⟨q, hq, heq⟩).elim⟩
  have hs : (vertex n v).Sat (c.set e (if d then a else b)).directions := by
    cases d <;> assumption
  apply Vertex.Sat.mono (s := (c.set e (if d then a else b)).directions) _ hs
  intro p hp hin
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact port_set_between c e a b k hak hkb q.1 d (hd q hq) hin

/-- On a loop-free graph, every position between two legal cursors remains legal. -/
theorem legal_set_between (G : ConstraintGraph V E) (w : E → ℕ)
    (hl : G.LoopFree) (c : Cursor n) (e : E) {a b k : Fin (n e + 2)}
    (ha : (graph G n w).Legal (c.set e a).directions)
    (hb : (graph G n w).Legal (c.set e b).directions) (hak : a ≤ k) (hkb : k ≤ b) :
    (graph G n w).Legal (c.set e k).directions := by
  intro v
  cases v with
  | inl v =>
    exact vertex_set_between (G v) (hl v) c e a b k hak hkb (ha (.inl v)) (hb (.inl v))
  | inr j => exact joint_sat G w (c.set e k) j.1 j.2

private theorem reachable_set_le (G : ConstraintGraph V E) (w : E → ℕ)
    (hl : G.LoopFree) (c : Cursor n) (e : E)
    {a b : Fin (n e + 2)} (ha : (graph G n w).Legal (c.set e a).directions)
    (hb : (graph G n w).Legal (c.set e b).directions) (hab : a ≤ b) :
    (graph G n w).Reachable (c.set e a).directions (c.set e b).directions := by
  have walk (k : Fin (n e + 2)) : a ≤ k → k ≤ b →
      (graph G n w).Reachable (c.set e a).directions (c.set e k).directions := by
    induction k using Fin.induction with
    | zero =>
      intro hak _
      have heq : a = 0 := le_antisymm hak (Fin.zero_le _)
      subst a
      exact .refl
    | succ k ih =>
      intro hak hkb
      by_cases heq : a = k.succ
      · subst a
        exact .refl
      · have hak' : a ≤ k.castSucc := by
          change a.val ≤ k.val
          have hne : a.val ≠ k.val + 1 := fun h => heq (Fin.ext h)
          change a.val ≤ k.val + 1 at hak
          omega
        have hkbound : k.castSucc ≤ b := (Fin.castSucc_le_succ k).trans hkb
        exact (ih hak' hkbound).tail
          ⟨legal_set_between G w hl c e ha hb hak' hkbound,
            legal_set_between G w hl c e ha hb hak hkb,
            ⟨e, k⟩, directions_set_succ c e k⟩
  exact walk b hab le_rfl

/-- Move one cursor monotonically between its two legal endpoints, reversing one real
segment per step and fixing all segments on other old edges. -/
theorem reachable_set (G : ConstraintGraph V E) (w : E → ℕ)
    (hl : G.LoopFree) (c : Cursor n) (e : E) {a b : Fin (n e + 2)}
    (ha : (graph G n w).Legal (c.set e a).directions)
    (hb : (graph G n w).Legal (c.set e b).directions) :
    (graph G n w).Reachable (c.set e a).directions (c.set e b).directions := by
  rcases le_total a b with hab | hba
  · exact reachable_set_le G w hl c e ha hb hab
  · exact (reachable_set_le G w hl c e hb ha hba).symm

end Cursor
end PushPuzzle.NCL.ConstraintGraph.Subdivision
