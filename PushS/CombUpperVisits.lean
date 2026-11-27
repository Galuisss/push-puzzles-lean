/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPartition
import all PushS.CombTopology
import all PushS.CombPartition

/-! The actual upper-page pairing retains every even edge-visit word exactly. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

private theorem pairOff_cons_cons (a b : Token) (tail : List Token) :
    pairOff (a :: b :: tail) = (a, b) :: pairOff tail := by
  unfold pairOff
  simp only [List.zipIdx_cons, List.filterMap_cons, Nat.zero_mod, ↓reduceIte,
    List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.reduceMod]
  congr 1
  rw [List.zipIdx_eq_map_add]
  simp only [List.filterMap_map, Function.comp_def]
  apply List.filterMap_congr
  intro p hp
  simp only [Nat.add_mod, Nat.reduceMod, Nat.zero_add, Nat.mod_mod]
  rw [show 2 + p.2 = (p.2 + 1) + 1 by omega, List.getD_cons_succ]

/-- Flattening actual upper pairs recovers the complete original even-length visit word. -/
theorem pairOff_tokens (tokens : List Token) (he : tokens.length % 2 = 0) :
    ((pairOff tokens).flatMap fun p => [p.1, p.2]) = tokens := by
  induction tokens using List.twoStepInduction with
  | nil => simp [pairOff]
  | singleton a => simp at he
  | cons_cons a b tail ih =>
    have he' : tail.length % 2 = 0 := by simp only [List.length_cons] at he; omega
    rw [pairOff_cons_cons, List.flatMap_cons, ih he']
    rfl

/-- Every original source edge has an even number of actual incidence/crossing-side visits. -/
theorem edgeVisits_length_even (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeVisits width d edge).length % 2 = 0 := by
  have hlen (crossings : List Crossing) :
      (crossings.flatMap fun c => if c.forward then [c.token false, c.token true]
        else [c.token true, c.token false]).length = 2 * crossings.length := by
    induction crossings with
    | nil => rfl
    | cons c cs ih => cases hc : c.forward <;> simp [hc, ih, Nat.mul_add]
  simp only [edgeVisits, List.length_append, List.length_cons, List.length_nil, hlen]
  omega

/-- Each real upper edge-fragment list retains all visits of that exact original edge. -/
theorem edgeVisits_pairOff_tokens (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    ((pairOff (edgeVisits width d edge)).flatMap fun p => [p.1, p.2]) = edgeVisits width d edge :=
  pairOff_tokens _ (edgeVisits_length_even width d edge)

private def crossingWord (c : Crossing) : List Token :=
  if c.forward then [c.token false, c.token true] else [c.token true, c.token false]

private theorem crossingWord_mem (c : Crossing) (token : Token) :
    token ∈ crossingWord c ↔ token = c.token false ∨ token = c.token true := by
  cases hc : c.forward <;> simp [crossingWord, hc, or_comm]

private theorem crossingWord_no_tip (c : Crossing) (edge : ℕ) (dir : Bool) :
    Token.tip edge dir ∉ crossingWord c := by simp [crossingWord_mem, Crossing.token]

/-- The actual edge word contains precisely its two native tips and both sides of its crossings. -/
theorem edgeVisits_mem (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) (token : Token) :
    token ∈ edgeVisits width d edge ↔ token = .tip edge false ∨ token = .tip edge true ∨
      ∃ c ∈ crossings width d, c.edge = edge ∧ (token = c.token false ∨ token = c.token true) := by
  change token ∈ [.tip edge false] ++ (edgeCrossings width d edge).flatMap crossingWord ++ [.tip edge true] ↔ _
  simp only [List.mem_append, List.mem_singleton, List.mem_flatMap, crossingWord_mem]
  constructor
  · rintro ((ht | ⟨c, hc, ht⟩) | ht)
    · exact Or.inl ht
    · obtain ⟨hc, he⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hc)
      exact Or.inr (Or.inr ⟨c, hc, of_decide_eq_true he, ht⟩)
    · exact Or.inr (Or.inl ht)
  · rintro (ht | ht | ⟨c, hc, he, ht⟩)
    · exact Or.inl (Or.inl ht)
    · exact Or.inr ht
    · exact Or.inl (Or.inr ⟨c, (edgeCrossings_perm width d edge).mem_iff.mpr
        (List.mem_filter.mpr ⟨hc, by simp only [he, decide_true]⟩), ht⟩)

/-- Every original edge's actual tips and marked crossing sides are distinct. -/
theorem edgeVisits_nodup (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeVisits width d edge).Nodup := by
  let hits := edgeCrossings width d edge
  have hin {c : Crossing} (hc : c ∈ hits) : c ∈ crossings width d :=
    (List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hc)).1
  have hn : hits.Nodup := (edgeCrossings_perm width d edge).nodup_iff.mpr
    ((crossings_nodup width d).filter _)
  have hwords : (hits.flatMap crossingWord).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro c _
      cases hc : c.forward <;> simp [crossingWord, hc, Crossing.token]
    · refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hn
      apply List.disjoint_left.mpr
      intro token hta htb
      rcases (crossingWord_mem a token).mp hta with rfl | rfl <;>
        rcases (crossingWord_mem b _).mp htb with he | he
      · exact hab (crossing_token_injective width d false (hin ha) (hin hb) he)
      · exact Bool.noConfusion (Token.mark.inj he).2.2.2
      · exact Bool.noConfusion (Token.mark.inj he).2.2.2
      · exact hab (crossing_token_injective width d true (hin ha) (hin hb) he)
  have htip (dir : Bool) : Token.tip edge dir ∉ hits.flatMap crossingWord := by
    intro ht
    obtain ⟨c, _, ht⟩ := List.mem_flatMap.mp ht
    exact crossingWord_no_tip c edge dir ht
  change ([Token.tip edge false] ++ hits.flatMap crossingWord ++ [Token.tip edge true]).Nodup
  apply ((List.nodup_cons.mpr ⟨htip false, hwords⟩).append (by simp))
  apply List.disjoint_left.mpr
  intro token hleft hright
  simp only [List.mem_singleton] at hright
  subst token
  rcases List.mem_cons.mp hleft with h | h
  · cases h
  · exact htip true h

/-- No actual upper edge fragment joins a contour token to itself. -/
theorem edgeVisits_pairOff_distinct (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    {a b : Token} (hab : (a, b) ∈ pairOff (edgeVisits width d edge)) : a ≠ b := by
  have hn := edgeVisits_nodup width d edge
  rw [← edgeVisits_pairOff_tokens width d edge] at hn
  simpa using
    (List.nodup_flatMap.mp hn).1 (a, b) hab

private theorem filter_range_perm {α : Type} (key : α → ℕ) (xs : List α) (n : ℕ) :
    ((List.range n).flatMap fun i => xs.filter fun x => decide (key x = i)).Perm
      (xs.filter fun x => decide (key x < n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply (ih.append_right _).trans
    have hsplit := List.filter_append_perm (fun x => decide (key x < n))
      (xs.filter fun x => decide (key x < n + 1))
    have hl : (xs.filter (fun x => decide (key x < n + 1))).filter (fun x => decide (key x < n)) =
        xs.filter (fun x => decide (key x < n)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hr : (xs.filter (fun x => decide (key x < n + 1))).filter (fun x => !decide (key x < n)) =
        xs.filter (fun x => decide (key x = n)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      omega
    simpa only [hl, hr] using hsplit

/-- Regrouping all actual crossing records by their original edge retains the exact table. -/
theorem edgeCrossings_flatMap_perm (width : ℕ) (d : Graph.OrthogonalDrawing) :
    ((List.range d.2.length).flatMap fun edge => edgeCrossings width d edge).Perm (crossings width d) := by
  apply (List.Perm.flatMap_left _ (fun edge _ => edgeCrossings_perm width d edge)).trans
  have hp := filter_range_perm Crossing.edge (crossings width d) d.2.length
  have he : (crossings width d).filter (fun c => decide (c.edge < d.2.length)) = crossings width d := by
    apply List.filter_eq_self.mpr
    intro c hc
    exact decide_eq_true (crossing_edge_lt width d hc)
  simpa only [he] using hp

private def Token.sourceEdge : Token → ℕ
  | .tip edge _ | .mark edge _ _ _ => edge
  | .rotation _ _ => 0

private theorem edgeVisits_owner (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    {token : Token} (ht : token ∈ edgeVisits width d edge) : token.sourceEdge = edge := by
  rcases (edgeVisits_mem width d edge token).mp ht with rfl | rfl | ⟨c, _, he, ht⟩
  · rfl
  · rfl
  · rcases ht with rfl | rfl <;> exact he

/-- The original route array's complete visit inventory has no repeated original or marked tip. -/
theorem allEdgeVisits_nodup (width : ℕ) (d : Graph.OrthogonalDrawing) :
    ((List.range d.2.length).flatMap fun edge => edgeVisits width d edge).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro edge _
    exact edgeVisits_nodup width d edge
  · refine List.Pairwise.imp_of_mem (fun {a b} _ _ hab => ?_) (List.nodup_range (n := d.2.length))
    apply List.disjoint_left.mpr
    intro token hta htb
    exact hab ((edgeVisits_owner width d a hta).symm.trans (edgeVisits_owner width d b htb))

/-- The emitted upper edge fragments retain the entire actual route-array visit inventory. -/
theorem allUpperFragments_tokens (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (d.2.zipIdx.flatMap (fun re => pairOff (edgeVisits width d re.2))).flatMap (fun p => [p.1, p.2]) =
      (List.range d.2.length).flatMap (fun edge => edgeVisits width d edge) := by
  rw [List.flatMap_assoc]
  have he (re : List Cslib.Orthogonal.Point × ℕ) :
      ((pairOff (edgeVisits width d re.2)).flatMap fun p => [p.1, p.2]) = edgeVisits width d re.2 :=
    edgeVisits_pairOff_tokens width d re.2
  simp only [he]
  have hm := congrArg (List.flatMap (fun edge => edgeVisits width d edge)) (List.zipIdx_map_snd (l := d.2) 0)
  simpa only [List.flatMap_map, Function.comp_def, ← List.range_eq_range'] using hm

end PushPuzzle.PushS.Comb
