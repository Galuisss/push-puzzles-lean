/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombUpperVisits
import all PushS.CombUpperVisits

/-! Literal source-fragment end tokens retain their exact original even and odd visit positions. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem crossingWords_length (hits : List Crossing) : (hits.flatMap crossingWord).length = 2 * hits.length := by
  induction hits with
  | nil => rfl
  | cons c cs ih => cases hc : c.forward <;> simp [crossingWord, hc, ih, Nat.mul_add]

private theorem crossingWords_getD (hits : List Crossing) (index : ℕ) (hi : index < hits.length) (side : Bool) :
    (hits.flatMap crossingWord).getD (2 * index + side.toNat) (.tip 0 false) =
      (hits.get ⟨index, hi⟩).token (if side then (hits.get ⟨index, hi⟩).forward else !(hits.get ⟨index, hi⟩).forward) := by
  induction hits generalizing index with
  | nil => simp at hi
  | cons c hits ih =>
    cases index with
    | zero => cases side <;> cases hc : c.forward <;> simp [crossingWord, hc]
    | succ index =>
      have hi' : index < hits.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi
      have hindex : 2 * (index + 1) + side.toNat = (2 * index + side.toNat) + 2 := by omega
      cases hc : c.forward <;>
        simpa only [List.flatMap_cons, crossingWord, hc, Bool.false_eq_true, ite_false, ite_true,
          List.cons_append, List.nil_append, hindex, List.getD_cons_succ, List.get_cons_succ] using ih index hi'

/-- Each actual paired position reads precisely its original even and odd visit entries. -/
theorem pairOff_getD (tokens : List Token) (he : tokens.length % 2 = 0) (index : ℕ) :
    (pairOff tokens).getD index (.tip 0 false, .tip 0 false) =
      (tokens.getD (2 * index) (.tip 0 false), tokens.getD (2 * index + 1) (.tip 0 false)) := by
  induction tokens using List.twoStepInduction generalizing index with
  | nil => simp [pairOff]
  | singleton a => simp at he
  | cons_cons a b tail ih =>
    have he' : tail.length % 2 = 0 := by simp only [List.length_cons] at he; omega
    rw [pairOff_cons_cons]
    cases index with
    | zero => simp
    | succ index =>
      rw [show 2 * (index + 1) = 2 * index + 2 by omega]
      simpa only [List.getD_cons_succ] using ih he' index

/-- The actual upper pairing contains one fragment for each pair of consecutive source visits. -/
theorem pairOff_length (tokens : List Token) (he : tokens.length % 2 = 0) :
    (pairOff tokens).length = tokens.length / 2 := by
  induction tokens using List.twoStepInduction with
  | nil => simp [pairOff]
  | singleton a => simp at he
  | cons_cons a b tail ih =>
    have he' : tail.length % 2 = 0 := by simp only [List.length_cons] at he; omega
    rw [pairOff_cons_cons]
    simp only [List.length_cons, ih he']
    omega

/-- The complete original edge visit array has exactly two entries per retained source fragment. -/
theorem edgeVisits_length (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeVisits width d edge).length = 2 * ((edgeCrossings width d edge).length + 1) := by
  change ([Token.tip edge false] ++ (edgeCrossings width d edge).flatMap crossingWord ++ [Token.tip edge true]).length = _
  simp only [List.length_append, List.length_cons, List.length_nil, crossingWords_length]
  omega

/-- Every actual source edge retains precisely one upper fragment more than its crossing count. -/
theorem edgeVisits_pairOff_length (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (pairOff (edgeVisits width d edge)).length = (edgeCrossings width d edge).length + 1 := by
  rw [pairOff_length _ (edgeVisits_length_even width d edge), edgeVisits_length]
  omega

/-- Every crossing-side entry is read at its exact original odd or following even visit index. -/
theorem edgeVisits_crossing_token (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    (edgeVisits width d edge).getD (2 * hit.val + 1 + side.toNat) (.tip 0 false) =
      ((edgeCrossings width d edge).get hit).token
        (if side then ((edgeCrossings width d edge).get hit).forward else !((edgeCrossings width d edge).get hit).forward) := by
  change (Token.tip edge false :: ((edgeCrossings width d edge).flatMap crossingWord ++ [Token.tip edge true])).getD
    (2 * hit.val + 1 + side.toNat) (.tip 0 false) = _
  rw [show 2 * hit.val + 1 + side.toNat = (2 * hit.val + side.toNat) + 1 by omega, List.getD_cons_succ]
  have hi : 2 * hit.val + side.toNat < ((edgeCrossings width d edge).flatMap crossingWord).length := by
    rw [crossingWords_length]
    have hh := hit.isLt
    cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  rw [List.getD_append _ _ _ _ hi]
  exact crossingWords_getD _ hit.val hit.isLt side

/-- The exact original source visit token at one Boolean end of an indexed retained fragment. -/
@[expose] def fragmentToken (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) : Token :=
  (edgeVisits width d edge).getD (2 * piece.val + side.toNat) (.tip 0 false)

private theorem fragmentToken_index_lt (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
    2 * piece.val + side.toNat < (edgeVisits width d edge).length := by
  rw [edgeVisits_length]
  have hp := piece.isLt
  cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Each actual source-fragment token is an in-bounds original edge visit occurrence. -/
theorem fragmentToken_mem (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
    fragmentToken width d edge piece side ∈ edgeVisits width d edge := by
  have hi := fragmentToken_index_lt width d edge piece side
  rw [fragmentToken, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem edgeVisits_shape (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) {token : Token}
    (ht : token ∈ edgeVisits width d edge) :
    (∃ side, token = .tip edge side) ∨ ∃ slot vertex side, token = .mark edge slot vertex side := by
  rcases (edgeVisits_mem width d edge token).mp ht with ht | ht | ⟨c, _, he, ht⟩
  · exact Or.inl ⟨false, ht⟩
  · exact Or.inl ⟨true, ht⟩
  · rcases ht with rfl | rfl <;> exact Or.inr ⟨c.segment, c.vertex, _, by rw [Crossing.token, he]⟩

/-- Equal literal fragment-end tokens retain the exact original source edge identity. -/
theorem fragmentToken_same_edge (width : ℕ) (d : Graph.OrthogonalDrawing) (left right : ℕ)
    (a : Fin ((edgeCrossings width d left).length + 1)) (b : Fin ((edgeCrossings width d right).length + 1))
    (s t : Bool) (he : fragmentToken width d left a s = fragmentToken width d right b t) : left = right := by
  have ha := edgeVisits_shape width d left (fragmentToken_mem width d left a s)
  have hb := edgeVisits_shape width d right (fragmentToken_mem width d right b t)
  rw [he] at ha
  rcases ha with ⟨u, hu⟩ | ⟨i, v, u, hu⟩ <;>
    rcases hb with ⟨z, hz⟩ | ⟨j, w, z, hz⟩
  · exact (Token.tip.inj (hu.symm.trans hz)).1
  · cases hu.symm.trans hz
  · cases hu.symm.trans hz
  · exact (Token.mark.inj (hu.symm.trans hz)).1

/-- Equal source-fragment tokens identify their exact original piece index and Boolean end tag. -/
theorem fragmentToken_same_end (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (left right : Fin ((edgeCrossings width d edge).length + 1)) (s t : Bool)
    (he : fragmentToken width d edge left s = fragmentToken width d edge right t) : left = right ∧ s = t := by
  have hi := (edgeVisits_nodup width d edge).getD_inj (fallback := Token.tip 0 false) (fragmentToken_index_lt width d edge left s)
    (fragmentToken_index_lt width d edge right t)
  have hindex := hi.mp he
  have hval : left.val = right.val := by
    cases s <;> cases t <;> simp only [Bool.toNat_false, Bool.toNat_true] at hindex <;> omega
  refine ⟨Fin.ext hval, ?_⟩
  cases s <;> cases t <;> simp only [Bool.toNat_false, Bool.toNat_true, hval] at hindex <;> first | rfl | omega

/-- The actual fragment's two original tokens are exactly its literal emitted upper-page pair. -/
theorem fragmentToken_pairOff (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) :
    (pairOff (edgeVisits width d edge)).getD piece (.tip 0 false, .tip 0 false) =
      (fragmentToken width d edge piece false, fragmentToken width d edge piece true) := by
  simpa only [fragmentToken, Bool.toNat_false, Nat.add_zero, Bool.toNat_true] using
    pairOff_getD (edgeVisits width d edge) (edgeVisits_length_even width d edge) piece.val

/-- The first actual fragment retains the original false native source tip. -/
theorem fragmentToken_first (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    fragmentToken width d edge 0 false = .tip edge false := by
  simp [fragmentToken, edgeVisits]

/-- The last actual fragment retains the original true native source tip. -/
theorem fragmentToken_last (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    fragmentToken width d edge (Fin.last (edgeCrossings width d edge).length) true = .tip edge true := by
  let visitPrefix := [Token.tip edge false] ++ (edgeCrossings width d edge).flatMap crossingWord
  have hlen : visitPrefix.length = 2 * (edgeCrossings width d edge).length + 1 := by
    simp only [visitPrefix, List.length_append, List.length_cons, List.length_nil, crossingWords_length]
    omega
  change (visitPrefix ++ [Token.tip edge true]).getD (2 * (edgeCrossings width d edge).length + 1) (.tip 0 false) = _
  rw [← hlen, List.getD_append_right _ _ _ _ le_rfl]
  simp

/-- The preceding fragment meets a real crossing at its side opposite to the source direction. -/
theorem fragmentToken_crossing_before (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (hit : Fin (edgeCrossings width d edge).length) :
    fragmentToken width d edge hit.castSucc true =
      ((edgeCrossings width d edge).get hit).token (!((edgeCrossings width d edge).get hit).forward) := by
  simpa only [fragmentToken, Fin.val_castSucc, Bool.toNat_true, Bool.toNat_false, Nat.add_zero,
    Bool.false_eq_true, ite_false] using edgeVisits_crossing_token width d edge hit false

/-- The following fragment leaves the same crossing at its side in the original source direction. -/
theorem fragmentToken_crossing_after (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (hit : Fin (edgeCrossings width d edge).length) :
    fragmentToken width d edge hit.succ false =
      ((edgeCrossings width d edge).get hit).token ((edgeCrossings width d edge).get hit).forward := by
  have h := edgeVisits_crossing_token width d edge hit true
  simpa only [fragmentToken, Fin.val_succ, Bool.toNat_false, Nat.add_zero, Bool.toNat_true, ite_true,
    Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

end PushPuzzle.PushS.Comb
