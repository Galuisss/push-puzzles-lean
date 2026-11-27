/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPieces

/-! The full actual augmented edge family has only its exact named endpoint contacts. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

private theorem source_contact_ends (e f : Fin G.edges.length)
    (a : Fin ((edgeCrossings width d e).length + 1)) (b : Fin ((edgeCrossings width d f).length + 1))
    (hne : Piece.source e a ≠ Piece.source (width := width) (G := G) (d := d) f b)
    (i : Fin (edgeFragment width height hd hfit e (hhead e) a).segments)
    (j : Fin (edgeFragment width height hd hfit f (hhead f) b).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (edgeFragment width height hd hfit e (hhead e) a).eval i s =
      (edgeFragment width height hd hfit f (hhead f) b).eval j t) :
    ∃ u v, (edgeFragment width height hd hfit e (hhead e) a).AtEnd i s u ∧
      (edgeFragment width height hd hfit f (hhead f) b).AtEnd j t v := by
  by_cases hef : e = f
  · subst f
    have hab : a ≠ b := fun h => hne (h ▸ rfl)
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨true, false, (edgeFragments_contact width height hd hfit e (hhead e) a b hab i j s t hs ht he).2⟩
    · have h := (edgeFragments_contact width height hd hfit e (hhead e) b a hba j i t s ht hs he.symm).2
      exact ⟨false, true, h.2, h.1⟩
  · obtain ⟨u, v, hu, hv, _⟩ := edgeFragments_contact_distinct width height hd hfit e f hef
      (hhead e) (hhead f) a b i j s t hs ht he
    exact ⟨u, v, hu, hv⟩

include height hd hfit in
private theorem tooth_contact_ends (v w : Fin d.1.length)
    (a : Fin ((toothCrossings width d v).length + 1)) (b : Fin ((toothCrossings width d w).length + 1))
    (hne : Piece.tooth v a ≠ Piece.tooth (width := width) (G := G) (d := d) w b)
    (i : Fin (toothPiece width d v a).segments) (j : Fin (toothPiece width d w b).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (toothPiece width d v a).eval i s = (toothPiece width d w b).eval j t) :
    ∃ u z, (toothPiece width d v a).AtEnd i s u ∧ (toothPiece width d w b).AtEnd j t z := by
  by_cases hvw : v = w
  · subst w
    have hab : a ≠ b := fun h => hne (h ▸ rfl)
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨true, false, (toothPieces_contact width height hd hfit v a b hab i j s t hs ht he).2⟩
    · have h := (toothPieces_contact width height hd hfit v b a hba j i t s ht hs he.symm).2
      exact ⟨false, true, h.2, h.1⟩
  · exact False.elim ((Set.disjoint_left.mp (toothPieces_disjoint width height hd hfit v w hvw a b))
      ((toothPiece width d v a).at_mem_support i hs) (he ▸ (toothPiece width d w b).at_mem_support j ht))

include height hd hfit in
private theorem spine_contact_ends (a b : Fin (d.1.length - 1)) (hne : a ≠ b)
    (i : Fin (spinePiece width d a).segments) (j : Fin (spinePiece width d b).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (spinePiece width d a).eval i s = (spinePiece width d b).eval j t) :
    ∃ u v, (spinePiece width d a).AtEnd i s u ∧ (spinePiece width d b).AtEnd j t v := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · have h := spinePieces_contact width height hd hfit a b hab i j hs ht he
    exact ⟨true, false, h.1, h.2.1⟩
  · have h := spinePieces_contact width height hd hfit b a hba j i ht hs he.symm
    exact ⟨false, true, h.2.1, h.1⟩

private theorem Piece.contact_ends (left right : Piece width G d) (hne : left ≠ right)
    (i : Fin (left.route width height hd hfit hhead).segments)
    (j : Fin (right.route width height hd hfit hhead).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (left.route width height hd hfit hhead).eval i s = (right.route width height hd hfit hhead).eval j t) :
    ∃ a b, (left.route width height hd hfit hhead).AtEnd i s a ∧ (right.route width height hd hfit hhead).AtEnd j t b := by
  cases left with
  | source e a =>
    cases right with
    | source f b => exact source_contact_ends width height hd hfit hhead e f a b hne i j hs ht he
    | spine b =>
      exact False.elim ((Set.disjoint_left.mp (edgeFragment_spinePiece_disjoint width height hd hfit e (hhead e) a b))
        ((edgeFragment width height hd hfit e (hhead e) a).at_mem_support i hs)
        (he ▸ (spinePiece width d b).at_mem_support j ht))
    | tooth v b =>
      obtain ⟨u, z, hu, hz, _⟩ := edgeFragment_toothPiece_contact width height hd hfit e (hhead e) a v b i j hs ht he
      exact ⟨u, z, hu, hz⟩
  | spine a =>
    cases right with
    | source e b =>
      exact False.elim ((Set.disjoint_left.mp (edgeFragment_spinePiece_disjoint width height hd hfit e (hhead e) b a))
        ((edgeFragment width height hd hfit e (hhead e) b).at_mem_support j ht)
        (he.symm ▸ (spinePiece width d a).at_mem_support i hs))
    | spine b => exact spine_contact_ends width height hd hfit a b (fun h => hne (h ▸ rfl)) i j hs ht he
    | tooth v b =>
      obtain ⟨u, z, hu, hz, _⟩ := toothPiece_spinePiece_contact width height hd hfit v b a j i ht hs he.symm
      exact ⟨z, u, hz, hu⟩
  | tooth v a =>
    cases right with
    | source e b =>
      obtain ⟨u, z, hu, hz, _⟩ := edgeFragment_toothPiece_contact width height hd hfit e (hhead e) b v a j i ht hs he.symm
      exact ⟨z, u, hz, hu⟩
    | spine b =>
      obtain ⟨u, z, hu, hz, _⟩ := toothPiece_spinePiece_contact width height hd hfit v a b i j hs ht he
      exact ⟨u, z, hu, hz⟩
    | tooth w b => exact tooth_contact_ends width height hd hfit v w a b hne i j hs ht he

/-- Any two distinct genuine augmented pieces contact only at their common exact named ends. -/
theorem Piece.edge_contacts (left right : Piece width G d) (hne : left ≠ right)
    (i : Fin (left.route width height hd hfit hhead).segments)
    (j : Fin (right.route width height hd hfit hhead).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (left.route width height hd hfit hhead).eval i s = (right.route width height hd hfit hhead).eval j t) :
    ∃ a b, (left.route width height hd hfit hhead).AtEnd i s a ∧
      (right.route width height hd hfit hhead).AtEnd j t b ∧ left.station width hd a = right.station width hd b := by
  obtain ⟨a, b, ha, hb⟩ := left.contact_ends width height hd hfit hhead right hne i j hs ht he
  refine ⟨a, b, ha, hb, ?_⟩
  apply stationPoint_injective width height hd hfit
  apply complexPoint_injective
  rw [← left.route_endpoint width height hd hfit hhead a, ← right.route_endpoint width height hd hfit hhead b]
  exact ((left.route width height hd hfit hhead).at_eq_endpoint i hs a ha).symm.trans
    (he.trans ((right.route width height hd hfit hhead).at_eq_endpoint j ht b hb))

end Geometry
end PushPuzzle.PushS.Comb
