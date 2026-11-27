/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortWallGeometry
public import PushFS.Reduction.AnnulusShortOwners

/-! Full true wall agreement across protected short-turn contacts, uniformly in every actual long-line length. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem short_near_walls_of_relative {d e : Direction}
    (hd : RectOrientation.Perpendicular d e) (flip : Bool)
    (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (q : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hrel : nearRelative d e flip (q.1.val,q.2.val)=
      ((p.1.val : ℤ)-(n+(if flip then 20 else 0)+2 : ℕ),(p.2.val : ℤ)-10)) :
    p∈(lineBase flip n hn a b).board.walls ↔ q∈(ShortCorners.template (cornerKindFor d e)).walls := by
  let span := n+(if flip then 20 else 0)
  have hx := near_overlap_columns hd flip q p.1.val span (congrArg Prod.fst hrel).symm
  have hdims := line_dimensions flip n hn a b
  have hw : n+(if flip then 25 else 5)=span+5 := by cases flip <;> dsimp [span]
  have hpX : p.1.val<span+5 := by have := p.1.isLt; omega
  have hpY : p.2.val<21 := by have := p.2.isLt; omega
  let i : Fin 7 := ⟨p.1.val+2-span,by omega⟩
  let y : Fin 21 := ⟨p.2.val,hpY⟩
  have hsample : nearRelative d e flip (q.1.val,q.2.val)=((i.val : ℤ)-4,(y.val : ℤ)-10) := by
    rw [hrel]
    apply Prod.ext <;> dsimp [i,y,span] at hx ⊢; omega
  have hq : ((q.1.val : ℤ),(q.2.val : ℤ))=nearSample d e flip i y :=
    (lineOrientation d flip).solve_relative (RectOrientation.choose d e)
      ((q.1.val : ℤ),(q.2.val : ℤ)) ((ShortCorners.sourceX (cornerKindFor d e) : ℤ),10)
      ((i.val : ℤ)-4,(y.val : ℤ)-10) hsample
  have hinside : ShortInside (cornerKindFor d e) (nearSample d e flip i y) := by
    rw [←hq]
    have hqX := q.1.isLt
    have hqY := q.2.isLt
    dsimp [ShortInside]
    omega
  have hwall := short_near_wall_checked d e flip i y hd hinside
  rw [←hq,shortWall_cell (cornerKindFor d e) q] at hwall
  rw [line_far_walls flip n hn a b p hx,Template.mem_walls (ShortCorners.template (cornerKindFor d e)) q,hwall]
  simp only [farGuard,decide_eq_true_eq,y]

private theorem short_far_walls_of_relative {d e : Direction}
    (hd : RectOrientation.Perpendicular d e)
    (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase false n hn a b).width (lineBase false n hn a b).height)
    (q : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hrel : farRelative d e (q.1.val,q.2.val)=((p.1.val : ℤ)-2,(p.2.val : ℤ)-10)) :
    p∈(lineBase false n hn a b).board.walls ↔ q∈(ShortCorners.template (cornerKindFor d e)).walls := by
  have hx := far_overlap_columns hd q p.1.val (congrArg Prod.fst hrel).symm
  have hdims := line_dimensions false n hn a b
  have hpY : p.2.val<21 := by have := p.2.isLt; omega
  let i : Fin 5 := ⟨p.1.val,hx⟩
  let y : Fin 21 := ⟨p.2.val,hpY⟩
  have hq : ((q.1.val : ℤ),(q.2.val : ℤ))=farSample d e i y :=
    (lineOrientation e false).solve_relative (RectOrientation.choose d e)
      ((q.1.val : ℤ),(q.2.val : ℤ)) (10,(ShortCorners.lastY (cornerKindFor d e)+2 : ℕ))
      ((p.1.val : ℤ)-2,(p.2.val : ℤ)-10) hrel
  have hinside : ShortInside (cornerKindFor d e) (farSample d e i y) := by
    rw [←hq]
    have hqX := q.1.isLt
    have hqY := q.2.isLt
    dsimp [ShortInside]
    omega
  have hwall := short_far_wall_checked d e i y hd hinside
  rw [←hq,shortWall_cell (cornerKindFor d e) q] at hwall
  rw [line_near_walls false n hn a b p hx,Template.mem_walls (ShortCorners.template (cornerKindFor d e)) q,hwall]
  simp only [nearGuard,decide_eq_true_eq,y]

theorem short_near_walls_placed {d e : Direction} (hd : RectOrientation.Perpendicular d e) (flip : Bool)
    (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (q : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation d flip).coordinates _ _ dx dy p=(RectOrientation.choose d e).coordinates _ _ ex ey q)
    (ha : (lineOrientation d flip).coordinates _ _ dx dy (lineFarAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearAnchor (cornerKindFor d e))) :
    p∈(lineBase flip n hn a b).board.walls ↔ q∈(ShortCorners.template (cornerKindFor d e)).walls := by
  have hh := (lineOrientation d flip).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    p (lineFarAnchor flip n hn a b) q (ShortCorners.nearAnchor (cornerKindFor d e)) hp ha
  exact short_near_walls_of_relative hd flip n hn a b p q hh

theorem short_far_walls_placed {d e : Direction} (hd : RectOrientation.Perpendicular d e) (flip : Bool)
    (hf : flip=false) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (q : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation e flip).coordinates _ _ dx dy p=(RectOrientation.choose d e).coordinates _ _ ex ey q)
    (ha : (lineOrientation e flip).coordinates _ _ dx dy (lineNearAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    p∈(lineBase flip n hn a b).board.walls ↔ q∈(ShortCorners.template (cornerKindFor d e)).walls := by
  cases flip
  · have hh := (lineOrientation e false).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
      p (lineNearAnchor false n hn a b) q (ShortCorners.farAnchor (cornerKindFor d e)) hp ha
    exact short_far_walls_of_relative hd n hn a b p q hh
  · cases hf

end PushPuzzle.PushFS.Reduction.GateTileRouting
