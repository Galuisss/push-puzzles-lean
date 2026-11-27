/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortMasks
public import PushFS.Reduction.AnnulusShortContacts
public import PushFS.Gadgets.Wires.ShortCorners.Transit

/-! Both real neighboring long-line phases fit the protected corner's walking mask; prepared phases fit its macro mask. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem composition_y (o f : RectOrientation) (u v : ℤ) :
    (o.inverseVector (f.vector (u,v))).2=
      (o.inverseVector (f.vector (1,0))).2*u+(o.inverseVector (f.vector (0,1))).2*v := by
  rcases o with ⟨s,a,b⟩
  rcases f with ⟨t,c,d⟩
  cases s <;> cases a <;> cases b <;> cases t <;> cases c <;> cases d <;>
    simp [RectOrientation.vector,RectOrientation.inverseVector]

private theorem near_y_coefficients : ∀ (d e : Direction) (flip : Bool),RectOrientation.Perpendicular d e →
    ((lineOrientation d flip).inverseVector ((RectOrientation.choose d e).vector (1,0))).2=0 ∧
      (((lineOrientation d flip).inverseVector ((RectOrientation.choose d e).vector (0,1))).2=1 ∨
        ((lineOrientation d flip).inverseVector ((RectOrientation.choose d e).vector (0,1))).2= -1) := by decide +kernel

private theorem far_y_coefficients : ∀ d e : Direction,RectOrientation.Perpendicular d e →
    ((lineOrientation e false).inverseVector ((RectOrientation.choose d e).vector (0,1))).2=0 ∧
      (((lineOrientation e false).inverseVector ((RectOrientation.choose d e).vector (1,0))).2=1 ∨
        ((lineOrientation e false).inverseVector ((RectOrientation.choose d e).vector (1,0))).2= -1) := by decide +kernel

private theorem near_row {d e : Direction} (hd : RectOrientation.Perpendicular d e) (flip : Bool)
    (p : ℤ×ℤ) (hy : (nearRelative d e flip p).2=0) : p.2=10 := by
  have hc:=near_y_coefficients d e flip hd
  dsimp only [nearRelative] at hy
  rw [composition_y,hc.1] at hy
  rcases hc.2 with hs|hs <;> rw [hs] at hy <;> omega

private theorem far_column {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (p : ℤ×ℤ) (hy : (farRelative d e p).2=0) : p.1=10 := by
  have hc:=far_y_coefficients d e hd
  dsimp only [farRelative] at hy
  rw [composition_y,hc.1] at hy
  rcases hc.2 with hs|hs <;> rw [hs] at hy <;> omega

private theorem near_line_walking_mask {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip phase : Bool) (n : ℕ) (hn : 2301≤n) (b : Bool) (dx dy ex ey : ℕ)
    (l : lineLabels flip n) (c : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation d flip).coordinates _ _ dx dy ((lineMatching flip n hn phase b).source l)=
      (RectOrientation.choose d e).coordinates _ _ ex ey c)
    (ha : (lineOrientation d flip).coordinates _ _ dx dy (lineFarAnchor flip n hn phase b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearAnchor (cornerKindFor d e))) :
    c∈ShortCorners.allNeighbors (cornerKindFor d e) := by
  have hr:=(lineOrientation d flip).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    ((lineMatching flip n hn phase b).source l) (lineFarAnchor flip n hn phase b) c
    (ShortCorners.nearAnchor (cornerKindFor d e)) hp ha
  change nearRelative d e flip (c.1.val,c.2.val)=
    ((((lineMatching flip n hn phase b).source l).1.val : ℤ)-(n+(if flip then 20 else 0)+2 : ℕ),
      (((lineMatching flip n hn phase b).source l).2.val : ℤ)-10) at hr
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  have hb:=line_source_bounds flip n hn phase b l
  have hcy : c.2.val=10 := by
    have hh:=near_row hd flip (c.1.val,c.2.val) (by dsimp only at hy; rw [hb.2.2] at hy; omega)
    dsimp only at hh
    omega
  rw [nearRelative_x hd] at hx
  have hphase : phase.toNat≤1 := by cases phase <;> decide
  have hcx : ShortCorners.sourceX (cornerKindFor d e)+1≤c.1.val := by dsimp only at hx; omega
  simp only [ShortCorners.allNeighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  exact Or.inl ⟨hcy,hcx⟩

private theorem far_line_walking_mask {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (phase : Bool) (n : ℕ) (hn : 2301≤n) (b : Bool) (dx dy ex ey : ℕ)
    (l : lineLabels false n) (c : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation e false).coordinates _ _ dx dy ((lineMatching false n hn phase b).source l)=
      (RectOrientation.choose d e).coordinates _ _ ex ey c)
    (ha : (lineOrientation e false).coordinates _ _ dx dy (lineNearAnchor false n hn phase b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    c∈ShortCorners.allNeighbors (cornerKindFor d e) := by
  have hr:=(lineOrientation e false).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    ((lineMatching false n hn phase b).source l) (lineNearAnchor false n hn phase b) c
    (ShortCorners.farAnchor (cornerKindFor d e)) hp ha
  change farRelative d e (c.1.val,c.2.val)=
    ((((lineMatching false n hn phase b).source l).1.val : ℤ)-2,
      (((lineMatching false n hn phase b).source l).2.val : ℤ)-10) at hr
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  have hb:=line_source_bounds false n hn phase b l
  have hcx : c.1.val=10 := by
    have hh:=far_column hd (c.1.val,c.2.val) (by dsimp only at hy; rw [hb.2.2] at hy; omega)
    dsimp only at hh
    omega
  rw [farRelative_x hd] at hx
  have hcy : ShortCorners.lastY (cornerKindFor d e)+2≤c.2.val := by dsimp only at hx; omega
  simp only [ShortCorners.allNeighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  exact Or.inr ⟨hcx,hcy⟩

private theorem far_line_walking_mask_general {d e : Direction}
    (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (hf : flip=false) (phase : Bool) (n : ℕ) (hn : 2301≤n) (b : Bool) (dx dy ex ey : ℕ)
    (l : lineLabels flip n) (c : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation e flip).coordinates _ _ dx dy ((lineMatching flip n hn phase b).source l)=
      (RectOrientation.choose d e).coordinates _ _ ex ey c)
    (ha : (lineOrientation e flip).coordinates _ _ dx dy (lineNearAnchor flip n hn phase b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    c∈ShortCorners.allNeighbors (cornerKindFor d e) := by
  cases flip
  · exact far_line_walking_mask hd phase n hn b dx dy ex ey l c hp ha
  · cases hf

theorem near_selected_line_walking (q : Key) (j k : ℕ) (hjk : j=k)
    (hj : j<(curve q).length) (hk : k+1<(curve q).length) (phase b : Bool)
    (l : lineLabels (fillerFlip q j) (fillerSpan q j))
    (p : Cell (ShortCorners.width (cornerKind q k)) (ShortCorners.height (cornerKind q k)))
    (hp : (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _
      (lineOffset q j).1 (lineOffset q j).2
      ((lineMatching (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 phase b).source l)=
        (cornerOrientation q k).coordinates _ _ (cornerOffset q k).1 (cornerOffset q k).2 p) :
    p∈ShortCorners.allNeighbors (cornerKind q k) := by
  subst j
  exact near_line_walking_mask (d:=(original q k).travel) (e:=(original q (k+1)).travel)
    (turn_perpendicular q k hk) (fillerFlip q k) phase (fillerSpan q k) (filler_shape q k hj).2.1 b
    (lineOffset q k).1 (lineOffset q k).2 (cornerOffset q k).1 (cornerOffset q k).2 l p hp
    ((line_far_anchor_coordinates q k hj phase b).trans (corner_near_anchor_coordinates q k hk).symm)

theorem far_selected_line_walking (q : Key) (j k : ℕ) (hjk : j=k+1)
    (hj : j<(curve q).length) (hk : k+1<(curve q).length) (phase b : Bool)
    (l : lineLabels (fillerFlip q j) (fillerSpan q j))
    (p : Cell (ShortCorners.width (cornerKind q k)) (ShortCorners.height (cornerKind q k)))
    (hp : (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _
      (lineOffset q j).1 (lineOffset q j).2
      ((lineMatching (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 phase b).source l)=
        (cornerOrientation q k).coordinates _ _ (cornerOffset q k).1 (cornerOffset q k).2 p) :
    p∈ShortCorners.allNeighbors (cornerKind q k) := by
  subst j
  exact far_line_walking_mask_general (d:=(original q k).travel) (e:=(original q (k+1)).travel)
    (turn_perpendicular q k hk) (fillerFlip q (k+1)) (later_line_unflipped q k) phase (fillerSpan q (k+1))
    (filler_shape q (k+1) hj).2.1 b (lineOffset q (k+1)).1 (lineOffset q (k+1)).2
    (cornerOffset q k).1 (cornerOffset q k).2 l p hp
    ((line_near_anchor_coordinates q (k+1) hj phase b).trans (corner_far_anchor_coordinates q k hk).symm)

private theorem line_source_sparse (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (i j : lineLabels flip n) (d : Direction) :
    ¬Adjacent d ((lineMatching flip n hn a b).source i) ((lineMatching flip n hn a b).source j) := by
  cases flip
  · exact Chain.sparse_targets n hn a i j d
  · change FlippedChain.Label n at i j
    change ¬Adjacent d ((FlippedChain.slotMatching n hn a b).source i) ((FlippedChain.slotMatching n hn a b).source j)
    rw [FlippedChain.source_position,FlippedChain.source_position]
    exact Catalog.Tail.sparse_targets n hn a i j d

private theorem line_far_low (flip : Bool) (n : ℕ) (hn : 2301≤n) (b : Bool) (l : lineLabels flip n)
    (hx : n+(if flip then 20 else 0)≤((lineMatching flip n hn false b).source l).1.val+2) :
    ((lineMatching flip n hn false b).source l).1.val=n+(if flip then 20 else 0) ∨
      ((lineMatching flip n hn false b).source l).1.val+2=n+(if flip then 20 else 0) := by
  have hb:=line_source_bounds flip n hn false b l
  have hl:=line_last_position flip n hn false b
  simp only [Bool.toNat_false,Nat.add_zero] at hb hl
  by_cases he : ((lineMatching flip n hn false b).source l).1.val=n+(if flip then 20 else 0)
  · exact Or.inl he
  right
  by_contra hn'
  apply line_source_sparse flip n hn false b l (lineLast flip n hn) .east
  refine ⟨by omega,Fin.ext (hl.2.trans hb.2.2.symm)⟩

private theorem line_near_high (flip : Bool) (n : ℕ) (hn : 2301≤n) (b : Bool) (l : lineLabels flip n)
    (hx : ((lineMatching flip n hn true b).source l).1.val<5) :
    ((lineMatching flip n hn true b).source l).1.val=3 := by
  cases flip
  · have hh:=Catalog.chain_near_x n hn true l hx
    rcases hh with hh|⟨hh,_⟩
    · exact hh
    · cases hh
  · change FlippedChain.Label n at l
    change ((FlippedChain.slotMatching n hn true b).source l).1.val=3
    change ((FlippedChain.slotMatching n hn true b).source l).1.val<5 at hx
    rw [FlippedChain.source_position] at hx ⊢
    have hh:=Catalog.flipped_near_x n hn true l hx
    rcases hh with hh|⟨hh,_⟩
    · exact hh
    · cases hh

private theorem near_neighbors_checked : ∀ (k : ShortCorners.Kind)
    (p : Cell (ShortCorners.width k) (ShortCorners.height k)),p.2.val=10 →
      (p.1.val=ShortCorners.sourceX k+2 ∨p.1.val=ShortCorners.sourceX k+4) →
        p∈(ShortCorners.template k).neighbors := by decide +kernel

private theorem far_neighbors_checked : ∀ (k : ShortCorners.Kind)
    (p : Cell (ShortCorners.width k) (ShortCorners.height k)),p.1.val=10 →
      p.2.val=ShortCorners.lastY k+3 →p∈(ShortCorners.template k).neighbors := by decide +kernel

/-- The actual low incoming line supplies exactly the protected corner's prepared input neighbors. -/
private theorem near_line_macro_mask {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (n : ℕ) (hn : 2301≤n) (b : Bool) (dx dy ex ey : ℕ)
    (l : lineLabels flip n) (c : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation d flip).coordinates _ _ dx dy ((lineMatching flip n hn false b).source l)=
      (RectOrientation.choose d e).coordinates _ _ ex ey c)
    (ha : (lineOrientation d flip).coordinates _ _ dx dy (lineFarAnchor flip n hn false b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearAnchor (cornerKindFor d e))) :
    c∈(ShortCorners.template (cornerKindFor d e)).neighbors := by
  have hr:=(lineOrientation d flip).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    ((lineMatching flip n hn false b).source l) (lineFarAnchor flip n hn false b) c
    (ShortCorners.nearAnchor (cornerKindFor d e)) hp ha
  change nearRelative d e flip (c.1.val,c.2.val)=
    ((((lineMatching flip n hn false b).source l).1.val : ℤ)-(n+(if flip then 20 else 0)+2 : ℕ),
      (((lineMatching flip n hn false b).source l).2.val : ℤ)-10) at hr
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  dsimp only at hx hy
  have hb:=line_source_bounds flip n hn false b l
  have hcy : c.2.val=10 := by
    have hh:=near_row hd flip (c.1.val,c.2.val) (by rw [hb.2.2] at hy; omega)
    dsimp only at hh
    omega
  have hmin:=near_overlap_columns hd flip c ((lineMatching flip n hn false b).source l).1.val
    (n+(if flip then 20 else 0)) hx.symm
  have hs:=line_far_low flip n hn b l hmin
  rw [nearRelative_x hd] at hx
  dsimp only at hx
  apply near_neighbors_checked (cornerKindFor d e) c hcy
  rcases hs with hs|hs <;> omega

/-- The actual high outgoing line supplies the protected corner's prepared output neighbor. -/
private theorem far_line_macro_mask {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (n : ℕ) (hn : 2301≤n) (b : Bool) (dx dy ex ey : ℕ)
    (l : lineLabels false n) (c : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation e false).coordinates _ _ dx dy ((lineMatching false n hn true b).source l)=
      (RectOrientation.choose d e).coordinates _ _ ex ey c)
    (ha : (lineOrientation e false).coordinates _ _ dx dy (lineNearAnchor false n hn true b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    c∈(ShortCorners.template (cornerKindFor d e)).neighbors := by
  have hr:=(lineOrientation e false).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    ((lineMatching false n hn true b).source l) (lineNearAnchor false n hn true b) c
    (ShortCorners.farAnchor (cornerKindFor d e)) hp ha
  change farRelative d e (c.1.val,c.2.val)=
    ((((lineMatching false n hn true b).source l).1.val : ℤ)-2,
      (((lineMatching false n hn true b).source l).2.val : ℤ)-10) at hr
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  dsimp only at hx hy
  have hb:=line_source_bounds false n hn true b l
  have hcx : c.1.val=10 := by
    have hh:=far_column hd (c.1.val,c.2.val) (by rw [hb.2.2] at hy; omega)
    dsimp only at hh
    omega
  have hmax:=far_overlap_columns hd c ((lineMatching false n hn true b).source l).1.val hx.symm
  have hs:=line_near_high false n hn b l hmax
  rw [farRelative_x hd] at hx
  dsimp only at hx
  exact far_neighbors_checked (cornerKindFor d e) c hcx (by omega)

private theorem far_line_macro_mask_general {d e : Direction}
    (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (hf : flip=false) (n : ℕ) (hn : 2301≤n) (b : Bool) (dx dy ex ey : ℕ)
    (l : lineLabels flip n) (c : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (hp : (lineOrientation e flip).coordinates _ _ dx dy ((lineMatching flip n hn true b).source l)=
      (RectOrientation.choose d e).coordinates _ _ ex ey c)
    (ha : (lineOrientation e flip).coordinates _ _ dx dy (lineNearAnchor flip n hn true b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    c∈(ShortCorners.template (cornerKindFor d e)).neighbors := by
  cases flip
  · exact far_line_macro_mask hd n hn b dx dy ex ey l c hp ha
  · cases hf

theorem near_selected_line_macro (q : Key) (j k : ℕ) (hjk : j=k)
    (hj : j<(curve q).length) (hk : k+1<(curve q).length) (b : Bool)
    (l : lineLabels (fillerFlip q j) (fillerSpan q j))
    (p : Cell (ShortCorners.width (cornerKind q k)) (ShortCorners.height (cornerKind q k)))
    (hp : (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _
      (lineOffset q j).1 (lineOffset q j).2
      ((lineMatching (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 false b).source l)=
        (cornerOrientation q k).coordinates _ _ (cornerOffset q k).1 (cornerOffset q k).2 p) :
    p∈(ShortCorners.template (cornerKind q k)).neighbors := by
  subst j
  exact near_line_macro_mask (d:=(original q k).travel) (e:=(original q (k+1)).travel)
    (turn_perpendicular q k hk) (fillerFlip q k) (fillerSpan q k) (filler_shape q k hj).2.1 b
    (lineOffset q k).1 (lineOffset q k).2 (cornerOffset q k).1 (cornerOffset q k).2 l p hp
    ((line_far_anchor_coordinates q k hj false b).trans (corner_near_anchor_coordinates q k hk).symm)

theorem far_selected_line_macro (q : Key) (j k : ℕ) (hjk : j=k+1)
    (hj : j<(curve q).length) (hk : k+1<(curve q).length) (b : Bool)
    (l : lineLabels (fillerFlip q j) (fillerSpan q j))
    (p : Cell (ShortCorners.width (cornerKind q k)) (ShortCorners.height (cornerKind q k)))
    (hp : (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _
      (lineOffset q j).1 (lineOffset q j).2
      ((lineMatching (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 true b).source l)=
        (cornerOrientation q k).coordinates _ _ (cornerOffset q k).1 (cornerOffset q k).2 p) :
    p∈(ShortCorners.template (cornerKind q k)).neighbors := by
  subst j
  exact far_line_macro_mask_general (d:=(original q k).travel) (e:=(original q (k+1)).travel)
    (turn_perpendicular q k hk) (fillerFlip q (k+1)) (later_line_unflipped q k) (fillerSpan q (k+1))
    (filler_shape q (k+1) hj).2.1 b (lineOffset q (k+1)).1 (lineOffset q (k+1)).2
    (cornerOffset q k).1 (cornerOffset q k).2 l p hp
    ((line_near_anchor_coordinates q (k+1) hj true b).trans (corner_far_anchor_coordinates q k hk).symm)

theorem near_selected_corner_slots (q : Key) (j k : ℕ) (hjk : j=k)
    (hj : j<(curve q).length) (hk : k+1<(curve q).length) (a b phase : Bool)
    (p : Cell (lineBase (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 a b).width
      (lineBase (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 a b).height)
    (l : Fin (ShortCorners.count (cornerKind q k)))
    (hp : (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _ (lineOffset q j).1 (lineOffset q j).2 p=
      (cornerOrientation q k).coordinates _ _ (cornerOffset q k).1 (cornerOffset q k).2 ((ShortCorners.template (cornerKind q k)).position phase l)) :
    p.2.val=10 ∧(p.1.val=fillerSpan q j+(if fillerFlip q j then 20 else 0)+2+phase.toNat ∨
      phase=false ∧p.1.val=fillerSpan q j+(if fillerFlip q j then 20 else 0)+4) := by
  subst j
  exact short_near_line_slots (d:=(original q k).travel) (e:=(original q (k+1)).travel)
    (turn_perpendicular q k hk) (fillerFlip q k) phase (fillerSpan q k) (filler_shape q k hj).2.1 a b
    (lineOffset q k).1 (lineOffset q k).2 (cornerOffset q k).1 (cornerOffset q k).2 p l hp
    ((line_far_anchor_coordinates q k hj a b).trans (corner_near_anchor_coordinates q k hk).symm)

theorem far_selected_corner_slots (q : Key) (j k : ℕ) (hjk : j=k+1)
    (hj : j<(curve q).length) (hk : k+1<(curve q).length) (a b phase : Bool)
    (p : Cell (lineBase (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 a b).width
      (lineBase (fillerFlip q j) (fillerSpan q j) (filler_shape q j hj).2.1 a b).height)
    (l : Fin (ShortCorners.count (cornerKind q k)))
    (hp : (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _ (lineOffset q j).1 (lineOffset q j).2 p=
      (cornerOrientation q k).coordinates _ _ (cornerOffset q k).1 (cornerOffset q k).2 ((ShortCorners.template (cornerKind q k)).position phase l)) :
    p.2.val=10 ∧p.1.val=phase.toNat := by
  subst j
  exact short_far_line_slots_general (d:=(original q k).travel) (e:=(original q (k+1)).travel)
    (turn_perpendicular q k hk) (fillerFlip q (k+1)) (later_line_unflipped q k) phase (fillerSpan q (k+1))
    (filler_shape q (k+1) hj).2.1 a b (lineOffset q (k+1)).1 (lineOffset q (k+1)).2
    (cornerOffset q k).1 (cornerOffset q k).2 p l hp
    ((line_near_anchor_coordinates q (k+1) hj a b).trans (corner_far_anchor_coordinates q k hk).symm)

end PushPuzzle.PushFS.Reduction.GateTileRouting
