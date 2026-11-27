/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.StorageImage
public import PushFS.Gadgets.Wires.Catalog.RotateCertificate
public import PushFS.RectOrientation
public import PushFS.SlotRelabel

/-! Actual rectangular storage images straighten through the inverse D4 map of their ambient board. -/

@[expose] public section
namespace PushPuzzle.PushFS.RectOrientation

def inverse (o : RectOrientation) : RectOrientation :=
  ⟨o.swapAxes,if o.swapAxes then o.flipY else o.flipX,if o.swapAxes then o.flipX else o.flipY⟩

def undo (o : RectOrientation) (W H : ℕ) : GridIsometry W H (o.width W H) (o.height W H) :=
  ((inverse o).axis W H).geometry

def undoOffset (o : RectOrientation) (W H w h dx dy : ℕ) : ℕ×ℕ :=
  let x:=if o.flipX then W-dx-o.width w h else dx
  let y:=if o.flipY then H-dy-o.height w h else dy
  if o.swapAxes then (y,x) else (x,y)

theorem undo_fits (o : RectOrientation) (W H w h dx dy : ℕ)
    (hx : dx+o.width w h≤W) (hy : dy+o.height w h≤H) :
    (o.undoOffset W H w h dx dy).1+w≤o.width W H ∧
      (o.undoOffset W H w h dx dy).2+h≤o.height W H := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp only [undoOffset,width,height,Bool.false_eq_true,ite_false,ite_true] at * <;> omega

private theorem undoPoint_offset (o : RectOrientation) (W H w h dx dy : ℕ)
    (hx : dx+o.width w h≤W) (hy : dy+o.height w h≤H) (p : Cell w h) :
    o.inverse.point W H (dx+(o.point w h (p.1.val,p.2.val)).1,dy+(o.point w h (p.1.val,p.2.val)).2)=
      ((o.undoOffset W H w h dx dy).1+p.1.val,(o.undoOffset W H w h dx dy).2+p.2.val) := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp only [inverse,point,undoOffset,width,height,Bool.false_eq_true,ite_false,ite_true] at *
  all_goals apply Prod.ext <;> dsimp only <;> omega

theorem undo_cells (o : RectOrientation) (W H w h dx dy : ℕ)
    (hx : dx+o.width w h≤W) (hy : dy+o.height w h≤H) (p : Cell w h) :
    (o.undo W H).cells ((GridEmbedding.translate dx dy hx hy).cells ((o.axis w h).geometry.cells p))=
      (GridEmbedding.translate (o.undoOffset W H w h dx dy).1 (o.undoOffset W H w h dx dy).2
        (o.undo_fits W H w h dx dy hx hy).1 (o.undo_fits W H w h dx dy hx hy).2).cells p := by
  have hn:=undoPoint_offset o W H w h dx dy hx hy p
  rw [o.point_cells] at hn
  have he:=o.inverse.point_cells W H
    ((GridEmbedding.translate dx dy hx hy).cells ((o.axis w h).geometry.cells p))
  have ht:=he.symm.trans hn
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst ht
  · exact congrArg Prod.snd ht

end PushPuzzle.PushFS.RectOrientation

namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

variable {I J : Instance} {L A : Type} [Fintype L] [Fintype A]

private theorem linear_of_rail {W H : ℕ} (B : Board W H) (anchor : PushFS.Cell W H) (t : AxisTrack)
    (hr : t.Rail) (hs : ∀p,component B p=component B anchor→t.Supports p) :
    ComponentLinear (component B anchor) := by
  cases t with
  | outside=>cases hr
  | horizontal y=>
    right
    intro p q hp hq
    exact Fin.ext ((hs p hp).trans (hs q hq).symm)
  | vertical x=>
    left
    intro p q hp hq
    exact Fin.ext ((hs p hp).trans (hs q hq).symm)
  | sink x y=>cases hr

private theorem linear_axis {w h W H : ℕ} (e : AxisIsometry w h W H) (B : Board w h)
    (anchor : PushFS.Cell w h) (hl : ComponentLinear (component B anchor)) :
    ComponentLinear (component (e.geometry.board B) (e.geometry.cells anchor)) := by
  rcases hl with hx|hy
  · apply linear_of_rail (e.geometry.board B) (e.geometry.cells anchor) (e.name (.vertical anchor.1.val))
      (e.rail _ trivial)
    intro p hp
    obtain ⟨p,rfl⟩:=e.geometry.cells.surjective p
    exact e.supported p _ (congrArg Fin.val (hx p anchor (component_reflect e.geometry B hp) rfl))
  · apply linear_of_rail (e.geometry.board B) (e.geometry.cells anchor) (e.name (.horizontal anchor.2.val))
      (e.rail _ trivial)
    intro p hp
    obtain ⟨p,rfl⟩:=e.geometry.cells.surjective p
    exact e.supported p _ (congrArg Fin.val (hy p anchor (component_reflect e.geometry B hp) rfl))

/-- Actual C1–C3 certificates transport through every rectangular D4 placement. -/
theorem rectCertificate (M : SlotMatching I L) (cert : Certificate I) (o : RectOrientation) :
    Certificate (((o.axis I.width I.height).geometry).reorientInstance I) :=
  rotateCertificate M cert _ (linear_axis (o.axis I.width I.height) I.board)

private theorem coord_x (o : RectOrientation) {w h : ℕ} (p : PushFS.Cell w h) :
    (((o.axis w h).geometry.cells p).1.val)=
      if o.flipX then o.width w h-((if o.swapAxes then p.2.val else p.1.val)+1)
      else if o.swapAxes then p.2.val else p.1.val :=
  by
    have hh:=(congrArg Prod.fst (o.point_cells w h p)).symm
    cases hs:o.swapAxes <;> simpa only [RectOrientation.point,hs,ite_true,ite_false,Bool.false_eq_true] using hh

private theorem coord_y (o : RectOrientation) {w h : ℕ} (p : PushFS.Cell w h) :
    (((o.axis w h).geometry.cells p).2.val)=
      if o.flipY then o.height w h-((if o.swapAxes then p.1.val else p.2.val)+1)
      else if o.swapAxes then p.1.val else p.2.val :=
  by
    have hh:=(congrArg Prod.snd (o.point_cells w h p)).symm
    cases hs:o.swapAxes <;> simpa only [RectOrientation.point,hs,ite_true,ite_false,Bool.false_eq_true] using hh

/-- Every actual rectangular D4 map preserves the matching's two coordinate orders. -/
theorem rectOrdered (M : SlotMatching I L) (ho : M.Ordered) (o : RectOrientation) :
    (M.reorient (o.axis I.width I.height).geometry).Ordered where
  horizontal i j hc hij:=by
    have hc0:=component_reflect (o.axis I.width I.height).geometry I.board hc
    change (((o.axis I.width I.height).geometry.cells (M.source i)).1.val)<(((o.axis I.width I.height).geometry.cells (M.source j)).1.val) at hij
    change (((o.axis I.width I.height).geometry.cells (M.target i)).1.val)<(((o.axis I.width I.height).geometry.cells (M.target j)).1.val)
    rw [coord_x,coord_x] at hij ⊢
    have hsi1:=(M.source i).1.isLt
    have hsj1:=(M.source j).1.isLt
    have hti1:=(M.target i).1.isLt
    have htj1:=(M.target j).1.isLt
    have hsi2:=(M.source i).2.isLt
    have hsj2:=(M.source j).2.isLt
    have hti2:=(M.target i).2.isLt
    have htj2:=(M.target j).2.isLt
    cases hs:o.swapAxes <;> cases hx:o.flipX <;> simp only [RectOrientation.width,hs,hx,ite_true,ite_false,Bool.false_eq_true] at hij ⊢
    · exact ho.horizontal i j hc0 hij
    · have hr:=ho.horizontal j i hc0.symm (by omega)
      omega
    · exact ho.vertical i j hc0 hij
    · have hr:=ho.vertical j i hc0.symm (by omega)
      omega
  vertical i j hc hij:=by
    have hc0:=component_reflect (o.axis I.width I.height).geometry I.board hc
    change (((o.axis I.width I.height).geometry.cells (M.source i)).2.val)<(((o.axis I.width I.height).geometry.cells (M.source j)).2.val) at hij
    change (((o.axis I.width I.height).geometry.cells (M.target i)).2.val)<(((o.axis I.width I.height).geometry.cells (M.target j)).2.val)
    rw [coord_y,coord_y] at hij ⊢
    have hsi1:=(M.source i).1.isLt
    have hsj1:=(M.source j).1.isLt
    have hti1:=(M.target i).1.isLt
    have htj1:=(M.target j).1.isLt
    have hsi2:=(M.source i).2.isLt
    have hsj2:=(M.source j).2.isLt
    have hti2:=(M.target i).2.isLt
    have htj2:=(M.target j).2.isLt
    cases hs:o.swapAxes <;> cases hy:o.flipY <;> simp only [RectOrientation.height,hs,hy,ite_true,ite_false,Bool.false_eq_true] at hij ⊢
    · exact ho.vertical i j hc0 hij
    · have hr:=ho.vertical j i hc0.symm (by omega)
      omega
    · exact ho.horizontal i j hc0 hij
    · have hr:=ho.horizontal j i hc0.symm (by omega)
      omega

namespace StorageImage

variable {M : SlotMatching I L} {N : SlotMatching J A}

def relabel {K : Type} [Fintype K] (g : StorageImage M N) (e : K≃A) :
    StorageImage M (N.relabel e) where
  dx:=g.dx
  dy:=g.dy
  fit_x:=g.fit_x
  fit_y:=g.fit_y
  labels:=e.toEmbedding.trans g.labels
  walls:=g.walls
  sources l:=g.sources (e l)
  targets l:=g.targets (e l)

/-- Retain every actual physical identity while undoing the rectangular glyph's orientation. -/
def straighten (o : RectOrientation) (g : StorageImage M (N.reorient (o.axis J.width J.height).geometry)) :
    StorageImage (M.reorient (o.undo I.width I.height)) N := by
  let dx:=(o.undoOffset I.width I.height J.width J.height g.dx g.dy).1
  let dy:=(o.undoOffset I.width I.height J.width J.height g.dx g.dy).2
  have hf:=o.undo_fits I.width I.height J.width J.height g.dx g.dy g.fit_x g.fit_y
  have he:=o.undo_cells I.width I.height J.width J.height g.dx g.dy g.fit_x g.fit_y
  refine ⟨dx,dy,hf.1,hf.2,g.labels,?_,?_,?_⟩
  · intro p
    change (GridEmbedding.translate dx dy hf.1 hf.2).cells p∈((o.undo I.width I.height).board I.board).walls ↔_
    rw [←he p]
    exact ((o.undo I.width I.height).mem_walls I.board _).trans
      ((g.walls _).trans ((o.axis J.width J.height).geometry.mem_walls J.board p))
  · intro l
    change (o.undo I.width I.height).cells (M.source (g.labels l))=_
    rw [g.sources]
    exact he (N.source l)
  · intro l
    change (o.undo I.width I.height).cells (M.target (g.labels l))=_
    rw [g.targets]
    exact he (N.target l)

end StorageImage
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
