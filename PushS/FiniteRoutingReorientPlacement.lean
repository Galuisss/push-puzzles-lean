/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingOrientation
public import PushFS.Gadgets.Wires.Catalog.RectImages

/-! Literal placement offsets when a complete physical board and its primitive rectangle are reoriented together. -/

@[expose] public section
namespace PushPuzzle.PushFS.RectOrientation

/-- New lower-left coordinate of the actual finite rectangle after the whole-board symmetry. -/
def placedX (o : RectOrientation) (W H w h dx dy : ℕ) : ℕ :=
  if o.flipX then o.width W H-((if o.swapAxes then dy else dx)+o.width w h) else (if o.swapAxes then dy else dx)

def placedY (o : RectOrientation) (W H w h dx dy : ℕ) : ℕ :=
  if o.flipY then o.height W H-((if o.swapAxes then dx else dy)+o.height w h) else (if o.swapAxes then dx else dy)

theorem placed_fits (o : RectOrientation) {W H w h dx dy : ℕ} (hx : dx+w ≤ W) (hy : dy+h ≤ H) :
    o.placedX W H w h dx dy+o.width w h ≤ o.width W H ∧
      o.placedY W H w h dx dy+o.height w h ≤ o.height W H := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp only [placedX,placedY,width,height,Bool.false_eq_true,ite_false,ite_true] <;> omega

private theorem placed_point (o : RectOrientation) {W H w h dx dy : ℕ} (hx : dx+w ≤ W)
    (hy : dy+h ≤ H)
    (p : ℕ × ℕ) (hpx : p.1 < w) (hpy : p.2 < h) :
    o.point W H (dx+p.1,dy+p.2) =
      (o.placedX W H w h dx dy+(o.point w h p).1, o.placedY W H w h dx dy+(o.point w h p).2) := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    dsimp [point,placedX,placedY,width,height] <;> apply Prod.ext <;> omega

theorem inverse_direction (o : RectOrientation) (d : Direction) :
    o.inverse.direction (o.direction d) = d := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases d <;> rfl

/-- Inverse rectangular dimensions recover the exact original rectangle size. -/
private theorem inverse_size (o : RectOrientation) (w h : ℕ) :
    o.inverse.width (o.width w h) (o.height w h) = w ∧
      o.inverse.height (o.width w h) (o.height w h) = h := by
  rcases o with ⟨s,x,y⟩
  cases s <;> exact ⟨rfl,rfl⟩

private theorem inverse_point (o : RectOrientation) {w h : ℕ} (p : Cell w h) :
    o.inverse.point (o.width w h) (o.height w h) (o.point w h (p.1.val,p.2.val)) = (p.1.val,p.2.val) := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    dsimp [inverse,point,width,height] <;> apply Prod.ext <;> omega

def normalizedX (o : RectOrientation) (W H w h dx dy : ℕ) : ℕ :=
  o.inverse.placedX W H (o.width w h) (o.height w h) dx dy

def normalizedY (o : RectOrientation) (W H w h dx dy : ℕ) : ℕ :=
  o.inverse.placedY W H (o.width w h) (o.height w h) dx dy

theorem normalized_fits (o : RectOrientation) {W H w h dx dy : ℕ}
    (hx : dx+o.width w h ≤ W) (hy : dy+o.height w h ≤ H) :
    o.normalizedX W H w h dx dy+w ≤ o.inverse.width W H ∧
      o.normalizedY W H w h dx dy+h ≤ o.inverse.height W H := by
  have hh := o.inverse.placed_fits hx hy
  rw [(o.inverse_size w h).1,(o.inverse_size w h).2] at hh
  exact hh

def normalizedEmbedding (o : RectOrientation) {W H w h dx dy : ℕ}
    (hx : dx+o.width w h ≤ W) (hy : dy+o.height w h ≤ H) :
    GridEmbedding w h (o.inverse.width W H) (o.inverse.height W H) :=
  GridEmbedding.translate (o.normalizedX W H w h dx dy) (o.normalizedY W H w h dx dy)
    (o.normalized_fits hx hy).1 (o.normalized_fits hx hy).2

/-- Normalizing an actually placed oriented rectangle recovers its literal canonical cell map. -/
theorem normalized_cell (o : RectOrientation) {W H w h dx dy : ℕ}
    (hx : dx+o.width w h ≤ W) (hy : dy+o.height w h ≤ H)
    (p : Cell w h) (q : Cell W H)
    (hq : (q.1.val,q.2.val) =
      (dx+(o.point w h (p.1.val,p.2.val)).1,dy+(o.point w h (p.1.val,p.2.val)).2)) :
    (o.inverse.axis W H).geometry.cells q = (o.normalizedEmbedding hx hy).cells p := by
  have hpoint := o.point_cells w h p
  have hpx : (o.point w h (p.1.val,p.2.val)).1 < o.width w h := by
    rw [congrArg Prod.fst hpoint]
    exact ((o.axis w h).geometry.cells p).1.isLt
  have hpy : (o.point w h (p.1.val,p.2.val)).2 < o.height w h := by
    rw [congrArg Prod.snd hpoint]
    exact ((o.axis w h).geometry.cells p).2.isLt
  have hr := o.inverse.placed_point hx hy (o.point w h (p.1.val,p.2.val)) hpx hpy
  rw [o.inverse_point p,←hq] at hr
  have hg := o.inverse.point_cells W H q
  have hcoords := hg.symm.trans hr
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst hcoords
  · exact congrArg Prod.snd hcoords

end PushPuzzle.PushFS.RectOrientation
