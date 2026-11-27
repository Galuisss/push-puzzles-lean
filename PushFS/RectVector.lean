/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.RectOrientation

/-! Signed relative coordinates remove the arbitrary long span and physical translation from local glyph seams. -/

@[expose] public section

namespace PushPuzzle.PushFS.RectOrientation

def vector (o : RectOrientation) (v : ℤ×ℤ) : ℤ×ℤ :=
  let u := if o.swapAxes then (v.2,v.1) else v
  (if o.flipX then -u.1 else u.1,if o.flipY then -u.2 else u.2)

def inverseVector (o : RectOrientation) (v : ℤ×ℤ) : ℤ×ℤ :=
  let u := (if o.flipX then -v.1 else v.1,if o.flipY then -v.2 else v.2)
  if o.swapAxes then (u.2,u.1) else u

theorem inverseVector_vector (o : RectOrientation) (v : ℤ×ℤ) : o.inverseVector (o.vector v)=v := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> simp [vector,inverseVector]

theorem vector_inverseVector (o : RectOrientation) (v : ℤ×ℤ) : o.vector (o.inverseVector v)=v := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> simp [vector,inverseVector]

/-- The signed first coordinate of a composed physical orientation is determined by its two unit vectors. -/
theorem composition_x (o f : RectOrientation) (u v : ℤ) :
    (o.inverseVector (f.vector (u,v))).1=
      (o.inverseVector (f.vector (1,0))).1*u+(o.inverseVector (f.vector (0,1))).1*v := by
  rcases o with ⟨s,a,b⟩
  rcases f with ⟨t,c,d⟩
  cases s <;> cases a <;> cases b <;> cases t <;> cases c <;> cases d <;> simp [vector,inverseVector]

/-- The actual eight-way finite-cell isometry has exactly its asserted signed linear action on differences. -/
private theorem point_difference (o : RectOrientation) (w h : ℕ) (p q : Cell w h) :
    (((o.point w h (p.1.val,p.2.val)).1 : ℤ)-(o.point w h (q.1.val,q.2.val)).1,
      ((o.point w h (p.1.val,p.2.val)).2 : ℤ)-(o.point w h (q.1.val,q.2.val)).2)=
      o.vector ((p.1.val : ℤ)-q.1.val,(p.2.val : ℤ)-q.2.val) := by
  have hpX := p.1.isLt
  have hpY := p.2.isLt
  have hqX := q.1.isLt
  have hqY := q.2.isLt
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> apply Prod.ext <;>
    simp [point,width,height,vector] <;> omega

theorem cells_difference (o : RectOrientation) (w h : ℕ) (p q : Cell w h) :
    ((((o.axis w h).geometry.cells p).1.val : ℤ)-((o.axis w h).geometry.cells q).1.val,
      (((o.axis w h).geometry.cells p).2.val : ℤ)-((o.axis w h).geometry.cells q).2.val)=
      o.vector ((p.1.val : ℤ)-q.1.val,(p.2.val : ℤ)-q.2.val) := by
  have hh := o.point_difference w h p q
  rw [o.point_cells,o.point_cells] at hh
  exact hh

end PushPuzzle.PushFS.RectOrientation
