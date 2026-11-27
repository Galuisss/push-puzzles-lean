/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.RectVector

/-! Coincident actual placed cells and anchors give exact local signed seam equations. -/

@[expose] public section

namespace PushPuzzle.PushFS.RectOrientation


def coordinates (o : RectOrientation) (w h dx dy : ℕ) (p : Cell w h) : ℕ×ℕ :=
  (dx+((o.axis w h).geometry.cells p).1.val,dy+((o.axis w h).geometry.cells p).2.val)

theorem coordinates_point (o : RectOrientation) (w h dx dy : ℕ) (p : Cell w h) :
    o.coordinates w h dx dy p=
      (dx+(o.point w h (p.1.val,p.2.val)).1,dy+(o.point w h (p.1.val,p.2.val)).2) := by
  rw [o.point_cells]
  rfl

/-- Equal global cells at a shared real seam anchor preserve both complete local relative vectors. -/
private theorem placed_relative {w h v z : ℕ} (o f : RectOrientation) (dx dy ex ey : ℕ)
    (p a : Cell w h) (q b : Cell v z)
    (hp : o.coordinates w h dx dy p=f.coordinates v z ex ey q)
    (ha : o.coordinates w h dx dy a=f.coordinates v z ex ey b) :
    o.vector ((p.1.val : ℤ)-a.1.val,(p.2.val : ℤ)-a.2.val)=
      f.vector ((q.1.val : ℤ)-b.1.val,(q.2.val : ℤ)-b.2.val) := by
  rw [← o.cells_difference w h p a,← f.cells_difference v z q b]
  have hpX := congrArg Prod.fst hp
  have hpY := congrArg Prod.snd hp
  have haX := congrArg Prod.fst ha
  have haY := congrArg Prod.snd ha
  dsimp only [coordinates] at hpX hpY haX haY
  apply Prod.ext <;> dsimp only <;> omega

theorem placed_inverse_relative {w h v z : ℕ} (o f : RectOrientation) (dx dy ex ey : ℕ)
    (p a : Cell w h) (q b : Cell v z)
    (hp : o.coordinates w h dx dy p=f.coordinates v z ex ey q)
    (ha : o.coordinates w h dx dy a=f.coordinates v z ex ey b) :
    o.inverseVector (f.vector ((q.1.val : ℤ)-b.1.val,(q.2.val : ℤ)-b.2.val))=
      ((p.1.val : ℤ)-a.1.val,(p.2.val : ℤ)-a.2.val) := by
  have hh := congrArg o.inverseVector (o.placed_relative f dx dy ex ey p a q b hp ha)
  rw [o.inverseVector_vector] at hh
  exact hh.symm

/-- Solve a relative seam equation in literal raw local coordinates. -/
theorem solve_relative (o f : RectOrientation) (p a v : ℤ×ℤ)
    (h : o.inverseVector (f.vector (p.1-a.1,p.2-a.2))=v) :
    p=(a.1+(f.inverseVector (o.vector v)).1,a.2+(f.inverseVector (o.vector v)).2) := by
  have hh := congrArg f.inverseVector (congrArg o.vector h)
  rw [o.vector_inverseVector,f.inverseVector_vector] at hh
  have hx := congrArg Prod.fst hh
  have hy := congrArg Prod.snd hh
  apply Prod.ext <;> dsimp only at hx hy ⊢ <;> omega

end PushPuzzle.PushFS.RectOrientation
