/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineReadout

/-! Literal two-sided obstructions of every emitted flip and parity atom. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Readout

open PushFS PushFS.Gadgets.Wires.Soundness
open FiniteTools (radius paritySpan)
open FiniteGeometry (Rectangle)

private theorem own_wall (w : ℕ) (pre post : List Atom) (a : Atom) (above : Bool) (r : Rectangle)
    (hr : r ∈ a.rectangles w (span w pre) (exitSide above pre))
    (p : Cell (width w (pre++a::post)) (height w)) (hp : p ∈ r.cells _ _) : p ∈ Line.walls w (pre++a::post) above := by
  apply Finset.mem_biUnion.mpr
  refine ⟨r, List.mem_toFinset.mpr ?_, hp⟩
  rw [rectangles_split]
  apply List.mem_append_right
  simp only [Nat.zero_add, rectangles]
  exact List.mem_append_left _ hr

attribute [local irreducible] width height

theorem flip_strips (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (above : Bool) :
    StripWalls (⟨Line.walls w (pre++ .flip::post) above,∅⟩ : Board (width w (pre++ .flip::post)) (height w))
      (radius w+span w pre+2) (radius w+span w pre+w) (radius w) ∧
    StripWalls (⟨Line.walls w (pre++ .flip::post) above,∅⟩ : Board (width w (pre++ .flip::post)) (height w))
      (radius w+span w pre+w+3) (radius w+span w pre+2*w+1) (radius w) := by
  constructor
  · constructor
    · intro p hy hx hx'
      apply own_wall w pre post .flip above
        ⟨if exitSide above pre then radius w+span w pre+2 else radius w+span w pre,
          radius w+1, if exitSide above pre then w else w+1,w⟩
      · cases hs : exitSide above pre <;> simp [Atom.rectangles]
      · apply (Rectangle.mem_cells _ _ _ _).mpr
        cases hs : exitSide above pre <;> simp <;> omega
    · intro p hy hx hx'
      apply own_wall w pre post .flip above
        ⟨if exitSide above pre then radius w+span w pre else radius w+span w pre+2,
          radius w-w, if exitSide above pre then w+1 else w,w⟩
      · cases hs : exitSide above pre <;> simp [Atom.rectangles]
      · apply (Rectangle.mem_cells _ _ _ _).mpr
        cases hs : exitSide above pre <;> simp <;> unfold radius at * <;> omega
  · constructor
    · intro p hy hx hx'
      apply own_wall w pre post .flip above
        ⟨if exitSide above pre then radius w+span w pre+w+3 else radius w+span w pre+w+2,
          radius w+1, if exitSide above pre then w+1 else w,w⟩
      · cases hs : exitSide above pre <;> simp [Atom.rectangles]
      · apply (Rectangle.mem_cells _ _ _ _).mpr
        cases hs : exitSide above pre <;> simp <;> omega
    · intro p hy hx hx'
      apply own_wall w pre post .flip above
        ⟨if exitSide above pre then radius w+span w pre+w+2 else radius w+span w pre+w+3,
          radius w-w, if exitSide above pre then w else w+1,w⟩
      · cases hs : exitSide above pre <;> simp [Atom.rectangles]
      · apply (Rectangle.mem_cells _ _ _ _).mpr
        cases hs : exitSide above pre <;> simp <;> unfold radius at * <;> omega

theorem parity_strip (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (above : Bool) :
    StripWalls (⟨Line.walls w (pre++ .parity::post) above,∅⟩ : Board (width w (pre++ .parity::post)) (height w))
      (radius w+span w pre+2) (radius w+span w pre+paritySpan w+1) (radius w) := by
  have hm := FiniteTools.paritySpan_bounds w
  constructor
  · intro p hy hx hx'
    apply own_wall w pre post .parity above
      ⟨if exitSide above pre then radius w+span w pre+2 else radius w+span w pre,
        radius w+1, if exitSide above pre then paritySpan w else paritySpan w+4,w⟩
    · cases hs : exitSide above pre <;> simp [Atom.rectangles]
    · apply (Rectangle.mem_cells _ _ _ _).mpr
      cases hs : exitSide above pre <;> simp <;> omega
  · intro p hy hx hx'
    apply own_wall w pre post .parity above
      ⟨if exitSide above pre then radius w+span w pre else radius w+span w pre+2,
        radius w-w, if exitSide above pre then paritySpan w+4 else paritySpan w,w⟩
    · cases hs : exitSide above pre <;> simp [Atom.rectangles]
    · apply (Rectangle.mem_cells _ _ _ _).mpr
      cases hs : exitSide above pre <;> simp <;> unfold radius at * <;> omega

end PushPuzzle.PushS.FiniteRouting.Line.Readout
