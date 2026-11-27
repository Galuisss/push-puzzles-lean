/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Geometry

/-! Deriving upper-arm bounds from actual track conservation and translating the literal cavity walls. -/

@[expose] public section
namespace PushPuzzle.PushFS


namespace Gadgets.Wires.Soundness.Successful

variable {I : Instance} {Label : Type} [Fintype Label] {M : SlotMatching I Label}
    {S final : LabelledState Label I.width I.height}

/-- A different named junction prevents a physical identity from crossing its upper bound. -/
theorem below_barrier (h : Successful M S final) (A : AxisTracks I) (axis : Bool) (line : ℕ)
    (i : Label) (hi : A.name (M.source i) = lineTag axis line)
    (p : Cell I.width I.height) (hcross : cross axis p = line)
    (hne : A.name p ≠ A.name (M.source i))
    (hstart : coord axis (M.source i) < coord axis p) : coord axis (S.position i) < coord axis p := by
  obtain ⟨hb,ha,hsol⟩ := h
  induction hb with
  | refl => exact hstart
  | @tail U V hr hs ih =>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    have hcoordne : coord axis (V.position i) ≠ coord axis p := by
      intro he
      have ht := (hv.line A axis line i hi).trans hcross.symm
      have hecell : V.position i = p := by
        cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at he ht <;>
          exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))
      exact hv.avoids A i p hne hecell
    have hbound := step_coord_bound hs axis i
    have hh := ih (ha.head hs)
    omega

end Gadgets.Wires.Soundness.Successful

namespace Gadgets.AND.CavityWalls

variable {w h W H : ℕ} {B : Board w h} {ambient : Board W H} {j y : ℕ}

/-- The five literal cavity wall cells retain their actual coordinates under a wall-matching placement. -/
theorem translate (hw : CavityWalls B j y) (hj : j+2 < w) (hy0 : 0 < y) (hy : y+1 < h)
    (dx dy : ℕ) (hx : dx+w ≤ W) (hh : dy+h ≤ H)
    (he : (GridEmbedding.translate dx dy hx hh).WallsAgree B ambient) :
    CavityWalls ambient (dx+j) (dy+y) := by
  have wall (p : Cell W H) (hl : dx+j ≤ p.1.val) (hu : p.1.val ≤ dx+j+2)
      (hp : p.2.val = dy+y+1 ∨ (p.2.val+1=dy+y ∧ (p.1.val=dx+j+1 ∨ p.1.val=dx+j+2))) :
      p ∈ ambient.walls := by
    let q : Cell w h := (⟨p.1.val-dx,by omega⟩,⟨p.2.val-dy,by omega⟩)
    have hq : (GridEmbedding.translate dx dy hx hh).cells q = p := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [q,GridEmbedding.translate] <;> omega
    have hqw : q ∈ B.walls := by
      rcases hp with hp | ⟨hpy,hpx⟩
      · exact hw.below q (by dsimp [q]; omega) (by dsimp [q]; omega) (by dsimp [q]; omega)
      · apply hw.roof q (by dsimp [q]; omega)
        dsimp [q]
        omega
    exact hq ▸ (he q).mpr hqw
  exact ⟨fun p hp hl hu => wall p hl hu (Or.inl hp),
    fun p hp hx => wall p (by omega) (by omega) (Or.inr ⟨hp,hx⟩)⟩

end Gadgets.AND.CavityWalls
end PushPuzzle.PushFS
