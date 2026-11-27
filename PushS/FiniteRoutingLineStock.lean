/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineIndices
public import PushS.FiniteLineMacros

/-! Actual exposed walking faces of ordinary stock between neighboring thick tools. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

def Exposed (w : ℕ) (above : Bool) (y : ℕ) : Prop :=
  if above then FiniteTools.radius w ≤ y else y ≤ FiniteTools.radius w

private theorem Atom.span_ge_four (w : ℕ) (hw : 2 ≤ w) (a : Atom)
    (ha : a.Valid w) : 4 ≤ a.span w := by
  have hm := FiniteTools.paritySpan_bounds w
  cases a <;> dsimp [Atom.Valid, Atom.span, buffer] at * <;> omega

private theorem span_ge_four (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (ha : ∀ a ∈ atoms, a.Valid w) : 4 ≤ span w atoms := by
  cases atoms with
  | nil => contradiction
  | cons a atoms =>
    have hh := a.span_ge_four w hw (ha a (by simp))
    simp only [span_cons]
    omega

private theorem Atom.left_face_floor {W H : ℕ} (w : ℕ) (hw : 2 ≤ w) (offset : ℕ) (above : Bool)
    (a : Atom)
    {r : Rectangle} (hr : r ∈ a.rectangles w offset above) (p : Cell W H)
    (hx : p.1.val ≤ FiniteTools.radius w+offset) (hy : Exposed w above p.2.val) :
    p ∉ r.cells W H := by
  have hrad : w ≤ FiniteTools.radius w := by unfold FiniteTools.radius; omega
  intro hp
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  cases above <;> cases a <;> simp [Atom.rectangles] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;>
    simp [Exposed] at hy <;> dsimp at hp' <;> omega

private theorem Atom.right_face_floor {W H : ℕ} (w : ℕ) (hw : 2 ≤ w) (offset : ℕ) (above : Bool)
    (a : Atom)
    {r : Rectangle} (hr : r ∈ a.rectangles w offset above) (p : Cell W H)
    (hx : FiniteTools.radius w+offset+a.span w+1 ≤ p.1.val)
    (hy : Exposed w (a.nextSide above) p.2.val) : p ∉ r.cells W H := by
  have hrad : w ≤ FiniteTools.radius w := by unfold FiniteTools.radius; omega
  intro hp
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  cases above <;> cases a <;> simp [Atom.rectangles] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;>
    simp [Exposed, Atom.nextSide] at hy <;> dsimp [Atom.span] at hx hp' <;> omega

theorem right_face_floor {W H : ℕ} (w : ℕ) (hw : 2 ≤ w) (offset : ℕ) (above : Bool)
    (atoms : List Atom) (ha : ∀ a ∈ atoms, a.Valid w) {r : Rectangle}
    (hr : r ∈ rectangles w offset above atoms) (p : Cell W H)
    (hx : FiniteTools.radius w+offset+span w atoms+1 ≤ p.1.val)
    (hy : Exposed w (exitSide above atoms) p.2.val) : p ∉ r.cells W H := by
  induction atoms generalizing offset above with
  | nil => simp [rectangles] at hr
  | cons a atoms ih =>
    rcases List.mem_append.mp hr with hr | hr
    · by_cases hn : atoms = []
      · subst atoms
        exact a.right_face_floor w hw offset above (by simpa only [rectangles, List.append_nil] using hr)
          p (by simpa only [span_cons, span_nil, Nat.add_zero] using hx) hy
      · have hb := a.rectangles_bounds w offset above hr
        have hs := span_ge_four w hw atoms hn (fun b hb => ha b (by simp [hb]))
        intro hp
        have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
        simp only [span_cons] at hx
        omega
    · exact ih (offset+a.span w) (a.nextSide above) (fun b hb => ha b (by simp [hb])) hr
        (by simp only [span_cons] at hx; omega) hy

private theorem left_face_floor {W H : ℕ} (w : ℕ) (hw : 2 ≤ w) (offset : ℕ) (above : Bool)
    (atoms : List Atom) (ha : ∀ a ∈ atoms, a.Valid w) {r : Rectangle}
    (hr : r ∈ rectangles w offset above atoms) (p : Cell W H)
    (hx : p.1.val ≤ FiniteTools.radius w+offset) (hy : Exposed w above p.2.val) : p ∉ r.cells W H := by
  cases atoms with
  | nil => simp [rectangles] at hr
  | cons a atoms =>
    rcases List.mem_append.mp hr with hr | hr
    · exact a.left_face_floor w hw offset above hr p hx hy
    · have hs := a.span_ge_four w hw (ha a (by simp))
      have hb := rectangles_bounds w (offset+a.span w) (a.nextSide above) atoms hr
      intro hp
      have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
      omega

/-- Every point on the ordinary stock's exposed face stays clear of both neighboring tool collars. -/
theorem stock_face_floor (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (above : Bool) (n : ℕ)
    (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (p : Cell (width w (pre++ .line n::post)) (height w))
    (hx : FiniteTools.radius w+span w pre+1 ≤ p.1.val)
    (hx' : p.1.val ≤ FiniteTools.radius w+span w pre+2*n)
    (hy : Exposed w (exitSide above pre) p.2.val) : p ∉ walls w (pre++ .line n::post) above := by
  have hrad : w ≤ FiniteTools.radius w := by unfold FiniteTools.radius; omega
  intro hp
  obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
  have hr' := List.mem_toFinset.mp hr
  rw [rectangles_split] at hr'
  rcases List.mem_append.mp hr' with hpre | hrest
  · exact right_face_floor w hw 0 above pre (fun a h => ha a (List.mem_append_left _ h)) hpre p (by omega) hy hp
  · simp only [rectangles, Atom.nextSide, Atom.span, Nat.zero_add] at hrest
    rcases List.mem_append.mp hrest with hline | hpost
    · have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
      cases hs : exitSide above pre <;> simp [Atom.rectangles, hs] at hline <;>
        rcases hline with rfl <;> simp [Exposed, hs] at hy <;> dsimp at hp' <;> omega
    · exact left_face_floor w hw (span w pre+2*n) (exitSide above pre) post
        (fun a h => ha a (List.mem_append_right _ (List.mem_cons_of_mem _ h))) hpost p (by omega) hy hp

end PushPuzzle.PushS.FiniteRouting.Line
