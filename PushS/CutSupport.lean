/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.RelativeSupport

/-! Sparse street supports whose vertical components end at central blocking holes. -/

@[expose] public section
namespace PushPuzzle.PushS.Support

open PushFS

variable {w h : ℕ}

/-- Sparse rows and vertical street components closed under clear vertical adjacency. -/
structure CutStreetSystem (G : Finset (Cell w h)) where
  columns : Set (Fin w)
  rows : Set (Fin h)
  vertical : Set (Cell w h)
  columns_separated : Separated columns
  rows_separated : Separated rows
  vertical_columns : ∀ p ∈ vertical, p.1 ∈ columns
  vertical_closed : ∀ d, d = .north ∨ d = .south → ∀ p q,
    Adjacent d p q → p ∈ vertical → p ∉ G → q ∉ G → q ∈ vertical

namespace CutStreetSystem
variable {G : Finset (Cell w h)} (A : CutStreetSystem G)

/-- Full horizontal streets together with the selected vertical components. -/
def support : Set (Cell w h) := {p | p.2 ∈ A.rows ∨ p ∈ A.vertical}

private theorem straight_lane {d : Direction} {p q : Cell w h}
    (hr : StraightReach G d p q) : d.lane q = d.lane p := by
  induction hr with
  | refl => rfl
  | tail _ hm ih => exact hm.1.lane.trans ih

private theorem horizontal_row {p q : Cell w h}
    (hp : p ∈ A.support) (hq : q ∈ A.support)
    (hy : q.2 = p.2) (hx : p.1.val + 1 = q.1.val) : p.2 ∈ A.rows := by
  rcases hp with hp | hp
  · exact hp
  · rcases hq with hq | hq
    · exact hy ▸ hq
    · exact False.elim (A.columns_separated (A.vertical_columns p hp)
        (A.vertical_columns q hq) hx)

private theorem vertical_start {d : Direction} (hd : d = .north ∨ d = .south)
    {p q : Cell w h} (ha : Adjacent d p q) (hp : p ∈ A.support) (hq : q ∈ A.support)
    (hGp : p ∉ G) (hGq : q ∉ G) : p ∈ A.vertical := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · rcases hd with rfl | rfl
      · exact False.elim (A.rows_separated hq hp ha.2)
      · exact False.elim (A.rows_separated hp hq ha.2.symm)
    · have hop : d.opposite = .north ∨ d.opposite = .south := by
        rcases hd with rfl | rfl <;> simp [Direction.opposite]
      exact A.vertical_closed d.opposite hop q p ha.reverse hq hGq hGp
  · exact hp

private theorem straight_vertical {d : Direction} (hd : d = .north ∨ d = .south)
    {p q : Cell w h} (hr : StraightReach G d p q) (hp : p ∈ A.vertical) :
    q ∈ A.vertical := by
  induction hr with
  | refl => exact hp
  | tail _ hm ih => exact A.vertical_closed d hd _ _ hm.1 ih hm.2.1 hm.2.2

/-- Clear straight rays preserve the cut street support. -/
private theorem relativeClosed : RelativeClosed A.support G := by
  intro d p q ha hp hq hGp hGq r hr
  have hl := straight_lane hr
  cases d with
  | north =>
    exact Or.inr (A.straight_vertical (Or.inl rfl) hr
      (A.vertical_start (Or.inl rfl) ha hp hq hGp hGq))
  | east =>
    have hy := A.horizontal_row hp hq ha.2 ha.1.symm
    exact Or.inl ((Fin.ext hl) ▸ hy)
  | south =>
    exact Or.inr (A.straight_vertical (Or.inr rfl) hr
      (A.vertical_start (Or.inr rfl) ha hp hq hGp hGq))
  | west =>
    have hy := A.horizontal_row hq hp ha.2.symm ha.1
    exact Or.inl ((Fin.ext hl) ▸ (ha.2 ▸ hy))

end CutStreetSystem

/-- Two-page street data with common main axes and sparse selected coordinates. -/
structure TwoPageStreets (w h : ℕ) where
  cut : Fin h
  top : Set (Fin w)
  bottom : Set (Fin w)
  main : Set (Fin w)
  rows : Set (Fin h)
  main_top : main ⊆ top
  main_bottom : main ⊆ bottom
  columns_separated : Separated (top ∪ bottom)
  rows_separated : Separated rows

namespace TwoPageStreets
variable (P : TwoPageStreets w h)

/-- All auxiliary columns have a blocking hole on the central cut. -/
noncomputable def blockers : Finset (Cell w h) := by
  classical
  exact Finset.univ.filter fun p => p.2 = P.cut ∧ p.1 ∈ P.top ∪ P.bottom ∧ p.1 ∉ P.main

theorem mem_blockers (p : Cell w h) :
    p ∈ P.blockers ↔ p.2 = P.cut ∧ p.1 ∈ P.top ∪ P.bottom ∧ p.1 ∉ P.main := by
  classical
  simp [blockers]

/-- Main axes cross the cut; each other column has only its specified page portions. -/
def vertical : Set (Cell w h) :=
  {p | p.1 ∈ P.main ∨ (p.1 ∈ P.top ∧ p.2.val ≤ P.cut.val) ∨
    (p.1 ∈ P.bottom ∧ P.cut.val ≤ p.2.val)}

/-- The two physical pages instantiate a street system with central blockers. -/
noncomputable def system : CutStreetSystem P.blockers where
  columns := P.top ∪ P.bottom
  rows := P.rows
  vertical := P.vertical
  columns_separated := P.columns_separated
  rows_separated := P.rows_separated
  vertical_columns p hp := by
    rcases hp with hp | hp | hp
    · exact Or.inl (P.main_top hp)
    · exact Or.inl hp.1
    · exact Or.inr hp.1
  vertical_closed d hd p q ha hp hGp _ := by
    have hx : q.1 = p.1 := by rcases hd with rfl | rfl <;> exact ha.1
    rcases hp with hp | ⟨hxT, hyT⟩ | ⟨hxB, hyB⟩
    · exact Or.inl (hx ▸ hp)
    · by_cases hm : p.1 ∈ P.main
      · exact Or.inl (hx ▸ hm)
      have hpcut : p.2.val ≠ P.cut.val := by
        intro he
        exact hGp ((P.mem_blockers p).mpr ⟨Fin.ext he, Or.inl hxT, hm⟩)
      refine Or.inr (Or.inl ⟨hx ▸ hxT, ?_⟩)
      rcases hd with rfl | rfl <;> simp only [Adjacent] at ha <;> omega
    · by_cases hm : p.1 ∈ P.main
      · exact Or.inl (hx ▸ hm)
      have hpcut : p.2.val ≠ P.cut.val := by
        intro he
        exact hGp ((P.mem_blockers p).mpr ⟨Fin.ext he, Or.inr hxB, hm⟩)
      refine Or.inr (Or.inr ⟨hx ▸ hxB, ?_⟩)
      rcases hd with rfl | rfl <;> simp only [Adjacent] at ha <;> omega

/-- The coordinate support used for the two pages. -/
def support : Set (Cell w h) := {p | p.2 ∈ P.rows ∨ p ∈ P.vertical}

/-- Central auxiliary holes separate both pages in the reverse support argument. -/
theorem relativeClosed : RelativeClosed P.support P.blockers := P.system.relativeClosed

end TwoPageStreets
end PushPuzzle.PushS.Support
