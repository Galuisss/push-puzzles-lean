/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPrefix
public import Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramLayout

/-! Whole-row and whole-column target reads leave their matching cleanup clears empty. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- The coordinate prefix requests enumerate exactly the supplied line set. -/
theorem mem_prefixRequests (lanes : Finset ℕ) (span : ℕ → ℕ) (lane n : ℕ) :
    (lane, n) ∈ prefixRequests lanes span ↔ lane ∈ lanes ∧ n = span lane := by
  simp only [prefixRequests, List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, hx, hn⟩
    subst i
    exact ⟨hi, hn.symm⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨lane, hi, rfl, rfl⟩

/-- Reading the whole row from either end touches exactly its complete physical row. -/
theorem readRows_region (p : Scales.Parameters) (side : Direction) (rows : Finset ℕ)
    (hside : side = .west ∨ side = .east) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (readRows p side rows).region ↔ q.2.val ∈ rows := by
  simp only [readRows, Template.region, mem_readRegion]
  have hrank : prefixRank side q < p.W + 1 := by
    rcases hside with rfl | rfl
    · exact q.1.isLt
    · simp only [prefixRank]
      omega
  have hlane : side.lane q = q.2.val := by rcases hside with rfl | rfl <;> rfl
  constructor
  · rintro ⟨request, hrequest, hx, hn⟩
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hrequest
    have hh : i ∈ rows := (Finset.mem_sort _).mp hi
    rw [he.symm, hlane] at hx
    exact hx ▸ hh
  · intro hrow
    refine ⟨(q.2.val, p.W + 1), ?_, hlane, hrank⟩
    exact (mem_prefixRequests rows (fun _ => p.W + 1) _ _).mpr ⟨hrow, rfl⟩

/-- Reading a whole column from either end touches exactly its complete physical column. -/
theorem readColumns_region (p : Scales.Parameters) (side : Direction) (cols : Finset ℕ)
    (hside : side = .north ∨ side = .south) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (readColumns p side cols).region ↔ q.1.val ∈ cols := by
  simp only [readColumns, Template.region, mem_readRegion]
  have hrank : prefixRank side q < p.H + 1 := by
    rcases hside with rfl | rfl
    · exact q.2.isLt
    · simp only [prefixRank]
      omega
  have hlane : side.lane q = q.1.val := by rcases hside with rfl | rfl <;> rfl
  constructor
  · rintro ⟨request, hrequest, hx, hn⟩
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hrequest
    have hh : i ∈ cols := (Finset.mem_sort _).mp hi
    rw [he.symm, hlane] at hx
    exact hx ▸ hh
  · intro hcol
    refine ⟨(q.1.val, p.H + 1), ?_, hlane, hrank⟩
    exact (mem_prefixRequests cols (fun _ => p.H + 1) _ _).mpr ⟨hcol, rfl⟩

/-- A prior full row read leaves a later clear of those rows empty, from either horizontal side. -/
theorem clear_rows_after_read (p : Scales.Parameters) (before : List Template)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (rows : Finset ℕ) (readSide clearSide : Direction)
    (hreadSide : readSide = .west ∨ readSide = .east)
    (hclearSide : clearSide = .west ∨ clearSide = .east)
    (hread : readRows p readSide rows ∈ before) :
    ((emit before E).remaining.filter fun q => clearSide.lane q ∈ rows) = ∅ := by
  apply clear_empty_of_touched
  intro q hq
  have hline := (Finset.mem_filter.mp hq).2
  have hlane : clearSide.lane q = q.2.val := by rcases hclearSide with rfl | rfl <;> rfl
  rw [hlane] at hline
  exact (mem_allRegions before q).mpr ⟨readRows p readSide rows, hread,
    (readRows_region p readSide rows hreadSide q).mpr hline⟩

/-- A prior full column read leaves a later clear of those columns empty, from either vertical side. -/
theorem clear_columns_after_read (p : Scales.Parameters) (before : List Template)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (cols : Finset ℕ) (readSide clearSide : Direction)
    (hreadSide : readSide = .north ∨ readSide = .south)
    (hclearSide : clearSide = .north ∨ clearSide = .south)
    (hread : readColumns p readSide cols ∈ before) :
    ((emit before E).remaining.filter fun q => clearSide.lane q ∈ cols) = ∅ := by
  apply clear_empty_of_touched
  intro q hq
  have hline := (Finset.mem_filter.mp hq).2
  have hlane : clearSide.lane q = q.1.val := by rcases hclearSide with rfl | rfl <;> rfl
  rw [hlane] at hline
  exact (mem_allRegions before q).mpr ⟨readColumns p readSide cols, hread,
    (readColumns_region p readSide cols hreadSide q).mpr hline⟩

/-- Additional requests in the same axis block preserve complete coverage of its ordinary columns. -/
theorem clear_columns_after_combined_read (p : Scales.Parameters) (before : List Template)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (cols : Finset ℕ) (more : List (ℕ × ℕ))
    (hread : Template.read .north (prefixRequests cols (fun _ => p.H + 1) ++ more) ∈ before) :
    ((emit before E).remaining.filter fun q => Direction.north.lane q ∈ cols) = ∅ := by
  apply clear_empty_of_touched
  intro q hq
  have hline : q.1.val ∈ cols := (Finset.mem_filter.mp hq).2
  apply (mem_allRegions before q).mpr
  refine ⟨_, hread, ?_⟩
  rw [Template.region, readRegion_append]
  apply Finset.mem_union_left
  exact (readColumns_region p .north cols (Or.inl rfl) q).mpr hline

end PushPuzzle.Push.AcceptanceProgram
