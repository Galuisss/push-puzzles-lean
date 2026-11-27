/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramRegions

/-! Literal coordinate tests for each same-direction acceptance prefix. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS

/-- Zero-based distance from the side where a line read starts. -/
def prefixRank {w h : ℕ} (side : Direction) (q : Cell w h) : ℕ :=
  match side with
  | .north => q.2.val
  | .south => h - 1 - q.2.val
  | .west => q.1.val
  | .east => w - 1 - q.1.val

/-- A line prefix is exactly its lane together with a strict coordinate-rank bound. -/
theorem mem_line_prefix {w h : ℕ} (side : Direction) (lane span : ℕ) (q : Cell w h) :
    q ∈ (Scan.lineCells side lane).take span ↔ side.lane q = lane ∧ prefixRank side q < span := by
  cases side with
  | north =>
    simp only [Scan.lineCells, Direction.lane, prefixRank]
    split
    · simp only [List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn,
        Prod.ext_iff, Fin.ext_iff]
      constructor
      · rintro ⟨i, hi, hx, hy⟩
        exact ⟨hx.symm, by omega⟩
      · rintro ⟨hx, hy⟩
        exact ⟨q.2.val, by have := q.2.isLt; omega, hx.symm, rfl⟩
    · simp only [List.take_nil, List.not_mem_nil, false_iff]
      intro hh
      have := q.1.isLt
      omega
  | south =>
    simp only [Scan.lineCells, Direction.lane, prefixRank]
    split
    · simp only [List.mem_take_iff_getElem, List.length_reverse, List.length_ofFn,
        List.getElem_reverse, List.getElem_ofFn, Prod.ext_iff, Fin.ext_iff]
      constructor
      · rintro ⟨i, hi, hx, hy⟩
        exact ⟨hx.symm, by have := q.2.isLt; omega⟩
      · rintro ⟨hx, hy⟩
        refine ⟨h - 1 - q.2.val, by have := q.2.isLt; omega, hx.symm, ?_⟩
        have := q.2.isLt
        omega
    · simp only [List.take_nil, List.not_mem_nil, false_iff]
      intro hh
      have := q.1.isLt
      omega
  | west =>
    simp only [Scan.lineCells, Direction.lane, prefixRank]
    split
    · simp only [List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn,
        Prod.ext_iff, Fin.ext_iff]
      constructor
      · rintro ⟨i, hi, hx, hy⟩
        exact ⟨hy.symm, by omega⟩
      · rintro ⟨hx, hy⟩
        exact ⟨q.1.val, by have := q.1.isLt; omega, rfl, hx.symm⟩
    · simp only [List.take_nil, List.not_mem_nil, false_iff]
      intro hh
      have := q.2.isLt
      omega
  | east =>
    simp only [Scan.lineCells, Direction.lane, prefixRank]
    split
    · simp only [List.mem_take_iff_getElem, List.length_reverse, List.length_ofFn,
        List.getElem_reverse, List.getElem_ofFn, Prod.ext_iff, Fin.ext_iff]
      constructor
      · rintro ⟨i, hi, hx, hy⟩
        exact ⟨hy.symm, by have := q.1.isLt; omega⟩
      · rintro ⟨hx, hy⟩
        refine ⟨w - 1 - q.1.val, by have := q.1.isLt; omega, ?_, hx.symm⟩
        have := q.1.isLt
        omega
    · simp only [List.take_nil, List.not_mem_nil, false_iff]
      intro hh
      have := q.2.isLt
      omega

/-- Membership in the read region is an explicit bounded search over the emitted line requests. -/
theorem mem_readRegion {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ)) (q : Cell w h) :
    q ∈ readRegion side requests ↔ ∃ request ∈ requests,
      side.lane q = request.1 ∧ prefixRank side q < request.2 := by
  induction requests with
  | nil => simp only [readRegion, Finset.notMem_empty, List.not_mem_nil, false_and, exists_false, iff_self]
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    simp only [readRegion, Finset.mem_union, List.mem_toFinset, mem_line_prefix, ih,
      List.mem_cons, exists_eq_or_imp]

end PushPuzzle.Push.AcceptanceProgram
