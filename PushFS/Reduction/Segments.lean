/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Bitmap
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridPath

/-!
# Explicit finite data for orthogonal paths

Segment lists serialize the upstream geometric paths without changing their
trace. Their integer cells are generated in polynomial time under unary
coordinate encodings, ready for selecting physical wire tiles.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Turing.MultiTapeTM ComputableInPolyTime

/-- One closed axis-aligned lattice segment. -/
structure Segment where
  /-- First endpoint. -/
  start : ℕ × ℕ
  /-- Last endpoint. -/
  finish : ℕ × ℕ
  deriving DecidableEq

/-- Two unary coordinate pairs in endpoint order. -/
enc_structure encSegment : Segment where
  start : Bitmap.encPoint, finish : Bitmap.encPoint

/-- Lattice points of a horizontal or vertical closed segment. -/
def Segment.Contains (s : Segment) (p : ℕ × ℕ) : Prop :=
  (s.start.1 = s.finish.1 ∧ p.1 = s.start.1 ∧
    min s.start.2 s.finish.2 ≤ p.2 ∧ p.2 ≤ max s.start.2 s.finish.2) ∨
  (s.start.2 = s.finish.2 ∧ p.2 = s.start.2 ∧
    min s.start.1 s.finish.1 ≤ p.1 ∧ p.1 ≤ max s.start.1 s.finish.1)

/-- Enumerate each represented cell, choosing the horizontal convention at a point segment. -/
def Segment.cells (s : Segment) : List (ℕ × ℕ) :=
  if s.start.2 = s.finish.2 then
    (List.range (max s.start.1 s.finish.1 - min s.start.1 s.finish.1 + 1)).map
      fun i => (min s.start.1 s.finish.1 + i, s.start.2)
  else if s.start.1 = s.finish.1 then
    (List.range (max s.start.2 s.finish.2 - min s.start.2 s.finish.2 + 1)).map
      fun i => (s.start.1, min s.start.2 s.finish.2 + i)
  else []

/-- The finite enumeration contains exactly the integer segment trace. -/
theorem Segment.mem_cells (s : Segment) (p : ℕ × ℕ) : p ∈ s.cells ↔ s.Contains p := by
  rcases s with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  rcases p with ⟨px, py⟩
  simp only [Segment.cells, Segment.Contains]
  split_ifs with hy hx
  · subst y'
    have hbounds : min x x' ≤ max x x' := min_le_max
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi, rfl, rfl⟩
      exact Or.inr ⟨True.intro, rfl, Nat.le_add_right _ _, by omega⟩
    · intro hp
      have hh : py = y ∧ min x x' ≤ px ∧ px ≤ max x x' := by omega
      exact ⟨px - min x x', by omega, by omega, hh.1.symm⟩
  · subst x'
    have hbounds : min y y' ≤ max y y' := min_le_max
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi, rfl, rfl⟩
      exact Or.inl ⟨True.intro, rfl, Nat.le_add_right _ _, by omega⟩
    · intro hp
      have hh : px = x ∧ min y y' ≤ py ∧ py ≤ max y y' := by omega
      exact ⟨py - min y y', by omega, hh.1.symm, by omega⟩
  · simp [hy, hx]

/-- Serialize every actual segment of an upstream finite orthogonal path. -/
def segments {p q : NCL.GridRouting.Point} : NCL.GridRouting.Path p q → List Segment
  | .horizontal x x' y => [⟨(x, y), (x', y)⟩]
  | .vertical x y y' _ => [⟨(x, y), (x, y')⟩]
  | .comp r s => segments r ++ segments s

/-- Serialization preserves the complete path trace, including endpoints and joins. -/
theorem mem_segments_iff {p q : NCL.GridRouting.Point} (r : NCL.GridRouting.Path p q)
    (u : NCL.GridRouting.Point) : (∃ s ∈ segments r, s.Contains u) ↔ r.Contains u := by
  induction r with
  | horizontal x x' y =>
    simp only [segments, List.mem_singleton, exists_eq_left, Segment.Contains,
      NCL.GridRouting.Path.Contains, Nat.min_self, Nat.max_self, true_and]
    constructor
    · rintro (⟨he, hx, hlo, hhi⟩ | hu)
      · subst x'
        simp only [Nat.min_self, Nat.max_self]
        omega
      · exact hu
    · exact Or.inr
  | vertical x y y' hy =>
    simp only [segments, List.mem_singleton, exists_eq_left, Segment.Contains,
      NCL.GridRouting.Path.Contains, Nat.min_self, Nat.max_self, true_and,
      Nat.min_eq_left hy, Nat.max_eq_right hy]
    omega
  | comp r s ihr ihs =>
    simp only [segments, List.mem_append, or_and_right, exists_or, ihr, ihs,
      NCL.GridRouting.Path.Contains]

@[fun_prop] theorem Segment.cells_polyTime :
    ComputableInPolyTime Segment.cells encSegment (encList Bitmap.encPoint) := by
  unfold Segment.cells Bitmap.encPoint
  fun_prop

end PushPuzzle.PushFS.Reduction
