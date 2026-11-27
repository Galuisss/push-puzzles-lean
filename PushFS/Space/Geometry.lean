/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! Unary raw coordinates, bounded cell enumeration and directional adjacency. -/

@[expose] public section

namespace PushPuzzle.PushFS.Machine


open Turing.MultiTapeTM ComputableInPolyTime

abbrev RawCell := ℕ × ℕ
abbrev encRawCell : RawCell ↪ List Bool := encPair encUnary encUnary

/-- All coordinates of a rectangle, in row-major order. -/
def cells (size : ℕ × ℕ) : List RawCell :=
  ((List.range size.2).map fun y => (List.range size.1).map fun x => (x, y)).flatten

@[fun_prop] theorem cells_polyTime :
    ComputableInPolyTime cells encRawCell (encList encRawCell) := by
  unfold cells
  apply (flatten encRawCell).comp
  apply mapWithInput
  · fun_prop
  · apply mapWithInput
    · fun_prop
    · fun_prop

/-- Membership in the enumeration is exactly the two bounds checks. -/
private theorem mem_cells (size p : ℕ × ℕ) : p ∈ cells size ↔ p.1 < size.1 ∧ p.2 < size.2 := by
  rcases p with ⟨x, y⟩
  simp [cells, List.mem_flatten, List.mem_map, List.mem_range, and_comm]

/-- Strip the proof fields of an actual board coordinate. -/
def rawCell {w h : ℕ} (p : Cell w h) : RawCell := (p.1.val, p.2.val)

@[simp] theorem rawCell_mem_cells {w h : ℕ} (p : Cell w h) : rawCell p ∈ cells (w, h) :=
  (mem_cells _ _).mpr ⟨p.1.isLt, p.2.isLt⟩

/-- Every enumerated raw coordinate is a genuine bounded cell. -/
private theorem mem_cells_iff {w h : ℕ} (p : RawCell) :
    p ∈ cells (w, h) ↔ ∃ q : Cell w h, rawCell q = p := by
  constructor
  · intro hp
    obtain ⟨hx, hy⟩ := (mem_cells _ _).mp hp
    exact ⟨(⟨p.1, hx⟩, ⟨p.2, hy⟩), rfl⟩
  · rintro ⟨q, rfl⟩
    exact rawCell_mem_cells q

theorem forall_cells_iff {w h : ℕ} (P : RawCell → Prop) :
    (∀ p ∈ cells (w, h), P p) ↔ ∀ q : Cell w h, P (rawCell q) := by
  constructor
  · intro hP q
    exact hP _ (rawCell_mem_cells q)
  · intro hP p hp
    obtain ⟨q, rfl⟩ := (mem_cells_iff p).mp hp
    exact hP q

theorem exists_cells_iff {w h : ℕ} (P : RawCell → Prop) :
    (∃ p ∈ cells (w, h), P p) ↔ ∃ q : Cell w h, P (rawCell q) := by
  constructor
  · rintro ⟨p, hp, hP⟩
    obtain ⟨q, rfl⟩ := (mem_cells_iff p).mp hp
    exact ⟨q, hP⟩
  · rintro ⟨q, hP⟩
    exact ⟨_, rawCell_mem_cells q, hP⟩

/-- Row-major address in the box or player bitmap. -/
def index (p : ℕ × RawCell) : ℕ := p.2.2 * p.1 + p.2.1

@[fun_prop] theorem index_polyTime :
    ComputableInPolyTime index (encPair encUnary encRawCell) encUnary := by
  unfold index
  fun_prop

/-- The arithmetic address is the exact inverse index used by the state codec. -/
theorem index_eq {w h : ℕ} (p : Cell w h) :
    index (w, rawCell p) = (finProdFinEquiv p.swap).val := by
  simp [index, rawCell, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- Adjacency of raw coordinates; the surrounding enumerator enforces bounds. -/
def adjacent (p : Direction × RawCell × RawCell) : Bool :=
  if p.1 == .north then (p.2.2.1 == p.2.1.1) && (p.2.2.2 + 1 == p.2.1.2)
  else if p.1 == .east then (p.2.2.1 == p.2.1.1 + 1) && (p.2.2.2 == p.2.1.2)
  else if p.1 == .south then (p.2.2.1 == p.2.1.1) && (p.2.2.2 == p.2.1.2 + 1)
  else (p.2.2.1 + 1 == p.2.1.1) && (p.2.2.2 == p.2.1.2)

@[fun_prop] theorem adjacent_polyTime :
    ComputableInPolyTime adjacent
      (encPair (encFinite Direction) (encPair encRawCell encRawCell)) encBool := by
  unfold adjacent
  have hn : ComputableInPolyTime (fun d : Direction => d == .north)
      (encFinite Direction) encBool := of_finite _
  have he : ComputableInPolyTime (fun d : Direction => d == .east)
      (encFinite Direction) encBool := of_finite _
  have hs : ComputableInPolyTime (fun d : Direction => d == .south)
      (encFinite Direction) encBool := of_finite _
  fun_prop

/-- The raw test and the logical grid relation agree in every direction. -/
theorem adjacent_correct {w h : ℕ} (d : Direction) (p q : Cell w h) :
    adjacent (d, rawCell p, rawCell q) = true ↔ Adjacent d p q := by
  cases d <;> simp [adjacent, rawCell, Adjacent, Fin.ext_iff]

end PushPuzzle.PushFS.Machine
