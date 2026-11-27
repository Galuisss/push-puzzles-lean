/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortSegments
public import PushS.PortLayoutCoordinates
public import PushS.Support
import all PushS.PortSegments

/-!
# Sparse streets of the actual port emitter

Original vertical streets and all working rows, reflected onto both pages and including the
frame, have even coordinates. The working rows include the depth-minus-two rows emitted when
there are no three-port centers. These actual coordinate sets satisfy sparse-street separation.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual emitted original-street coordinate list. -/
def streetColumnCoordinates (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  streetColumns l (coordinates p)

/-- The actual selected depth list, including depth-minus-two when there are no gate centers. -/
def workingDepthCoordinates (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  workingRows l (coordinates p)

/-- The emitter's original complete street-row list. -/
def streetRowCoordinates (p : Scales.Parameters) : List ℕ := streetRows (coordinates p)

/-- Original vertical street columns of the actual emitter, including both side frames. -/
@[expose] def streetColumnSet (l : PortLayout) (p : Scales.Parameters) : Set (Fin (p.W + 1)) :=
  {x | x.val ∈ streetColumnCoordinates l p}

/-- Both frame rows and both page reflections of every actual selected working row. -/
@[expose] def workingRowSet (l : PortLayout) (p : Scales.Parameters) : Set (Fin (p.H + 1)) :=
  {y | y.val ∈ [0, p.H] ++ (workingDepthCoordinates l p).flatMap (fun v => [v, p.H - v])}

/-- Membership reads the emitter's original vertical-street list. -/
theorem streetColumnSet_iff (l : PortLayout) (p : Scales.Parameters) (x : Fin (p.W + 1)) :
    x ∈ streetColumnSet l p ↔ x.val ∈ streetColumnCoordinates l p := Iff.rfl

/-- Membership reads the actual working-row list on either page, together with the frame. -/
theorem workingRowSet_iff (l : PortLayout) (p : Scales.Parameters) (y : Fin (p.H + 1)) :
    y ∈ workingRowSet l p ↔ y.val = 0 ∨ y.val = p.H ∨
      ∃ v ∈ workingDepthCoordinates l p, y.val = v ∨ y.val = p.H - v := by
  simp [workingRowSet, List.mem_flatMap]

/-- Every emitted selected working row belongs to the support set on either physical page. -/
theorem mem_workingRowSet_of_onSide (l : PortLayout) (p : Scales.Parameters) {v : ℕ}
    (hv : v ∈ workingDepthCoordinates l p) (side : Side) (y : Fin (p.H + 1))
    (hy : y.val = if side = .upper then v else p.H - v) : y ∈ workingRowSet l p := by
  apply (workingRowSet_iff l p y).mpr
  refine Or.inr (Or.inr ⟨v, hv, ?_⟩)
  cases side with
  | upper => exact Or.inl hy
  | lower => exact Or.inr hy

/-- Each allocated level contributes its work row and its depth-plus-two branch row. -/
theorem workingDepthCoordinates_mem (l : PortLayout) (p : Scales.Parameters) (j : ℕ)
    (hj : j < p.levels) : readDepth p (j + 1) ∈ workingDepthCoordinates l p ∧
      readDepth p (j + 1) + 2 ∈ workingDepthCoordinates l p := by
  constructor
  all_goals
    change _ ∈ workingRows l (coordinates p)
    apply List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    change _ ∈ (if (centers l).isEmpty then
      [readDepth p (j + 1) - 2, readDepth p (j + 1), readDepth p (j + 1) + 2]
      else [readDepth p (j + 1), readDepth p (j + 1) + 2])
    split_ifs <;> simp

private theorem Y_even (p : Scales.Parameters) (j : ℕ) : p.Y j % 2 = 0 := by
  simp [Scales.Parameters.Y, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem L_even (p : Scales.Parameters) (j : ℕ) : p.L j % 2 = 0 := by
  by_cases hj : j = 0 <;>
    simp [Scales.Parameters.L, hj, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem D_even (p : Scales.Parameters) : p.D % 2 = 0 := by
  simp [Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem H_even (p : Scales.Parameters) : p.H % 2 = 0 := by
  simp [Scales.Parameters.H]

private theorem W_even (p : Scales.Parameters) : p.W % 2 = 0 := by
  simp [Scales.Parameters.W, Nat.mul_mod, D_even]

private theorem x_even (p : Scales.Parameters) (i : ℕ) : p.x i % 2 = 0 := by
  simp [Scales.Parameters.x, Nat.mul_mod, D_even]

private theorem readDepth_even (p : Scales.Parameters) (j : ℕ) : readDepth p j % 2 = 0 := by
  by_cases hj : j = 0
  · simp [hj, readDepth, depthTable]
  · by_cases hm : j ≤ p.levels
    · rw [readDepth_eq p (by omega) hm]
      exact Y_even p j
    · rw [readDepth_eq_zero p (by omega)]

private theorem readLength_even (p : Scales.Parameters) (j : ℕ) : readLength p j % 2 = 0 := by
  by_cases hj : j = 0
  · simp [hj, readLength, lengthTable]
  · by_cases hm : j ≤ p.levels
    · rw [readLength_eq p (by omega) hm]
      exact L_even p j
    · rw [readLength_eq_zero p (by omega)]

private theorem auxiliary_even (p : Scales.Parameters) (e : Endpoint) :
    (auxiliary (coordinates p) e).1 % 2 = 0 ∧ (auxiliary (coordinates p) e).2 % 2 = 0 := by
  have hx := x_even p e.port
  have hL := readLength_even p e.level
  change (if e.inward then p.x e.port - readLength p e.level
      else p.x e.port + readLength p e.level) % 2 = 0 ∧
    (if e.inward then p.x e.port + 2 else p.x e.port - 2) % 2 = 0
  cases e.inward <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem specialColumns_even (p : Scales.Parameters) (i : ℕ) {x : ℕ}
    (hx : x ∈ specialColumns (coordinates p) i) : x % 2 = 0 := by
  have hi := x_even p i
  change x ∈ [p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

/-- Every coordinate in the actual original-street list is even. -/
theorem streetColumnCoordinates_even (l : PortLayout) (p : Scales.Parameters)
    {x : ℕ} (hx : x ∈ streetColumnCoordinates l p) : x % 2 = 0 := by
  change x ∈ streetColumns l (coordinates p) at hx
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | hx
  · rcases hx with hx | hx
    · rw [hx]
    · rw [hx]
      exact W_even p
  · obtain ⟨i, _, he⟩ := List.mem_map.mp hx
    rw [← he]
    exact x_even p i
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, _, hx⟩ := List.mem_flatMap.mp hx
      have he := auxiliary_even p e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact he.1
      · rw [hx]
        exact he.2
    · obtain ⟨i, _, hx⟩ := List.mem_flatMap.mp hx
      exact specialColumns_even p i hx

/-- Every actual selected depth, including depth-minus-two, is even. -/
private theorem workingDepthCoordinates_even (l : PortLayout) (p : Scales.Parameters) {y : ℕ}
    (hy : y ∈ workingDepthCoordinates l p) : y % 2 = 0 := by
  change y ∈ workingRows l (coordinates p) at hy
  obtain ⟨j, _, hy⟩ := List.mem_flatMap.mp hy
  have hd := readDepth_even p (j + 1)
  change y ∈ (if (centers l).isEmpty then
    [readDepth p (j + 1) - 2, readDepth p (j + 1), readDepth p (j + 1) + 2]
    else [readDepth p (j + 1), readDepth p (j + 1) + 2]) at hy
  split_ifs at hy <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  · rcases hy with rfl | rfl | rfl <;> omega
  · rcases hy with rfl | rfl <;> omega

/-- Every selected actual vertical street has an even coordinate. -/
theorem streetColumnSet_even (l : PortLayout) (p : Scales.Parameters)
    {x : Fin (p.W + 1)} (hx : x ∈ streetColumnSet l p) : x.val % 2 = 0 :=
  streetColumnCoordinates_even l p hx

/-- Every selected actual row on either page, including the frame, has an even coordinate. -/
theorem workingRowSet_even (l : PortLayout) (p : Scales.Parameters)
    {y : Fin (p.H + 1)} (hy : y ∈ workingRowSet l p) : y.val % 2 = 0 := by
  change y.val ∈ [0, p.H] ++ _ at hy
  rcases List.mem_append.mp hy with hy | hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy
    · rw [hy]
    · rw [hy]
      exact H_even p
  · obtain ⟨v, hv, hy⟩ := List.mem_flatMap.mp hy
    have he := workingDepthCoordinates_even l p hv
    have hH := H_even p
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy <;> omega

private theorem separated_of_even {k : ℕ} (X : Set (Fin k))
    (hX : ∀ x ∈ X, x.val % 2 = 0) : Support.Separated X := by
  intro a b ha hb he
  have := hX a ha
  have := hX b hb
  omega

/-- The actual original columns contain no adjacent selected coordinates. -/
theorem streetColumnSet_separated (l : PortLayout) (p : Scales.Parameters) :
    Support.Separated (streetColumnSet l p) :=
  separated_of_even _ fun _ => streetColumnSet_even l p

/-- The full actual working-row set contains no adjacent selected coordinates. -/
theorem workingRowSet_separated (l : PortLayout) (p : Scales.Parameters) :
    Support.Separated (workingRowSet l p) :=
  separated_of_even _ fun _ => workingRowSet_even l p

/-- The actual emitted street sets satisfy the geometric closure used by reverse support. -/
theorem streets_axisClosed (l : PortLayout) (p : Scales.Parameters) :
    Support.AxisClosed (Support.streets (streetColumnSet l p) (workingRowSet l p)) :=
  Support.streets_axisClosed (streetColumnSet_separated l p) (workingRowSet_separated l p)

end PushPuzzle.PushS.PortLayout
