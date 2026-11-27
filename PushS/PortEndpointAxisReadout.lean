/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisTrainReadout

/-! A common actual half-axis word for any ordinary endpoint. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual frame gap and near gap of one ordinary endpoint on its reflected half-axis. -/
structure EndpointAxisReadout (p : Scales.Parameters) (e : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (parameter shift : ℕ) : Prop where
  /-- The near gap is nonempty between its shifted outer rod and middle train. -/
  shift_le : shift + parameter ≤ 3
  /-- Exact holes on this complete actual half-axis. -/
  axis_holes (q : Cell (p.W + 1) (p.H + 1)) (axis : q.1.val = p.x e.port)
      (half : 0 < (if e.side = .upper then q.2.val else p.H - q.2.val) ∧
        (if e.side = .upper then q.2.val else p.H - q.2.val) < p.D) :
    q ∈ holes u ↔ (if e.side = .upper then q.2.val else p.H - q.2.val) ≤ shift ∨
      ((shift : ℤ) ≤ ((if e.side = .upper then q.2.val else p.H - q.2.val : ℕ) : ℤ) - readDepth p e.level ∧
        ((if e.side = .upper then q.2.val else p.H - q.2.val : ℕ) : ℤ) - readDepth p e.level ≤ 3 - (parameter : ℤ))

/-- The genuine ordinary-axis upper word is the upper endpoint's own reflected readout. -/
theorem OrdinaryAxisReadout.upper_endpoint {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement}
    (hr : OrdinaryAxisReadout p upper lower u a) (hs : upper.side = .upper) :
    EndpointAxisReadout p upper u a.parameter a.upperShift := by
  refine ⟨hr.upper_shift_le, ?_⟩
  intro q hx hy
  simp only [hs, ite_true] at hy ⊢
  exact hr.upper_holes q hx hy

/-- The genuine ordinary-axis lower word is the lower endpoint's complementary reflected readout. -/
theorem OrdinaryAxisReadout.lower_endpoint {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement}
    (hr : OrdinaryAxisReadout p upper lower u a) (hs : lower.side = .lower) (hp : lower.port = upper.port) :
    EndpointAxisReadout p lower u a.lowerParameter a.lowerShift := by
  have hparam := hr.parameter_le
  have hshift := hr.lower_shift_le
  refine ⟨by unfold OrdinaryAxisPlacement.lowerParameter; omega, ?_⟩
  intro q hx hy
  simp only [hs, reduceCtorEq, ite_false] at hy ⊢
  rw [hp] at hx
  have hmax : (3 : ℤ) - (a.lowerParameter : ℤ) = a.parameter := by
    unfold OrdinaryAxisPlacement.lowerParameter
    omega
  rw [hmax]
  exact hr.lower_holes q hx hy

/-- A failed ordinary axis input occupies both axis neighbours outside its three-cell pocket. -/
theorem EndpointAxisReadout.fault_axis_box {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {parameter shift : ℕ}
    (hr : EndpointAxisReadout p e u parameter shift) (hbad : 2 ≤ parameter)
    (hY : 3 ≤ readDepth p e.level) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x e.port)
    (hy : (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level - 1 ∨
      (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level + 2) :
    q ∈ u.boxes := by
  have hmargin := readDepth_add_lt_D p e.level
  have hshift := hr.shift_le
  have hhalf : 0 < (if e.side = .upper then q.2.val else p.H - q.2.val) ∧
      (if e.side = .upper then q.2.val else p.H - q.2.val) < p.D := by omega
  by_contra hb
  have hh := (hr.axis_holes q hx hhalf).mp ((mem_holes q).mpr hb)
  omega

end PushPuzzle.PushS.PortLayout
