/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointAxisReadout
public import PushS.PortEndpointHorizontalReadout
import all PushS.PortLayoutCoordinates

/-! The actual endpoint hole words uniquely determine the decoded axis and horizontal failure threshold. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem parameter_le {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {parameter shift otherParameter otherShift : ℕ}
    (hr : EndpointAxisReadout p e u parameter shift) (other : EndpointAxisReadout p e u otherParameter otherShift)
    (hp : e.port < p.axes) (hY : 4 ≤ readDepth p e.level) : otherParameter ≤ parameter := by
  have hsource := hr.shift_le
  have htarget := other.shift_le
  have hxW := x_add_readLength_lt_W p hp 0
  have hH := readDepth_add_lt_H p e.level
  have hD := readDepth_add_lt_D p e.level
  let depth := readDepth p e.level + 3 - parameter
  have hdepth : 4 ≤ depth ∧ depth < p.D ∧ depth ≤ p.H := by dsimp only [depth]; omega
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x e.port, by omega⟩, ⟨if e.side = .upper then depth else p.H - depth, by split <;> omega⟩)
  have hy : (if e.side = .upper then q.2.val else p.H - q.2.val) = depth := by
    cases hs : e.side <;> simp only [q, hs, reduceCtorEq, ite_true, ite_false]; omega
  have hhalf : 0 < (if e.side = .upper then q.2.val else p.H - q.2.val) ∧
      (if e.side = .upper then q.2.val else p.H - q.2.val) < p.D := by rw [hy]; omega
  have hq : q ∈ holes u := by
    apply (hr.axis_holes q rfl hhalf).mpr
    right
    rw [hy]
    dsimp only [depth]
    omega
  have hh := (other.axis_holes q rfl hhalf).mp hq
  rw [hy] at hh
  dsimp only [depth] at hh
  omega

/-- Two actual half-axis words for the same endpoint assign the same ordinary axis parameter. -/
theorem EndpointAxisReadout.parameter_unique {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {parameter shift otherParameter otherShift : ℕ}
    (hr : EndpointAxisReadout p e u parameter shift) (other : EndpointAxisReadout p e u otherParameter otherShift)
    (hp : e.port < p.axes) (hY : 4 ≤ readDepth p e.level) : parameter = otherParameter :=
  Nat.le_antisymm (parameter_le other hr hp hY) (parameter_le hr other hp hY)

/-- The actual second inward cell uniquely determines whether the horizontal endpoint supply has failed. -/
theorem EndpointHorizontalReadout.failed_iff {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {horizontal otherHorizontal : ℕ}
    (hr : EndpointHorizontalReadout p e u horizontal) (other : EndpointHorizontalReadout p e u otherHorizontal)
    (hp : e.port < p.axes) : horizontal ≤ 1 ↔ otherHorizontal ≤ 1 := by
  have hxW := x_add_readLength_lt_W p hp 0
  have hx0 := readLength_add_lt_x p e.port 0
  have hH := readDepth_add_lt_H p e.level
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨if e.inward then p.x e.port + 2 else p.x e.port - 2, by split <;> omega⟩,
      ⟨if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level, by split <;> omega⟩)
  have hfirst := hr.near_holes q 2 (by omega) (by omega) rfl rfl
  have hsecond := other.near_holes q 2 (by omega) (by omega) rfl rfl
  have heq := hfirst.symm.trans hsecond
  omega

/-- Every actual ordinary endpoint's genuine half-axis parameter is unique. -/
theorem endpoint_axis_parameter_unique (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {u : State (p.W + 1) (p.H + 1)} {parameter shift otherParameter otherShift : ℕ}
    (hr : EndpointAxisReadout p e u parameter shift) (other : EndpointAxisReadout p e u otherParameter otherShift) :
    parameter = otherParameter := by
  apply hr.parameter_unique other ((l.endpoints_port_lt hl he).trans_le ha)
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  omega

/-- Every actual ordinary endpoint's failed horizontal threshold is independent of its chosen readout. -/
theorem endpoint_horizontal_failed_iff (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {u : State (p.W + 1) (p.H + 1)} {horizontal otherHorizontal : ℕ}
    (hr : EndpointHorizontalReadout p e u horizontal) (other : EndpointHorizontalReadout p e u otherHorizontal) :
    horizontal ≤ 1 ↔ otherHorizontal ≤ 1 :=
  hr.failed_iff other ((l.endpoints_port_lt hl he).trans_le ha)

end PushPuzzle.PushS.PortLayout
