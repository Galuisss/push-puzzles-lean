/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireTrainReadout
public import PushS.PortGateTrainReadout
import all PushS.PortWireTrains
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortGateTrainReadout
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing

/-! Actual near-horizontal endpoint holes from the complete WIRE and gate trains. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The first three inward work-row cells of an ordinary endpoint read its actual horizontal gap length. -/
structure EndpointHorizontalReadout (p : Scales.Parameters) (e : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (horizontal : ℕ) : Prop where
  near_holes (q : Cell (p.W + 1) (p.H + 1)) (distance : ℕ) (positive : 1 ≤ distance) (near : distance ≤ 3)
      (column : q.1.val = if e.inward then p.x e.port + distance else p.x e.port - distance)
      (row : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) :
    q ∈ holes u ↔ distance ≤ horizontal

/-- A failed horizontal supply occupies the actual second inward work-row cell. -/
theorem EndpointHorizontalReadout.fault_probe_box {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {horizontal : ℕ}
    (hr : EndpointHorizontalReadout p e u horizontal) (hbad : horizontal ≤ 1)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port + 2 else p.x e.port - 2)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) : q ∈ u.boxes := by
  by_contra hb
  have hh := (hr.near_holes q 2 (by omega) (by omega) hx hy).mp ((mem_holes q).mpr hb)
  omega

/-- The actual WIRE's left gap supplies the left ordinary endpoint's complete near-horizontal word. -/
theorem WireRailReadout.left_endpoint {l : PortLayout} {p : Scales.Parameters} {g : Placement}
    {u : State (p.W + 1) (p.H + 1)} {left right : ℕ} (hs : WireRailReadout p g u left right)
    (hl : l.pages.Valid) (hg : g ∈ placements l) (hw : g.gate = none) :
    EndpointHorizontalReadout p ⟨g.side, g.left, true, g.level, g.internal⟩ u left := by
  constructor
  intro q distance hd hd3 hx hy
  have hmargin := wire_train_margin l p hl hg hw
  have hsum := hs.holes_sum
  simp only [ite_true] at hx
  have hR : q ∈ wireOpenRail p g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩
  rw [hs.rail_holes q hR]
  omega

/-- The actual WIRE's right gap supplies the right ordinary endpoint's complete near-horizontal word. -/
theorem WireRailReadout.right_endpoint {l : PortLayout} {p : Scales.Parameters} {g : Placement}
    {u : State (p.W + 1) (p.H + 1)} {left right : ℕ} (hs : WireRailReadout p g u left right)
    (hl : l.pages.Valid) (hg : g ∈ placements l) (hw : g.gate = none) :
    EndpointHorizontalReadout p ⟨g.side, g.right, false, g.level, g.internal⟩ u right := by
  constructor
  intro q distance hd hd3 hx hy
  have hmargin := wire_train_margin l p hl hg hw
  have hsum := hs.holes_sum
  simp only [Bool.false_eq_true, ite_false] at hx
  have hR : q ∈ wireOpenRail p g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩
  rw [hs.rail_holes q hR]
  omega

private theorem gate_outer_geometry (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    g.side = .lower ∧ g.level = 1 ∧ p.x g.left + 40 < p.x g.right ∧ 40 < p.D := by
  have hs := placement_gate_shape l hg hk
  have hspacing := axis_spacing p (gate_port_bounds l hl hg hk).1
  have hD := p.outer_distance
  exact ⟨hs.1, gate_level_one l hg hk, by omega, by omega⟩

/-- The actual gate's left long train gives its left ordinary endpoint's near-horizontal hole word. -/
theorem GateTrainShape.left_endpoint {l : PortLayout} {p : Scales.Parameters} {g : Placement}
    {kind : Shuttle.Kind} {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (hs : GateTrainShape p g kind u b) (hl : l.pages.Valid) (hg : g ∈ placements l) (hk : g.gate = some kind) :
    EndpointHorizontalReadout p ⟨g.side, g.left, true, g.level, g.internal⟩ u (gateTrainPlacement p g b).left := by
  constructor
  intro q distance hd hd3 hx hy
  have hgeometry := gate_outer_geometry l p hl hg hk
  simp only [ite_true] at hx
  simp only [hgeometry.1, hgeometry.2.1, reduceCtorEq, ite_false] at hy
  have hR : q ∈ gateOpenRail p g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩
  rw [mem_holes, hs.box_iff hR, ThreeBlocks.mem_slots]
  have hfit := hs.fits
  have hgap := hs.gapped
  have hfirst := hs.first_length
  have hmiddle := hs.middle_length
  have hcoord := hs.placement_coordinates
  have hkappa : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  change b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last at hgap
  omega

/-- The actual gate's right long train gives its right ordinary endpoint's near-horizontal hole word. -/
theorem GateTrainShape.right_endpoint {l : PortLayout} {p : Scales.Parameters} {g : Placement}
    {kind : Shuttle.Kind} {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (hs : GateTrainShape p g kind u b) (hl : l.pages.Valid) (hg : g ∈ placements l) (hk : g.gate = some kind) :
    EndpointHorizontalReadout p ⟨g.side, g.right, false, g.level, g.internal + 2⟩ u (gateTrainPlacement p g b).right := by
  constructor
  intro q distance hd hd3 hx hy
  have hgeometry := gate_outer_geometry l p hl hg hk
  simp only [Bool.false_eq_true, ite_false] at hx
  simp only [hgeometry.1, hgeometry.2.1, reduceCtorEq, ite_false] at hy
  have hR : q ∈ gateOpenRail p g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩
  rw [mem_holes, hs.box_iff hR, ThreeBlocks.mem_slots]
  have hfit := hs.fits
  have hgap := hs.gapped
  have hmiddle := hs.middle_length
  have hlast := hs.last_length
  have hcoord := hs.placement_coordinates
  change b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last at hgap
  omega

end PushPuzzle.PushS.PortLayout
