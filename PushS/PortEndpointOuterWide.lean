/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointWide
import all PushS.PortEndpointWide
import all PushS.PortWideGeometry
import all PushS.PortTwoPageStreets
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortCentralMargins
import all PushS.PortSegmentBounds
import all PushS.PortAxisClear
import all PushS.PortWireIndexing
import all PushS.PortWireGeometry
import all PushS.PortSegments

/-!
# Actual wide separators outside ordinary endpoint streets

The outer neighbour of the actual f street bounds a wide gap. Any placement crossing this
gap strictly encloses the endpoint and therefore has a deeper work row. Every selected row
through the endpoint's branch row consequently receives its actual wide separator point.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- An actual separator on a specified work row, beyond the endpoint's outer f street. -/
structure EndpointOuterWideSeparator (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (v : ℕ) where
  /-- Actual finite emitted cell. -/
  cell : Cell (p.W + 1) (p.H + 1)
  /-- Membership after conditional even rounding. -/
  hole : cell ∈ l.wideSeparatorHoles p
  /-- The specified depth, reflected on the lower page. -/
  row : cell.2.val = if e.side = .upper then v else p.H - v
  /-- Strictly beyond the outer f street. -/
  outward : if e.inward then cell.1.val < p.x e.port - readLength p e.level
    else p.x e.port + readLength p e.level < cell.1.val
  /-- The interval from the f street to the separator contains no page column. -/
  columnsEmpty : ∀ z ∈ l.pageColumnCoordinates p e.side,
    ¬(if e.inward then cell.1.val ≤ z ∧ z < p.x e.port - readLength p e.level
      else p.x e.port + readLength p e.level < z ∧ z ≤ cell.1.val)

private theorem near_column_sharp (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {i z : ℕ} (hz : z ∈ l.pageColumnCoordinates p side)
    (hnear : Nat.dist z (p.x i) ≤ 2 * p.L p.levels + 12) :
    Nat.dist z (p.x i) ≤ p.L p.levels + 12 := by
  obtain ⟨k, _, hkz, hzk⟩ := streetColumn_near_grid l p hl side
    (pageColumn_mem_street l p hl side hz)
  have hD := p.outer_distance
  have hsep := grid_separated p.D k (i + 1)
  change k * p.D = p.x i ∨ k * p.D + p.D ≤ p.x i ∨ p.x i + p.D ≤ k * p.D at hsep
  simp only [Nat.dist] at hnear ⊢
  rcases hsep with h | h | h <;> omega

private theorem outer_gap (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) :
    ∃ a b, (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p e.side) ∧
      p.L p.levels < b - a ∧
      (if e.inward then b = p.x e.port - readLength p e.level
        else a = p.x e.port + readLength p e.level) := by
  have hc : (coordinates p).x e.port = p.x e.port := rfl
  have hlength : (coordinates p).length e.level = readLength p e.level := rfl
  have hf : (auxiliary (coordinates p) e).1 ∈ l.pageColumnCoordinates p e.side :=
    endpoint_columns_mem l p e he (by simp)
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hpositive := readLength_ge p hj hm
  have hmax := readLength_le_last p e.level
  have hleft := readLength_add_lt_x p e.port e.level
  have hright := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) e.level
  cases hd : e.inward with
  | false =>
    simp only [auxiliary, outward, hd, Bool.false_eq_true, ite_false, hc, hlength] at hf
    have hframe : p.W ∈ l.pageColumnCoordinates p e.side := by
      simp [pageColumnCoordinates, pageColumns, show (coordinates p).W = p.W from rfl]
    obtain ⟨b, hab⟩ := next_column _ hf ⟨p.W, hframe, by omega⟩
    have hgap := (adjacentPair_gap hab).1
    have hb := (adjacentPair_mem hab).2
    have hwide : p.L p.levels < b - (p.x e.port + readLength p e.level) := by
      by_contra h
      have hnear : Nat.dist b (p.x e.port) ≤ 2 * p.L p.levels + 12 := by
        simp only [Nat.dist]
        omega
      have hcols := nearby_page_columns l p hl ha he hb (near_column_sharp l p hl _ hb hnear)
      simp only [auxiliary, outward, inward, hd, Bool.false_eq_true, ite_false, hc, hlength] at hcols
      omega
    exact ⟨p.x e.port + readLength p e.level, b, hab, hwide, by simp⟩
  | true =>
    simp only [auxiliary, outward, hd, ite_true, hc, hlength] at hf
    have hzero : 0 ∈ l.pageColumnCoordinates p e.side := by simp [pageColumnCoordinates, pageColumns]
    obtain ⟨a, hab⟩ := previous_column _ hf ⟨0, hzero, by omega⟩
    have hgap := (adjacentPair_gap hab).1
    have ha' := (adjacentPair_mem hab).1
    have hwide : p.L p.levels < p.x e.port - readLength p e.level - a := by
      by_contra h
      have hnear : Nat.dist a (p.x e.port) ≤ 2 * p.L p.levels + 12 := by
        simp only [Nat.dist]
        omega
      have hcols := nearby_page_columns l p hl ha he ha' (near_column_sharp l p hl _ ha' hnear)
      simp only [auxiliary, outward, inward, hd, ite_true, hc, hlength] at hcols
      omega
    exact ⟨a, p.x e.port - readLength p e.level, hab, hwide, by simp⟩

private theorem outer_span_ports (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    {g : Placement} (hg : g ∈ placements l) (hs : e.side = g.side)
    (hf : p.x g.left ≤ (auxiliary (coordinates p) e).1 ∧
      (auxiliary (coordinates p) e).1 ≤ p.x g.right) : g.left < e.port ∧ e.port < g.right := by
  have hnL := auxiliary_off_axis l p hl hM he g.left (Or.inl rfl)
  have hnR := auxiliary_off_axis l p hl hM he g.right (Or.inl rfl)
  have hspan : p.x e.port - (readLength p e.level + 2) ≤ (auxiliary (coordinates p) e).1 ∧
      (auxiliary (coordinates p) e).1 ≤ p.x e.port + (readLength p e.level + 2) := by
    have hc : (coordinates p).x e.port = p.x e.port := rfl
    have hlength : (coordinates p).length e.level = readLength p e.level := rfl
    cases hd : e.inward <;> simp only [auxiliary, outward, hd, Bool.false_eq_true,
      ite_true, ite_false, hc, hlength] <;> omega
  have hlo : p.x g.left < (auxiliary (coordinates p) e).1 := by omega
  have hhi : (auxiliary (coordinates p) e).1 < p.x g.right := by omega
  have hm := readDepth_readLength_margin p 0 e.level
  have hb := span_port_bounds p (by omega) hspan hlo hhi
  have hneL : e.port ≠ g.left := by
    intro h
    let f : Endpoint := ⟨g.side, g.left, true, g.level, g.internal⟩
    have hmem : f ∈ l.endpoints := List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_self⟩
    have heq := l.endpoints_key_injective hl he hmem hs h
    have hdir : e.inward = true := congrArg Endpoint.inward heq
    have hc : (coordinates p).x e.port = p.x g.left := by change p.x e.port = p.x g.left; rw [h]
    simp only [auxiliary, outward, hdir, ite_true, hc] at hlo
    omega
  have hneR : e.port ≠ g.right := by
    intro h
    let f : Endpoint := ⟨g.side, g.right, false, g.level,
      g.internal + if g.gate.isSome then 2 else 0⟩
    have hmem : f ∈ l.endpoints :=
      List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_of_mem _ List.mem_cons_self⟩
    have heq := l.endpoints_key_injective hl he hmem hs h
    have hdir : e.inward = false := congrArg Endpoint.inward heq
    have hc : (coordinates p).x e.port = p.x g.right := by change p.x e.port = p.x g.right; rw [h]
    simp only [auxiliary, outward, hdir, Bool.false_eq_true, ite_false, hc] at hhi
    omega
  omega

private theorem outer_gap_uncrossed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    {a b v : ℕ} (hab : (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p e.side))
    (hout : if e.inward then b = p.x e.port - readLength p e.level
      else a = p.x e.port + readLength p e.level)
    (hv : v ≤ readDepth p e.level + 2) : crosses l (coordinates p) e.side a b v = false := by
  apply Bool.eq_false_iff.mpr
  intro hcross
  obtain ⟨g, hg, hcross⟩ := List.any_eq_true.mp hcross
  obtain ⟨hside, hrow, hleft, _, hright⟩ := of_decide_eq_true hcross
  have hc : (coordinates p).x = p.x := rfl
  have hlength : (coordinates p).length e.level = readLength p e.level := rfl
  have hgap := (adjacentPair_gap hab).1
  have hf : p.x g.left ≤ (auxiliary (coordinates p) e).1 ∧
      (auxiliary (coordinates p) e).1 ≤ p.x g.right := by
    simp only [hc] at hleft hright
    cases hd : e.inward <;>
      simp only [auxiliary, outward, hd, Bool.false_eq_true, ite_true, ite_false, hc, hlength] at hout ⊢ <;>
      omega
  have hports := outer_span_ports l p hl hM he hg hside.symm hf
  cases hk : g.gate with
  | none =>
    have hj := interior_endpoint_shallower l hl hg hk he hside.symm hports.1 hports.2
    have hgLevel := placement_level_bounds l hl hg
    have heLevel := l.endpoints_level_bounds p hl hM he
    have hdepth := depth_gap p heLevel.1 hj (show g.level ≤ p.levels by omega)
    change readDepth p g.level = v at hrow
    omega
  | some kind =>
    have hshape := placement_gate_shape l hg hk
    have hm := placement_gate_mem l hg hk
    exact l.endpoints_lower_ne_gate_middle hl hm he (hside.symm.trans hshape.1)
      (by omega)

/-- Every actual working depth through an ordinary endpoint's branch row has an actual
wide separator outside that endpoint's f street. -/
theorem endpointOuterWideSeparator_nonempty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) {v : ℕ} (hv : v ∈ l.workingDepthCoordinates p)
    (hve : v ≤ readDepth p e.level + 2) : Nonempty (EndpointOuterWideSeparator l p e v) := by
  obtain ⟨a, b, hab, hwide, hout⟩ := outer_gap l p hl hM ha he
  have hcross := outer_gap_uncrossed l p hl hM he hab hout hve
  obtain ⟨g, hhole, hrow, hinside⟩ := wide_cell_of_uncrossed l p hl ha e.side hv hab hwide hcross
  refine ⟨⟨g, hhole, hrow, ?_, ?_⟩⟩
  · cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hout ⊢ <;> omega
  · intro z hz hzin
    have hno := (adjacentPair_gap hab).2 z hz
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hout hzin <;> omega

end PushPuzzle.PushS.PortLayout
