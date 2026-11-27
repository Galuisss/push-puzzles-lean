/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWirePaymentGeometry
public import Push.AcceptanceSoundnessOrdinaryWalksStock
import all Push.AcceptanceSoundnessSupportCoordinatesGuards
import all Push.AcceptanceSoundnessCentral
import all PushS.PortStreetSupport
import all PushS.PortGatePageWindow
import all PushS.PortStreetEnumeration
import all PushS.PortGateIndexing
import all PushS.PortEndpointLocality
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortWideGeometry
import all PushS.PortWireRail
import all PushS.PortSegments

/-! Every actual guard column has fixed target stock and supplies no ordinary WIRE payment. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem endpoint_guard_midpoint (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {e : Endpoint} (he : e ∈ l.endpoints) {s : Segment}
    (hs : s ∈ endpointFixedSegments l (coordinates p) e)
    (hg : GuardPoint l (coordinates p) s) :
    s.start.1 = (EndpointStreet.f.column p e + p.x e.port) / 2 := by
  have hfar (x : ℕ) (hx : x ∈ l.streetColumnCoordinates p) : 14 < Nat.dist s.start.1 x :=
    of_decide_eq_true (List.all_eq_true.mp hg.2.2.2 x hx)
  have hxAxis := axis_in_streetColumns l p (l.endpoints_port_lt hl he)
  have haux := auxiliary_columns l p he
  have hf := hfar _ haux.1
  have hr := hfar _ haux.2
  have haxis := hfar _ hxAxis
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · simp only [segment, Nat.min_self, Nat.dist_self] at hf
    omega
  · simp only [segment, Nat.min_self, Nat.dist_self] at hr
    omega
  · have hx0 := readLength_add_lt_x p e.port e.level
    cases hi : e.inward <;>
      simp only [segment, auxiliary, outward, inward, hi, Bool.false_eq_true, ite_true, ite_false,
        Nat.dist] at hf hr haxis ⊢ <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        simp only [point, segment, Nat.min_self, EndpointStreet.column_f]
        rfl
      · cases hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hx0 := readLength_add_lt_x p e.port 0
        simp only [point, segment, Nat.min_self] at haxis
        have hc : (coordinates p).x e.port = p.x e.port := rfl
        rw [hc] at haxis
        cases hi : e.inward <;>
          simp only [inward, hi, Bool.false_eq_true, ite_true, ite_false, Nat.dist] at haxis <;> omega
      · cases hs
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · simp only [point, segment, Nat.min_self, Nat.dist_self] at hf
        omega
      · simp only [point, segment, Nat.min_self, Nat.dist_self] at hr
        omega
    · cases hs

/-- Every emitted guard column comes from an ordinary f midpoint or an actual wide separator point. -/
private theorem acceptanceGuard_source_columns (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {x : ℕ} (hx : x ∈ guards l p) :
    (∃ e ∈ l.endpoints, x = (EndpointStreet.f.column p e + p.x e.port) / 2) ∨
      ∃ g ∈ l.wideSeparatorHoles p, g.1.val = x := by
  obtain ⟨s, hs, hg, hx⟩ := actual_guard_origin l p hx
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with he | hgates | hu | hd | haux
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp he
    rw [rounded_endpoint l p hl hM e he hs] at hg hx
    exact Or.inl ⟨e, he, hx.symm.trans (endpoint_guard_midpoint l p hl he hs hg)⟩
  · obtain ⟨middle, hi, hs⟩ := List.mem_flatMap.mp hgates
    rw [rounded_gate l p middle hs] at hg hx
    have hc := point_start_contains s hg.1
    have hspan := gate_fixed_span p middle ((mem_pointHoles _ s.start).mpr ⟨s, hs, hc⟩)
    have haxis := axis_in_streetColumns l p (gate_center_lt l hl hi)
    have hfar : 14 < Nat.dist s.start.1 (p.x middle) :=
      of_decide_eq_true (List.all_eq_true.mp hg.2.2.2 _ haxis)
    simp only [Nat.dist] at hfar
    exact False.elim (by omega)
  · right
    have hwide := rounded_wide_mem l p .upper hu
    have hc := point_start_contains (roundedPiece l p s) hg.1
    have hfixed := List.mem_append_right (frame (coordinates p)) (physicalWide_mem_marked l p .upper hwide)
    have hb := l.fixedSegments_contains_bounds p hl haxes hfixed hc
    let g : Cell (p.W + 1) (p.H + 1) :=
      (⟨(roundedPiece l p s).start.1, by omega⟩, ⟨(roundedPiece l p s).start.2, by omega⟩)
    exact ⟨g, (SegmentRecipe.mem_holes _ g).mpr
      ⟨_, List.mem_append_left _ hwide, hc⟩, hx⟩
  · right
    have hwide := rounded_wide_mem l p .lower hd
    have hc := point_start_contains (roundedPiece l p s) hg.1
    have hfixed := List.mem_append_right (frame (coordinates p)) (physicalWide_mem_marked l p .lower hwide)
    have hb := l.fixedSegments_contains_bounds p hl haxes hfixed hc
    let g : Cell (p.W + 1) (p.H + 1) :=
      (⟨(roundedPiece l p s).start.1, by omega⟩, ⟨(roundedPiece l p s).start.2, by omega⟩)
    exact ⟨g, (SegmentRecipe.mem_holes _ g).mpr
      ⟨_, List.mem_append_right _ hwide, hc⟩, hx⟩
  · obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp haux
    change GuardPoint l (coordinates p) (roundedPiece l p (point col p.D)) at hg
    rw [rounded_auxiliary l p hcol] at hg
    exact False.elim (central_not_guard l p col p.D (by omega) (by omega) hg)

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- All accepted holes on any actual guard column belong to its fixed canonical target stock. -/
theorem canonical_guard_column_target_stock {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ guards l p)
    (hq : q ∈ PushS.holes t) (hf : q ∉ Boundary.frame) : q ∈ targetHoles l p target := by
  rcases l.acceptanceGuard_source_columns p hl hM haxes hx with ⟨e, he, hx⟩ | ⟨g, hg, hx⟩
  · exact canonical_midpoint_column_target_stock_of_reader l p hl hM haxes initial target e he hr ha
      (fun s hs ht => canonical_allReaderWalks_empty l p hl hM haxes initial target hgate e.level hs ht ha) hx hq
  · exact canonical_wide_column_target_stock l p hl hM haxes initial target hr ha hg (Fin.ext hx.symm) hq hf

/-- No actual accepted ordinary-rail hole lies on a guard column. -/
theorem canonical_wire_hole_not_guard {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t) (hrail : q ∈ wireOpenRail p g) :
    q.1.val ∉ guards l p := by
  intro hx
  have hports := wire_ports l hl hg hw
  have hY := readDepth_ge p (placement_level_bounds l hl hg).1 ((placement_level_bounds l hl hg).2.trans hM)
  have hD := readDepth_add_lt_D p g.level
  have hH : p.H = 2 * p.D := rfl
  have hrow := (Finset.mem_filter.mp hrail).2
  have hx0 := readLength_add_lt_x p g.left 0
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le haxes) 0
  have hf : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases hs : g.side <;> cases d <;>
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hs,
        ite_true, reduceCtorEq, ite_false] at hd hrow <;> omega
  have htarg := canonical_guard_column_target_stock l p hl hM haxes initial target hgate hr ha hx hq hf
  have hnear := l.encodedSegments_wireOpenRail p hl hM haxes (l.canonical target) hg hw
  have hqnear := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hnear).mp
    (Finset.mem_inter.mpr ⟨htarg, hrail⟩)
  have hn := (wire_near_mem p (l.canonical target) g _).mp ((finite_mem p _ q).mp hqnear)
  have hL := l.acceptanceGuard_street_far p hx (axis_in_streetColumns l p (hports.1.trans hports.2))
  have hR := l.acceptanceGuard_street_far p hx (axis_in_streetColumns l p hports.2)
  have hb := Bool.toNat_le ((l.canonical target).internal.getD g.internal false)
  have hnb := Bool.toNat_le (!((l.canonical target).internal.getD g.internal false))
  simp only [Nat.dist] at hL hR
  rcases hn.2 with hn | hn <;> omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
