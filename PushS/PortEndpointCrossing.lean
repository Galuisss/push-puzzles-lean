/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCoreCounts
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! Global separation of physical endpoint pieces at different ports or pages. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem fixed_endpoint_span (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    p.x e.port - (readLength p e.level + 2) ≤ q.1 ∧
      q.1 ≤ p.x e.port + readLength p e.level + 2 := by
  have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  change (coordinates p).x e.port - ((coordinates p).length e.level + 2) ≤ q.1 ∧
    q.1 ≤ (coordinates p).x e.port + (coordinates p).length e.level + 2
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · have hv := vertical_coordinates hq
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hv <;> omega
  · have hv := vertical_coordinates hq
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hv <;> omega
  · have hh := horizontal_coordinates hq
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hh <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hp := point_coordinates hq
        cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hp <;> omega
      · cases hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hp := point_coordinates hq
        cases hd : e.inward <;> simp [inward, hd] at hp <;> omega
      · cases hs
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals have hp := point_coordinates hq
      all_goals cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hp <;> omega
    · cases hs

private theorem axis_spacing (p : Scales.Parameters) {i j : ℕ} (hij : i < j) :
    p.x i + p.D ≤ p.x j := by
  have hx := Nat.mul_le_mul_right p.D (show i + 1 + 1 ≤ j + 1 by omega)
  simpa only [Scales.Parameters.x, Nat.add_mul, Nat.one_mul] using hx

/-- A fixed endpoint piece and signal endpoint at distinct ports share no physical hole. -/
theorem endpointFixedSegments_disjoint_of_port_ne (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (fixed signal : Endpoint) (hport : fixed.port ≠ signal.port) :
    Disjoint (pointHoles (endpointFixedSegments l (coordinates p) fixed))
      (pointHoles (endpointSegments (coordinates p) state signal)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  have hf := fixed_endpoint_span l p fixed hfixed
  have hs := endpoint_near p state signal hsignal
  have hs' : p.x signal.port - 2 ≤ q.1 ∧ q.1 ≤ p.x signal.port + 2 := by
    change (coordinates p).x signal.port - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x signal.port + 2
    cases hd : signal.inward <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at hs <;> omega
  have hmargin := readDepth_readLength_margin p 0 fixed.level
  rcases lt_or_gt_of_ne hport with hp | hp
  · have hgap := axis_spacing p hp
    omega
  · have hgap := axis_spacing p hp
    omega

private theorem segment_page (p : Scales.Parameters) (side : Side) {x u y v : ℕ}
    (hy : y + 32 < p.D) (hv : v + 32 < p.D) {q : ℕ × ℕ}
    (hq : (segment x (onSide (coordinates p) side y) u (onSide (coordinates p) side v)).Contains q) :
    if side = .upper then q.2 + 32 < p.D else p.D + 32 < q.2 := by
  have hH : p.H = 2 * p.D := rfl
  cases side <;> simp [segment, Segment.Contains, onSide, coordinates] at hq ⊢ <;> omega

private theorem fixed_endpoint_page (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    if e.side = .upper then q.2 + 32 < p.D else p.D + 32 < q.2 := by
  have hu : (coordinates p).depth e.level + 64 < p.D := readDepth_add_lt_D p e.level
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · exact segment_page p e.side (by omega) (by omega) hq
  · exact segment_page p e.side (by omega) (by omega) hq
  · exact segment_page p e.side (by omega) (by omega) hq
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        exact segment_page p e.side (by omega) (by omega) hq
      · cases hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        exact segment_page p e.side (by omega) (by omega) hq
      · cases hs
  · split at hs
    · have hn : (coordinates p).depth (e.level + 1) + 64 < p.D :=
        readDepth_add_lt_D p (e.level + 1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact segment_page p e.side (by omega) (by omega) hq
    · cases hs

private theorem signal_endpoint_page (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) :
    if e.side = .upper then q.2 + 32 < p.D else p.D + 32 < q.2 := by
  have hu : (coordinates p).depth e.level + 64 < p.D := readDepth_add_lt_D p e.level
  have hb := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> exact segment_page p e.side (by omega) (by omega) hq

/-- Endpoint fixed pieces and endpoint signals on opposite pages are separated by the central row. -/
theorem endpointFixedSegments_disjoint_of_side_ne (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (fixed signal : Endpoint) (hside : fixed.side ≠ signal.side) :
    Disjoint (pointHoles (endpointFixedSegments l (coordinates p) fixed))
      (pointHoles (endpointSegments (coordinates p) state signal)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  have hf := fixed_endpoint_page l p fixed hfixed
  have hs := signal_endpoint_page p state signal hsignal
  cases hfs : fixed.side <;> cases hss : signal.side <;>
    simp [hfs, hss] at hside hf hs <;> omega

end PushPuzzle.PushS.PortLayout
