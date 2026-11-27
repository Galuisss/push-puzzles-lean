/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateCertifiedSamples
public import Push.AcceptanceEndpointTrimPayment
import all PushS.PortGateRail
import all PushS.PortGateIndexing
import all PushS.PortSegments

/-! Actual outer receiving-column payments bound both weak terminal gate-rail ends. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram SegmentRecipe

private theorem endpoint_second_target (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints)
    (hbit : (if e.inward then (l.canonical target).internal.getD e.internal false
      else !((l.canonical target).internal.getD e.internal false)) = true)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port + 2 else p.x e.port - 2)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) :
    q ∈ targetHoles l p target := by
  have hx0 := readLength_add_lt_x p e.port 0
  have hpoint : (q.1.val, q.2.val) ∈ pointHoles ((endpointSegments (coordinates p) (l.canonical target) e).drop 1) := by
    apply (endpoint_horizontal_mem p (l.canonical target) e _).mpr
    refine ⟨hy, ?_⟩
    cases hi : e.inward <;> cases hb : (l.canonical target).internal.getD e.internal false <;>
      simp only [hi, hb, Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true] at hbit hx ⊢ <;>
      simp only [Bool.toNat_true] <;> omega
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hpoint
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨e, he, List.mem_of_mem_drop hs⟩)), hc⟩

/-- A canonical target second horizontal hole emits the actual nonzero receiving-column quota. -/
theorem endpoint_work_delta_of_target_second (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port + 2 else p.x e.port - 2)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level)
    (htarget : q ∈ targetHoles l p target) : endpointWorkDelta l p target e = 1 := by
  have hY := readDepth_add_lt_H p e.level
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hread := readDepth_eq p hj hjm
  have hq : q ∈ endpointRWorkSlot l p target e := by
    apply Finset.mem_filter.mpr
    refine ⟨htarget, by simpa only [EndpointStreet.column_r] using hx, ?_⟩
    cases hs : e.side <;> simp only [pageDepth, hs, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega
  have hpositive := Finset.card_pos.mpr ⟨q, hq⟩
  have hbound := endpointWorkDelta_le_one l p target e
  change (endpointRWorkSlot l p target e).card ≤ 1 at hbound
  exact Nat.le_antisymm hbound hpositive

namespace GateRailBlocks

/-- A real hole at the left endpoint's second work cell forces at least two outer holes even before gaps are positive. -/
private theorem left_two_of_second_hole {p : Scales.Parameters} {g : Placement}
    {kind : Shuttle.Kind}
    {t : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks} (shape : GateRailBlocks p g kind t b)
    {q : Cell (p.W + 1) (p.H + 1)} (hR : q ∈ gateOpenRail p g)
    (hx : q.1.val = p.x g.left + 2) (hq : q ∈ holes t) : 2 ≤ (gateTrainPlacement p g b).left := by
  have hcoord := shape.placement_coordinates
  have hfit := shape.fits
  have hfirst := shape.first_length
  have hD := readDepth_readLength_margin p 0 0
  have hk : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  by_contra hn
  apply (PushS.mem_holes _).mp hq
  apply (shape.box_iff hR).mpr
  apply (b.mem_slots _).mpr
  exact Or.inl ⟨by omega, by omega⟩

/-- The corresponding actual right second work cell bounds the weak right outer hole count. -/
private theorem right_two_of_second_hole {p : Scales.Parameters} {g : Placement}
    {kind : Shuttle.Kind}
    {t : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks} (shape : GateRailBlocks p g kind t b)
    {q : Cell (p.W + 1) (p.H + 1)} (hR : q ∈ gateOpenRail p g)
    (hx : q.1.val = p.x g.right - 2) (hq : q ∈ holes t) : 2 ≤ (gateTrainPlacement p g b).right := by
  have hcoord := shape.placement_coordinates
  have hfit := shape.fits
  have hlast := shape.last_length
  have hD := readDepth_readLength_margin p 0 0
  have hx0 := readLength_add_lt_x p g.right 0
  by_contra hn
  apply (PushS.mem_holes _).mp hq
  apply (shape.box_iff hR).mpr
  apply (b.mem_slots _).mpr
  exact Or.inr (Or.inr ⟨by omega, by omega⟩)

end GateRailBlocks

/-- The two canonical target outer payments bound the actual weak gate-rail ends. -/
theorem canonical_gateRail_terminal_outer_payments (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {b : ThreeBlocks} (shape : GateRailBlocks p g kind t b) :
    ((canonicalShuttleTarget l target g).left = false → 2 ≤ (gateTrainPlacement p g b).left) ∧
      ((canonicalShuttleTarget l target g).relay = false → 2 ≤ (gateTrainPlacement p g b).right) := by
  have hports := gate_port_bounds l hl hg hk
  have hleft := (gate_endpoints l hg hk).1
  have hright := (gate_endpoints l hg hk).2
  have hx0 := readLength_add_lt_x p g.left 0
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le haxes) 0
  have hY := readDepth_add_lt_H p 1
  have hD := readDepth_readLength_margin p 0 0
  have hgap := axis_spacing p hports.1
  have hs := placement_gate_shape l hg hk
  have hlevel := gate_level_one l hg hk
  let qL : Cell (p.W + 1) (p.H + 1) := (⟨p.x g.left + 2, by omega⟩, ⟨p.H - readDepth p 1, by omega⟩)
  let qR : Cell (p.W + 1) (p.H + 1) := (⟨p.x g.right - 2, by omega⟩, ⟨p.H - readDepth p 1, by omega⟩)
  have hrowL : qL.2.val = if (gateLeft g).side = .upper then readDepth p (gateLeft g).level
      else p.H - readDepth p (gateLeft g).level := by simp only [gateLeft, hs.1, hlevel, reduceCtorEq, ite_false]; rfl
  have hrowR : qR.2.val = if (gateRight g).side = .upper then readDepth p (gateRight g).level
      else p.H - readDepth p (gateRight g).level := by simp only [gateRight, hs.1, hlevel, reduceCtorEq, ite_false]; rfl
  constructor
  · intro htarget
    have hbit : (if (gateLeft g).inward then (l.canonical target).internal.getD (gateLeft g).internal false
        else !((l.canonical target).internal.getD (gateLeft g).internal false)) = true := by
      change (!((l.canonical target).internal.getD g.internal false)) = false at htarget
      simpa only [gateLeft, ite_true, Bool.not_eq_false_eq_eq_true] using htarget
    have ht := endpoint_second_target l p target (gateLeft g) hleft hbit (q := qL) rfl hrowL
    have hdelta := endpoint_work_delta_of_target_second l p hl hM target (gateLeft g) hleft (q := qL) rfl hrowL ht
    have hhole := canonical_r_horizontal_target_payment l p hl hM haxes initial target hgate (gateLeft g) hleft
      hr accepted hdelta (q := qL) rfl hrowL
    exact shape.left_two_of_second_hole (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [qL]; omega, by dsimp only [qL]; omega⟩) rfl hhole
  · intro htarget
    have hbit : (if (gateRight g).inward then (l.canonical target).internal.getD (gateRight g).internal false
        else !((l.canonical target).internal.getD (gateRight g).internal false)) = true := by
      change (l.canonical target).internal.getD (g.internal + 2) false = false at htarget
      simp only [gateRight, Bool.false_eq_true, ite_false, htarget, Bool.not_false]
    have ht := endpoint_second_target l p target (gateRight g) hright hbit (q := qR) rfl hrowR
    have hdelta := endpoint_work_delta_of_target_second l p hl hM target (gateRight g) hright (q := qR) rfl hrowR ht
    have hhole := canonical_r_horizontal_target_payment l p hl hM haxes initial target hgate (gateRight g) hright
      hr accepted hdelta (q := qR) rfl hrowR
    exact shape.right_two_of_second_hole (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [qR]; omega, by dsimp only [qR]; omega⟩) rfl hhole

end PushPuzzle.Push.AcceptanceSoundness
