/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockSlots
import all Push.AcceptanceProgramLayout
import all PushS.EndpointWalking
import all PushS.PortWireRail
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! Only the two literal r-work cells prepay an ordinary WIRE's R23 inventory. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- The actual left ordinary endpoint of a selected WIRE. -/
@[expose] def wireWorkLeft (g : Placement) : Endpoint :=
  ⟨g.side, g.left, true, g.level, g.internal⟩

/-- The actual right ordinary endpoint of a selected WIRE. -/
@[expose] def wireWorkRight (g : Placement) : Endpoint :=
  ⟨g.side, g.right, false, g.level, g.internal⟩

/-- The actual canonical r-column hole on this endpoint's own work row. -/
@[expose] def endpointRWorkSlot (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (e : Endpoint) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (targetHoles l p target).filter fun q => q.1.val = EndpointStreet.r.column p e ∧
    pageDepth p e.side q = p.Y e.level

/-- The zero-or-one canonical work-hole payment at one endpoint. -/
@[expose] def endpointWorkDelta (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (e : Endpoint) : ℕ :=
  (endpointRWorkSlot l p target e).card

/-- One physical r-work coordinate contains at most one canonical hole. -/
theorem endpointWorkDelta_le_one (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (e : Endpoint) :
    endpointWorkDelta l p target e ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  obtain ⟨_, hqx, hqy⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, hrx, hry⟩ := Finset.mem_filter.mp hr
  apply Prod.ext (Fin.ext (hqx.trans hrx.symm))
  apply Fin.ext
  have hqH := q.2.isLt
  have hrH := r.2.isLt
  cases hs : e.side <;> simp only [hs, pageDepth, ite_true, reduceCtorEq, ite_false] at hqy hry <;> omega

private theorem trimRound_mem_wireWorkPrefix (l : PortLayout) (p : Scales.Parameters)
    (target : List Bool) (side : Side) : trimRound l p side ∈ wireWorkPrefix l p target := by
  cases side <;> simp [wireWorkPrefix, schedule, preparation, frameSchedule]

private theorem wire_r_slot_paid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (target : List Bool) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target ∩ wireOpenRail p g)
    (hr : q.1.val = p.x g.left + 2 ∨ q.1.val + 2 = p.x g.right) :
    q ∈ wireWorkPaid l p target g := by
  have hrow := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2.1
  have hb := placement_level_bounds l hl hg
  have hM' := hb.2.trans hM
  have hH := readDepth_add_lt_H p g.level
  rw [readDepth_eq p hb.1 hM'] at hrow hH
  have hdepth : pageDepth p g.side q = p.Y g.level := by
    cases hs : g.side <;> simp only [hs, pageDepth, ite_true, reduceCtorEq, ite_false] at hrow ⊢ <;> omega
  apply Finset.mem_inter.mpr
  refine ⟨hq, (mem_allRegions _ q).mpr ⟨trimRound l p g.side, trimRound_mem_wireWorkPrefix l p target g.side, ?_⟩⟩
  obtain ⟨hl', hr'⟩ := wire_endpoints l hg hw
  rcases hr with hx | hx
  · exact endpoint_column_trim l p hl hM (wireLeft g) hl' .r q hx (by simpa only [wireLeft] using hdepth.le.trans (by omega))
  · have hxx : q.1.val = EndpointStreet.r.column p (wireRight g) := by
      change q.1.val = p.x g.right - 2
      omega
    exact endpoint_column_trim l p hl hM (wireRight g) hr' .r q hxx (by simpa only [wireRight] using hdepth.le.trans (by omega))

/-- The original canonical r-work cells are exactly all earlier payments from this actual WIRE. -/
theorem wireWorkPaid_eq_r_slots (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    wireWorkPaid l p target g =
      (targetHoles l p target ∩ wireOpenRail p g).filter
        (fun q => q.1.val = p.x g.left + 2 ∨ q.1.val + 2 = p.x g.right) := by
  ext q
  constructor
  · intro hq
    obtain ⟨ht, hmask⟩ := Finset.mem_inter.mp hq
    refine Finset.mem_filter.mpr ⟨ht, ?_⟩
    by_contra hn
    have hnear : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p (l.canonical target) g) := by
      rw [← l.encodedSegments_wireOpenRail p hl hM haxes (l.canonical target) hg hw]
      exact ht
    have hnq := (wire_near_mem p (l.canonical target) g _).mp ((finite_mem p _ q).mp hnear)
    have hbit := Bool.toNat_le ((l.canonical target).internal.getD g.internal false)
    have hneg := Bool.toNat_le (!((l.canonical target).internal.getD g.internal false))
    have hxR := readLength_add_lt_x p g.right 0
    have hunit : q.1.val = p.x g.left + 1 ∨ q.1.val + 1 = p.x g.right := by
      rcases hnq.2 with hL | hR
      · left
        omega
      · right
        omega
    have hs := wire_unit_slot_survives l p hl hM haxes target hg hw ht hunit
    exact (Finset.mem_sdiff.mp (by simpa only [wireWorkReference, emit_remaining] using hs)).2 hmask
  · intro hq
    obtain ⟨ht, hr⟩ := Finset.mem_filter.mp hq
    exact wire_r_slot_paid l p hl hM target hg hw ht hr

/-- The two endpoint work-hole stocks are exactly the actual earlier WIRE payment. -/
theorem wireWorkPaid_eq_endpoint_slots (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    wireWorkPaid l p target g =
      endpointRWorkSlot l p target (wireWorkLeft g) ∪ endpointRWorkSlot l p target (wireWorkRight g) := by
  have hb := placement_level_bounds l hl hg
  have hgM := hb.2.trans hM
  have hY := readDepth_add_lt_H p g.level
  rw [readDepth_eq p hb.1 hgM] at hY
  have hp := wire_ports l hl hg hw
  have hgap := axis_spacing p hp.1
  have hD := p.outer_distance
  rw [wireWorkPaid_eq_r_slots l p hl hM haxes target hg hw]
  ext q
  have hrow : q.2.val = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) ↔
      pageDepth p g.side q = p.Y g.level := by
    have hqH := q.2.isLt
    rw [readDepth_eq p hb.1 hgM]
    cases g.side <;> simp only [pageDepth, ite_true, reduceCtorEq, ite_false]
    omega
  simp only [endpointRWorkSlot, Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
  change ((q ∈ targetHoles l p target ∧ q ∈ wireOpenRail p g) ∧
      (q.1.val = p.x g.left + 2 ∨ q.1.val + 2 = p.x g.right)) ↔
    (q ∈ targetHoles l p target ∧ q.1.val = p.x g.left + 2 ∧ pageDepth p g.side q = p.Y g.level) ∨
      (q ∈ targetHoles l p target ∧ q.1.val = p.x g.right - 2 ∧ pageDepth p g.side q = p.Y g.level)
  constructor
  · rintro ⟨⟨ht, hr⟩, hx⟩
    have hy := hrow.mp (Finset.mem_filter.mp hr).2.1
    rcases hx with hx | hx
    · exact Or.inl ⟨ht, hx, hy⟩
    · exact Or.inr ⟨ht, by omega, hy⟩
  · rintro (⟨ht, hx, hy⟩ | ⟨ht, hx, hy⟩)
    · exact ⟨⟨ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow.mpr hy, by omega, by omega⟩⟩, Or.inl hx⟩
    · exact ⟨⟨ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow.mpr hy, by omega, by omega⟩⟩, Or.inr (by omega)⟩

/-- The exact earlier WIRE payment is the sum of its two canonical zero-or-one endpoint payments. -/
theorem wireWorkPaid_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    (wireWorkPaid l p target g).card =
      endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g) := by
  rw [wireWorkPaid_eq_endpoint_slots l p hl hM haxes target hg hw, Finset.card_union_of_disjoint]
  · rfl
  · apply Finset.disjoint_left.mpr
    intro q hL hR
    have hL := (Finset.mem_filter.mp hL).2.1
    have hR := (Finset.mem_filter.mp hR).2.1
    change q.1.val = p.x g.left + 2 at hL
    change q.1.val = p.x g.right - 2 at hR
    have hg := axis_spacing p (wire_ports l hl hg hw).1
    have hD := p.outer_distance
    omega

/-- The exact full-row ledger written with the literal endpoint work-hole payments. -/
theorem wireWork_row_card_deltas (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (hordinary : side = .upper ∨ 2 ≤ j) :
    ((wireWorkReference l p target).filter (fun q => q.2.val = wireWorkRow p side j)).card +
        ∑ g ∈ wireRowPlacements l side j,
          (endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g)) =
      (wireRowFixedStock l p side j).card + 3 * (wireRowPlacements l side j).card := by
  classical
  convert wireWork_row_card l p hl hM haxes target side hj hjm hordinary using 2
  apply Finset.sum_congr rfl
  intro g hg
  obtain ⟨hg, hw, _, _⟩ := Finset.mem_filter.mp hg
  exact (wireWorkPaid_card l p hl hM haxes target (List.mem_toFinset.mp hg) hw).symm

end PushPuzzle.Push.AcceptanceProgram
