/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortRailProjection
public import PushS.TrainInterval
import all PushS.PortWireRail
import all PushS.PortWireIndexing
import all PushS.PortAxisMacro
import all PushS.PortEndpointCrossing
import all PushS.PortLayoutCoordinates
import all PushS.PortSegments

/-! The actual single fixed-length box train between an ordinary WIRE's two axes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe RowLabels

/-- The physical WIRE train length across its full, possibly multi-axis, span. -/
@[expose] def wireTrainLength (p : Scales.Parameters) (g : Placement) : ℕ :=
  p.x g.right - p.x g.left - 4

/-- The canonical first occupied coordinate after the left receiving holes. -/
@[expose] def wireTrainStart (p : Scales.Parameters) (g : Placement) (state : SignalState) : ℤ :=
  (p.x g.left : ℤ) + 2 + (state.internal.getD g.internal false).toNat

private theorem wire_train_margin (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) : p.x g.left + 40 < p.x g.right := by
  have hspacing := axis_spacing p (wire_ports l hl hg hw).1
  have hD := p.outer_distance
  omega

/-- Every actual ordinary WIRE has a nonempty box train of its full span length. -/
theorem wireTrainLength_positive (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) : 0 < wireTrainLength p g := by
  have h := wire_train_margin l p hl hg hw
  unfold wireTrainLength
  omega

private theorem wire_train_interval_inside (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) (state : SignalState) {x : ℤ}
    (hx : x ∈ Finset.Ico (wireTrainStart p g state) (wireTrainStart p g state + wireTrainLength p g)) :
    (p.x g.left : ℤ) < x ∧ x < p.x g.right := by
  have hmargin := wire_train_margin l p hl hg hw
  have hb := Bool.toNat_le (state.internal.getD g.internal false)
  rw [Finset.mem_Ico] at hx
  simp only [wireTrainStart, wireTrainLength] at hx
  omega

/-- Complete canonical WIRE occupancy is exactly its one prescribed consecutive interval. -/
theorem encodedSegments_wire_train_boxes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (BoxMask.keep s (wireOpenRail p g)).boxes ↔
      q.2.val = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) ∧
        (q.1.val : ℤ) ∈ Finset.Ico (wireTrainStart p g state) (wireTrainStart p g state + wireTrainLength p g) := by
  change q ∈ s.boxes ∩ wireOpenRail p g ↔ _
  by_cases hr : q ∈ wireOpenRail p g
  · have hbox : q ∈ s.boxes ↔ q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
      rw [← hholes]
      simp only [mem_holes, not_not]
    have he := Finset.ext_iff.mp (l.encodedSegments_wireOpenRail p hl hM ha state hg hw) q
    simp only [Finset.mem_inter, hr, and_true] at he
    rw [Finset.mem_inter, hbox]
    simp only [hr, and_true]
    rw [he, finite_mem, wire_near_mem, Finset.mem_Ico]
    have hrow := (Finset.mem_filter.mp hr).2
    have hmargin := wire_train_margin l p hl hg hw
    have hb := Bool.toNat_le (state.internal.getD g.internal false)
    have hn := Bool.toNat_le (!(state.internal.getD g.internal false))
    have hsum : (state.internal.getD g.internal false).toNat + (!(state.internal.getD g.internal false)).toNat = 1 := by
      cases state.internal.getD g.internal false <;> decide +kernel
    simp only [wireTrainStart, wireTrainLength]
    omega
  · constructor
    · intro hq
      exact False.elim (hr (Finset.mem_inter.mp hq).2)
    · rintro ⟨hy, hx⟩
      have hb := wire_train_interval_inside l p hl hg hw state hx
      exact False.elim (hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩))

/-- The actual WIRE's canonical line slots are exactly its full fixed-length train interval. -/
theorem encodedSegments_wire_train_slots (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    (lineBoxes .east (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep s (wireOpenRail p g))).image Direction.east.position =
        Finset.Ico (wireTrainStart p g state) (wireTrainStart p g state + wireTrainLength p g) := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact ((l.encodedSegments_wire_train_boxes p hl hM ha state hg hw s hholes q).mp
      (Finset.mem_filter.mp hq).1).2
  · intro hx
    have hb := wire_train_interval_inside l p hl hg hw state hx
    have hxval : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have hxW := x_add_readLength_lt_W p ((wire_ports l hl hg hw).2.trans_le ha) 0
    have hH := readDepth_add_lt_H p g.level
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨x.toNat, by omega⟩, ⟨if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level, by split <;> omega⟩)
    have hq := (l.encodedSegments_wire_train_boxes p hl hM ha state hg hw s hholes q).mpr
      ⟨rfl, by simpa only [q, hxval] using hx⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, hxval⟩

/-- The actual ordinary WIRE consists of one rigid train of its full prescribed span length. -/
structure WireTrainShape (p : Scales.Parameters) (g : Placement)
    (u : State (p.W + 1) (p.H + 1)) (first : ℤ) : Prop where
  /-- Its occupied coordinate slots are exactly this consecutive train. -/
  slots : (u.boxes ∩ wireOpenRail p g).image Direction.east.position = Finset.Ico first (first + wireTrainLength p g)

/-- Every successful physical WIRE prefix preserves its original one-piece train at its original full length. -/
theorem physicalInstance_wire_train_shape (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ first, WireTrainShape p g u first := by
  have hslots := l.encodedSegments_wire_train_slots p hl hM ha initial hg hw
    (l.physicalInstance p hl hM ha initial target).initial (l.physicalInstance_initial_holes p hl hM ha initial target)
  have hpre := l.physicalInstance_wire_admissible_prefix p hl hM ha initial target hg hw hsu hut ht
  obtain ⟨first, hfirst⟩ := interval_admissible (l.wireTrainLength_positive p hl hg hw) (wireTrainStart p g initial) hpre hslots
  refine ⟨first, ?_⟩
  constructor
  change (lineBoxes (w := p.W + 1) (h := p.H + 1) .east
    (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (BoxMask.keep u (wireOpenRail p g))).image Direction.east.position = _ at hfirst
  rw [BoxMask.lineBoxes_keep] at hfirst
  · exact hfirst
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

end PushPuzzle.PushS.PortLayout
