/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateRail
import all PushS.PortGateRail
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortSegments
import all PushS.ShuttleMacroSegments

/-! An actual gate's internal updates preserve the complete board outside its horizontal rail. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem finite_append (p : Scales.Parameters) (ss tt : List Segment)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (ss ++ tt) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ss ∨
        q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) tt := by
  simp only [finite_point_mem, pointHoles_append, Finset.mem_union]

private theorem finite_flatMap (p : Scales.Parameters) {α : Type} (xs : List α)
    (f : α → List Segment) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (xs.flatMap f) ↔
      ∃ a ∈ xs, q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (f a) := by
  simp only [SegmentRecipe.mem_holes, List.mem_flatMap]
  constructor
  · rintro ⟨s, ⟨a, ha, hs⟩, hc⟩
    exact ⟨a, ha, s, hs, hc⟩
  · rintro ⟨a, ha, s, hs, hc⟩
    exact ⟨s, ⟨a, ha, hs⟩, hc⟩

private theorem finite_take_drop (p : Scales.Parameters) (ss : List Segment) (n : ℕ)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ss ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (ss.take n) ∨
        q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (ss.drop n) := by
  conv_lhs => rw [← List.take_append_drop n ss]
  exact finite_append p _ _ q

private theorem endpoint_internal_offRail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {i : ℕ} (hi : i < 3) (b : Bool)
    {e : Endpoint} (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)} (hout : q ∉ gateOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) {state with internal := state.internal.set (g.internal + i) b} e) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (endpointSegments (coordinates p) state e) := by
  by_cases hindex : e.internal = g.internal + i
  · have howner := gate_endpoint_of_internal l hg hk he (by omega) (by omega)
    have hnot (s : SignalState) : q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        ((endpointSegments (coordinates p) s e).drop 1) := by
      intro hq
      apply hout
      apply gateHorizontalSegments_subset_rail l p hl s hg hk
      apply (horizontal_piece_mem p s g kind q).mpr
      rcases howner with rfl | rfl
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
    rw [finite_take_drop p (endpointSegments (coordinates p)
      {state with internal := state.internal.set (g.internal + i) b} e) 1,
      finite_take_drop p (endpointSegments (coordinates p) state e) 1]
    simp only [hnot, or_false]
    have haxis : (endpointSegments (coordinates p)
        {state with internal := state.internal.set (g.internal + i) b} e).take 1 =
        (endpointSegments (coordinates p) state e).take 1 := by
      simp only [endpointSegments, List.take_succ_cons, List.take_zero]
    rw [haxis]
  · have hsame : endpointSegments (coordinates p)
        {state with internal := state.internal.set (g.internal + i) b} e =
        endpointSegments (coordinates p) state e := by
      simp only [endpointSegments, List.getD, List.getElem?_set_ne (Ne.symm hindex)]
    rw [hsame]

private theorem own_core_internal_offRail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (i : ℕ) (b : Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hout : q ∉ gateOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (gateSegments (coordinates p) {state with internal := state.internal.set (g.internal + i) b} kind g.left g.internal) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateSegments (coordinates p) state kind g.left g.internal) := by
  have hnot (s : SignalState) : q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((gateSegments (coordinates p) s kind g.left g.internal).take 2) := by
    intro hq
    exact hout (gateHorizontalSegments_subset_rail l p hl s hg hk
      ((horizontal_piece_mem p s g kind q).mpr (Or.inr (Or.inr hq))))
  rw [finite_take_drop p (gateSegments (coordinates p)
      {state with internal := state.internal.set (g.internal + i) b} kind g.left g.internal) 2,
    finite_take_drop p (gateSegments (coordinates p) state kind g.left g.internal) 2]
  simp only [hnot, false_or]
  have haxis : (gateSegments (coordinates p)
      {state with internal := state.internal.set (g.internal + i) b} kind g.left g.internal).drop 2 =
      (gateSegments (coordinates p) state kind g.left g.internal).drop 2 := by
    simp only [gateSegments, List.drop_succ_cons, List.drop_zero]
  rw [haxis]

private theorem core_internal_offRail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {i : ℕ} (hi : i < 3) (b : Bool)
    {h : Placement} (hh : h ∈ placements l) {q : Cell (p.W + 1) (p.H + 1)} (hout : q ∉ gateOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (tripleSignal (coordinates p) {state with internal := state.internal.set (g.internal + i) b} h) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (tripleSignal (coordinates p) state h) := by
  cases hhk : h.gate with
  | none => simp only [tripleSignal, hhk, Option.elim_none]
  | some other =>
    by_cases hindex : h.internal = g.internal
    · have hsame : h = g := first_slot_owner l hh hg (by omega) (by
        simp only [slotCount, hhk, Option.isSome_some, ite_true]
        omega)
      subst h
      simp only [tripleSignal, hk, Option.elim_some]
      exact own_core_internal_offRail l p hl state hg hk i b hout
    · have h0 := gate_other_internal l hg hk hh hhk hindex hi (j := 0) (by omega)
      have h1 := gate_other_internal l hg hk hh hhk hindex hi (j := 1) (by omega)
      have h2 := gate_other_internal l hg hk hh hhk hindex hi (j := 2) (by omega)
      simp only [Nat.add_zero] at h0
      have hsame : tripleSignal (coordinates p)
          {state with internal := state.internal.set (g.internal + i) b} h = tripleSignal (coordinates p) state h := by
        simp only [tripleSignal, hhk, Option.elim_some, gateSegments, List.getD,
          List.getElem?_set_ne h0.symm, List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]
        rfl
      rw [hsame]

/-- Setting any actual three-port internal bit preserves every emitted hole outside its open rail. -/
theorem encodedSegments_gate_internal_offRail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {i : ℕ} (hi : i < 3) (b : Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hout : q ∉ gateOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.encodedSegments p {state with internal := state.internal.set (g.internal + i) b}) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  simp only [encodedSegments, signalSegments, rawSignals, finite_append, finite_flatMap]
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨e, he, hq⟩
      exact ⟨e, he, (endpoint_internal_offRail l p hl state hg hk hi b he hout).mp hq⟩
    · rintro ⟨e, he, hq⟩
      exact ⟨e, he, (endpoint_internal_offRail l p hl state hg hk hi b he hout).mpr hq⟩
  · constructor
    · rintro ⟨h, hh, hq⟩
      exact ⟨h, hh, (core_internal_offRail l p hl state hg hk hi b hh hout).mp hq⟩
    · rintro ⟨h, hh, hq⟩
      exact ⟨h, hh, (core_internal_offRail l p hl state hg hk hi b hh hout).mpr hq⟩

private theorem core_horizontal_mem_on_row (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (kind : Shuttle.Kind) (q : Cell (p.W + 1) (p.H + 1))
    (hy : q.2.val = p.H - readDepth p 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((gateSegments (coordinates p) state kind g.left g.internal).take 2) ↔
      (p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1)) ∨
      (p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1) + 3 ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + 11 + (state.internal.getD (g.internal + 2) false).toNat) := by
  constructor
  · intro hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    have hcore : q ∈ ShuttleMacro.coreHoles p state kind g.left g.internal :=
      (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_of_mem_take hs, hc⟩
    have hm := (ShuttleMacro.coreHoles_mem p state kind g.left g.internal q).mp hcore
    have hH := readDepth_add_lt_H p 1
    rcases hm with ⟨hh, _⟩ | ⟨hh, _⟩ | ⟨_, _, hh⟩
    · exact Or.inl hh
    · exact Or.inr hh
    · omega
  · intro hq
    apply core_horizontal_of_workrow p state kind g ?_ hy
    apply (ShuttleMacro.coreHoles_mem p state kind g.left g.internal q).mpr
    exact hq.elim (fun hh => Or.inl ⟨hh, hy⟩) (fun hh => Or.inr (Or.inl ⟨hh, hy⟩))

private theorem gate_horizontal_mem_on_row (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind}
    (hk : g.gate = some kind) (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) ↔
      (p.x g.left + 1 ≤ q.1.val ∧ q.1.val ≤ p.x g.left + 1 + (state.internal.getD g.internal false).toNat) ∨
      (p.x g.right - (1 + (!(state.internal.getD (g.internal + 2) false)).toNat) ≤ q.1.val ∧
        q.1.val ≤ p.x g.right - 1) ∨
      (p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1)) ∨
      (p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1) + 3 ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + 11 + (state.internal.getD (g.internal + 2) false).toNat) := by
  rw [horizontal_piece_mem, core_horizontal_mem_on_row p state g kind q hy]
  simp only [finite_point_mem, endpoint_horizontal_mem]
  dsimp only [gateLeft, gateRight]
  simp only [ite_true, Bool.false_eq_true, ite_false, gate_workrow l p hg hk, hy, true_and]

/-- Within an actual open gate rail, the complete encoded holes have their four literal slot/gap intervals. -/
theorem encodedSegments_gateOpenRail_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {q : Cell (p.W + 1) (p.H + 1)}
    (hr : q ∈ gateOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ↔
      (p.x g.left + 1 ≤ q.1.val ∧ q.1.val ≤ p.x g.left + 1 + (state.internal.getD g.internal false).toNat) ∨
      (p.x g.right - (1 + (!(state.internal.getD (g.internal + 2) false)).toNat) ≤ q.1.val ∧
        q.1.val ≤ p.x g.right - 1) ∨
      (p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1)) ∨
      (p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1) + 3 ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + 11 + (state.internal.getD (g.internal + 2) false).toNat) := by
  have heq := l.encodedSegments_gateOpenRail p hl hM ha state hg hk
  have hmem : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) := by
    rw [← heq]
    simp only [Finset.mem_inter, hr, and_true]
  exact hmem.trans (gate_horizontal_mem_on_row l p state hg hk q (Finset.mem_filter.mp hr).2.1)

private theorem outer_transfer_in_rail (l : PortLayout) (p : Scales.Parameters)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1)
    (hx : q.1.val = p.x g.left + 2 ∨ q.1.val = p.x (g.left + 1) + 2 - kind.kappa.toNat ∨
      q.1.val = p.x (g.left + 1) + 12 ∨ q.1.val = p.x g.right - 2) :
    q ∈ gateOpenRail p g := by
  have hs := placement_gate_shape l hg hk
  have hleft := axis_spacing p (show g.left < g.left + 1 by omega)
  have hright := axis_spacing p (show g.left + 1 < g.right by omega)
  have hD := p.outer_distance
  have hkappa : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  have hx0 := readLength_add_lt_x p (g.left + 1) 0
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩

private def outerSlot (g : Placement) (right : Bool) : ℕ :=
  g.internal + if right then 2 else 0

private def outerFirstX (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (right gain : Bool) : ℕ :=
  if right then (if gain then p.x (g.left + 1) + 12 else p.x g.right - 2)
  else if gain then p.x g.left + 2 else p.x (g.left + 1) + 2 - kind.kappa.toNat

private structure GateOuterGeometry (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (kind : Shuttle.Kind) : Prop where
  shape : g.side = .lower ∧ g.right = g.left + 2
  leftGap : p.x g.left + p.D ≤ p.x (g.left + 1)
  rightGap : p.x (g.left + 1) + p.D ≤ p.x g.right
  margin : 4 * (p.b p.levels + p.L p.levels + 10) < p.D
  kappa : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4
  short : 1 ≤ (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) ∧
    (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) ≤ 6
  leftBit : (state.internal.getD g.internal false).toNat ≤ 1
  rightBit : (state.internal.getD (g.internal + 2) false).toNat ≤ 1
  rightNot : (!(state.internal.getD (g.internal + 2) false)).toNat ≤ 1
  centerMargin : readLength p 0 + 64 < p.x (g.left + 1)
  rightMargin : readLength p 0 + 64 < p.x g.right

private theorem gate_outer_geometry (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    GateOuterGeometry p state g kind := by
  have hs := placement_gate_shape l hg hk
  exact ⟨hs, axis_spacing p (by omega), axis_spacing p (by omega), p.outer_distance,
    (by cases kind <;> decide +kernel), (by split <;> decide +kernel), Bool.toNat_le _, Bool.toNat_le _,
    Bool.toNat_le _, readLength_add_lt_x p (g.left + 1) 0, readLength_add_lt_x p g.right 0⟩

private theorem gate_outer_update (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (right gain : Bool)
    (hi : outerSlot g right < state.internal.length)
    (hbefore : state.internal.getD (outerSlot g right) false = !gain)
    (q z : Cell (p.W + 1) (p.H + 1))
    (hqx : q.1.val = outerFirstX p g kind right gain)
    (hzx : z.1.val = outerFirstX p g kind right (!gain))
    (hqy : q.2.val = p.H - readDepth p 1) (hzy : z.2.val = p.H - readDepth p 1) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.encodedSegments p {state with internal := state.internal.set (outerSlot g right) gain}) =
    insert q ((SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)).erase z) := by
  have hqR := outer_transfer_in_rail l p hg hk hqy (by cases right <;> cases gain <;> simp_all [outerFirstX])
  have hzR := outer_transfer_in_rail l p hg hk hzy (by cases right <;> cases gain <;> simp_all [outerFirstX])
  ext r
  by_cases hr : r ∈ gateOpenRail p g
  · have hry := (Finset.mem_filter.mp hr).2.1
    have hqpoint : r = q ↔ r.1.val = outerFirstX p g kind right gain := by
      simp only [Prod.ext_iff, Fin.ext_iff, hqx, hqy, hry, and_true]
    have hzpoint : r = z ↔ r.1.val = outerFirstX p g kind right (!gain) := by
      simp only [Prod.ext_iff, Fin.ext_iff, hzx, hzy, hry, and_true]
    rw [l.encodedSegments_gateOpenRail_mem p hl hM ha
      {state with internal := state.internal.set (outerSlot g right) gain} hg hk hr,
      Finset.mem_insert, Finset.mem_erase, hqpoint]
    simp only [ne_eq, hzpoint]
    rw [l.encodedSegments_gateOpenRail_mem p hl hM ha state hg hk hr]
    have hset0 : (state.internal.set (outerSlot g right) gain).getD g.internal false =
        (if right then state.internal.getD g.internal false else gain) := by
      cases right
      · exact List.getD_set_self hi
      · exact List.getD_set_ne (by dsimp [outerSlot]; omega)
    have hset1 : (state.internal.set (outerSlot g right) gain).getD (g.internal + 1) false =
        state.internal.getD (g.internal + 1) false :=
      List.getD_set_ne (by cases right <;> dsimp [outerSlot] <;> omega)
    have hset2 : (state.internal.set (outerSlot g right) gain).getD (g.internal + 2) false =
        (if right then gain else state.internal.getD (g.internal + 2) false) := by
      cases right
      · exact List.getD_set_ne (by dsimp [outerSlot]; omega)
      · exact List.getD_set_self hi
    obtain ⟨hs, hleft, hright, hD, hkappa, hshort, hleftBit, hrightBit, hrightNot, hx0, hxR⟩ :=
      gate_outer_geometry l p state hg hk
    simp only [hset0, hset1, hset2]
    cases right <;> cases gain <;>
      simp only [outerSlot, outerFirstX, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero,
        Bool.not_false, Bool.not_true] at hbefore ⊢ <;>
      simp only [hbefore, Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true] <;> omega
  · have hqne : r ≠ q := fun h => hr (h ▸ hqR)
    have hzne : r ≠ z := fun h => hr (h ▸ hzR)
    rw [Finset.mem_insert, Finset.mem_erase]
    simp only [hqne, false_or]
    have hoff := l.encodedSegments_gate_internal_offRail p hl state hg hk
      (i := if right then 2 else 0) (by cases right <;> decide +kernel) gain hr
    exact ⟨fun h => ⟨hzne, hoff.mp h⟩, fun h => hoff.mpr h.2⟩

end PushPuzzle.PushS.PortLayout
