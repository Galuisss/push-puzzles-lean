/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramNarrowSignals
public import Push.AcceptanceProgramWhole
public import PushS.PortGatePageWindow
import all PushS.PortEndpointLocality
import all PushS.PortWideGeometry
import all PushS.PortSegments
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals

/-! Page and level ownership of the actual target stock used by the later acceptance rounds. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- The actual private columns selected by the lower-page emitter. -/
def privateColumns (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  (((pageColumns l p .lower).filter PageColumn.privateColumn).map PageColumn.column).toFinset

/-- The lower gate's actual four-hole private-column prefix. -/
def privateRound (l : PortLayout) (p : Scales.Parameters) : Template :=
  .read .south (prefixRequests (privateColumns l p) fun _ => p.Y 1 + 3)

/-- The core-axis prefix occurring inside the combined ordinary/core-axis round. -/
def corePrefixRound (l : PortLayout) (p : Scales.Parameters) : Template :=
  .read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1)

/-- An actual interlevel marker, retaining its emitted page, column, and level. -/
def InterlevelMarker (l : PortLayout) (p : Scales.Parameters) (side : Side)
    (q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  ∃ a ∈ pageColumns l p side, 1 ≤ a.level ∧ a.level < p.levels ∧
    q.1.val = a.column ∧ pageDepth p side q = trimDepth p a.level

/-- Literal coordinate classes of all target holes after removing the frame. -/
inductive Stock (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) : Prop
  | work (row : q.2.val ∈ workRows l p)
  | trim (side : Side) (contains : q ∈ (trimRound l p side).region)
  | main (side : Side) (contains : q ∈ (mainRound l p side).region)
  | privateCap (contains : q ∈ (privateRound l p).region)
  | coreNear (contains : q ∈ (corePrefixRound l p).region)
  | interlevel (side : Side) (marker : InterlevelMarker l p side q)
  | half (row : q.2.val = p.H - p.Y 1 / 2)
      (column : q.1.val ∈ cores l p ∪ privateColumns l p)
  | central (band : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4)

/-- Both selected rows at every allocated level occur literally in the working-row stock. -/
theorem level_work_rows (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    (if side = .upper then p.Y j else p.H - p.Y j) ∈ workRows l p ∧
    (if side = .upper then p.Y j + 2 else p.H - (p.Y j + 2)) ∈ workRows l p := by
  obtain ⟨hwork, hbranch⟩ := l.workingDepthCoordinates_mem p (j - 1) (by omega)
  have hindex : j - 1 + 1 = j := by omega
  rw [hindex, readDepth_eq p hj hjm] at hwork hbranch
  exact ⟨working_row_mem l p side hwork, working_row_mem l p side hbranch⟩

/-- The emitter really selects every gate's private +4 column. -/
theorem gate_private_column (l : PortLayout) (p : Scales.Parameters) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) : p.x middle + 4 ∈ privateColumns l p := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨⟨p.x middle + 4, 1, true⟩, ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨?_, rfl⟩
  unfold pageColumns
  apply List.mem_append_right
  rw [ite_eq_left rfl]
  apply List.mem_flatMap.mpr
  refine ⟨middle, hi, ?_⟩
  simp

/-- Every literal gate center is in the emitted core-axis set. -/
theorem gate_core_column (l : PortLayout) (p : Scales.Parameters) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) : p.x middle ∈ cores l p := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨middle, hi, rfl⟩

/-- Coordinate test for the private column prefix. -/
theorem private_region (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (privateRound l p).region ↔ q.1.val ∈ privateColumns l p ∧ p.H - q.2.val < p.Y 1 + 3 := by
  simp only [privateRound, Template.region, mem_readRegion,
    Direction.lane, prefixRank, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨i, n⟩, hrequest, hx, hy⟩
    obtain ⟨hi, hn⟩ := (mem_prefixRequests _ _ i n).mp hrequest
    refine ⟨hx.symm ▸ hi, ?_⟩
    simpa only [Prod.snd, hn] using hy
  · rintro ⟨hx, hy⟩
    exact ⟨(q.1.val, p.Y 1 + 3), (mem_prefixRequests _ _ _ _).mpr ⟨hx, rfl⟩, rfl, hy⟩

set_option maxRecDepth 2048 in
/-- Coordinate test for the core-axis prefix. -/
private theorem core_prefix_region (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1)
    (p.H + 1)) :
    q ∈ (corePrefixRound l p).region ↔ q.1.val ∈ cores l p ∧ q.2.val < p.H - p.Y 1 := by
  simp only [corePrefixRound, Template.region, mem_readRegion, Direction.lane, prefixRank]
  constructor
  · rintro ⟨⟨i, n⟩, hrequest, hx, hy⟩
    obtain ⟨hi, hn⟩ := (mem_prefixRequests _ _ i n).mp hrequest
    refine ⟨hx.symm ▸ hi, ?_⟩
    simpa only [Prod.snd, hn] using hy
  · rintro ⟨hx, hy⟩
    exact ⟨(q.1.val, p.H - p.Y 1), (mem_prefixRequests _ _ _ _).mpr ⟨hx, rfl⟩, rfl, hy⟩

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem endpoint_fixed_stock (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) : Stock l p q := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hq
  by_cases hs2 : s ∈ (endpointFixedSegments l (coordinates p) e).take 2
  · exact .trim e.side (endpoint_corridors_trim l p hl hM e he ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs2, hc⟩))
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · exact False.elim (hs2 (by simp [endpointFixedSegments]))
  · exact False.elim (hs2 (by simp [endpointFixedSegments]))
  · apply Stock.work
    have hy := (horizontal_coordinates hc).1
    change q.2.val = onSide (coordinates p) e.side (readDepth p e.level + 2) at hy
    rw [readDepth_eq p hj hjm] at hy
    rw [hy]
    exact (level_work_rows l p e.side hj hjm).2
  · obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    all_goals
      split at hs
      next hsel =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        apply Stock.work
        have hy := (point_coordinates hc).2
        dsimp only at hy
        rw [hy]
        exact working_row_mem l p e.side (by simpa only [workingDepthCoordinates] using hv)
      next hsel => cases hs
  · split at hs
    next hlevel =>
      have hlevel' : e.level < p.levels := hlevel
      have hread : (depthTable p).getD e.level 0 = p.Y e.level := readDepth_eq p hj hjm
      have hnext : (depthTable p).getD (e.level + 1) 0 = p.Y (e.level + 1) :=
        readDepth_eq p (by omega) (by omega)
      have hH0 := readDepth_add_lt_H p e.level
      have hH1 := readDepth_add_lt_H p (e.level + 1)
      rw [readDepth_eq p hj hjm] at hH0
      rw [readDepth_eq p (by omega) (by omega : e.level + 1 ≤ p.levels)] at hH1
      have hmark (street : EndpointStreet)
          (hx : q.1.val = street.column p e)
          (hy : q.2.val = onSide (coordinates p) e.side
            (((coordinates p).depth e.level + (coordinates p).depth (e.level + 1)) / 2)) :
          Stock l p q := by
        apply Stock.interlevel e.side
        obtain ⟨a, ha, hx', hla, _⟩ := endpoint_trim_column l p e he street
        refine ⟨a, ha, hla.symm ▸ hj, hla.symm ▸ hlevel', hx.trans hx'.symm, ?_⟩
        rw [hla, trimDepth, ite_eq_left hlevel']
        cases hside : e.side <;>
          simp only [pageDepth, hside, reduceCtorEq, ite_true, ite_false, onSide,
            coordinates, Coordinates.depth, hread, hnext] at hy ⊢ <;> omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hmark .f (point_coordinates hc).1 (point_coordinates hc).2
      · exact hmark .r (point_coordinates hc).1 (point_coordinates hc).2
    next hlevel => cases hs

private theorem endpoint_signal_stock (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) (e : Endpoint)
    (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) state e)) : Stock l p q := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hb := acceptanceEndpointSignalBand p state e hq
  rw [readDepth_eq p hj hjm] at hb
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hq
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have hx : q.1.val = p.x e.port := by
      simp only [segment, Segment.Contains, min_self, max_self, coordinates, Coordinates.x,
        Scales.Parameters.x] at hc ⊢
      omega
    by_cases hrow : q.2.val = if e.side = .upper then p.Y e.level + 2 else p.H - (p.Y e.level + 2)
    · exact .work (hrow.symm ▸ (level_work_rows l p e.side hj hjm).2)
    · apply Stock.main e.side
      apply endpoint_main_region l p e he hx
      have hH := readDepth_add_lt_H p e.level
      rw [readDepth_eq p hj hjm] at hH
      cases hside : e.side <;>
        simp only [hside, pageDepth, reduceCtorEq, ite_true, ite_false] at hb hrow ⊢ <;> omega
  · apply Stock.work
    have hy := (horizontal_coordinates hc).1
    change q.2.val = onSide (coordinates p) e.side (readDepth p e.level) at hy
    rw [readDepth_eq p hj hjm] at hy
    rw [hy]
    exact (level_work_rows l p e.side hj hjm).1

private theorem gate_fixed_stock (l : PortLayout) (p : Scales.Parameters) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (gateFixedSegments (coordinates p) middle)) : Stock l p q := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hq
  by_cases hs4 : s ∈ (gateFixedSegments (coordinates p) middle).take 4
  · exact .trim .lower (gate_corridors_trim l p middle hi ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs4, hc⟩))
  rw [← List.take_append_drop 4 (gateFixedSegments (coordinates p) middle), List.mem_append] at hs
  rcases hs with hs | hs
  · exact False.elim (hs4 hs)
  have hread : (depthTable p).getD 1 0 = p.Y 1 := readDepth_eq p le_rfl p.levels_pos
  dsimp only [gateFixedSegments] at hs
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.mem_cons] at hs
  rcases hs with rfl | hbranch | rfl | rfl | hmarkers
  · apply Stock.privateCap
    apply (private_region l p q).mpr
    have hp := point_coordinates hc
    simp only [onSide, reduceCtorEq, ite_false, coordinates, Coordinates.x, Coordinates.depth, hread] at hp
    refine ⟨hp.1.symm ▸ gate_private_column l p hi, ?_⟩
    have hH := readDepth_add_lt_H p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hH
    omega
  · subst s
    apply Stock.work
    have hy := (horizontal_coordinates hc).1
    change q.2.val = onSide (coordinates p) .lower (readDepth p 1 + 2) at hy
    rw [readDepth_eq p le_rfl p.levels_pos] at hy
    rw [hy]
    exact (level_work_rows l p .lower le_rfl p.levels_pos).2
  · have hp := point_coordinates hc
    simp only [onSide, reduceCtorEq, ite_false, coordinates, Coordinates.x, Coordinates.depth, hread] at hp
    exact .half hp.2 (Finset.mem_union_left _ (hp.1.symm ▸ gate_core_column l p hi))
  · have hp := point_coordinates hc
    simp only [onSide, reduceCtorEq, ite_false, coordinates, Coordinates.x, Coordinates.depth, hread] at hp
    exact .half hp.2 (Finset.mem_union_right _ (hp.1.symm ▸ gate_private_column l p hi))
  · split at hmarkers
    next hlevel =>
      obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp hmarkers
      have hp := point_coordinates hc
      have hlevel' : 1 < p.levels := hlevel
      have hnext : (depthTable p).getD 2 0 = p.Y 2 := readDepth_eq p (by omega) (by omega)
      have hcol' : (⟨col, 1, decide (col = p.x middle + 4)⟩ : Push.AcceptanceProgram.PageColumn) ∈
          Push.AcceptanceProgram.pageColumns l p .lower := by
        unfold Push.AcceptanceProgram.pageColumns
        apply List.mem_append_right
        rw [ite_eq_left rfl]
        apply List.mem_flatMap.mpr
        refine ⟨middle, hi, ?_⟩
        have hx0 := readLength_add_lt_x p middle 0
        change col ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hcol
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol ⊢
        rcases hcol with rfl | rfl | rfl | rfl | rfl <;> simp
        omega
      apply Stock.interlevel .lower
      refine ⟨_, hcol', le_rfl, hlevel', hp.1, ?_⟩
      have hH := readDepth_add_lt_H p 2
      rw [readDepth_eq p (by omega) (by omega)] at hH
      have hH0 := readDepth_add_lt_H p 1
      rw [readDepth_eq p le_rfl p.levels_pos] at hH0
      simp only [pageDepth, reduceCtorEq, ite_false, trimDepth, ite_eq_left hlevel',
        onSide, coordinates, Coordinates.depth, hread, hnext, Nat.reduceAdd] at hp ⊢
      omega
    next hlevel => cases hmarkers

set_option maxRecDepth 2048 in
private theorem gate_signal_stock (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) (hg : .gate kind first ∈ l.lowerGroups)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) : Stock l p q := by
  have hi : first + 1 ∈ l.gateCenterCoordinates := by
    change first + 1 ∈ centers l
    exact List.mem_filterMap.mpr ⟨.gate kind first, hg, rfl⟩
  cases gateSegments_location p state kind first internal hq with
  | horizontal hy =>
    dsimp only at hy
    rw [readDepth_eq p le_rfl p.levels_pos] at hy
    apply Stock.work
    rw [hy]
    exact (level_work_rows l p .lower le_rfl p.levels_pos).1
  | axis hx hb =>
    dsimp only at hx hb
    rw [readDepth_eq p le_rfl p.levels_pos] at hb
    by_cases hbranch : q.2.val = p.H - (p.Y 1 + 2)
    · apply Stock.work
      rw [hbranch]
      exact (level_work_rows l p .lower le_rfl p.levels_pos).2
    · apply Stock.coreNear
      apply (core_prefix_region l p q).mpr
      have hH := readDepth_add_lt_H p 1
      rw [readDepth_eq p le_rfl p.levels_pos] at hH
      exact ⟨hx.symm ▸ gate_core_column l p hi, by omega⟩

/-- Every real off-frame target hole has its working, page, private, marker, or central source. -/
theorem acceptanceStock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hf : q ∉ Boundary.frame) : Stock l p q := by
  rcases encoded_sources l p hl hM state hq hf with hc | hw | ⟨e, he, hs⟩ | ⟨kind, first, hg, hs⟩
  · exact .central (Finset.mem_filter.mp hc).2
  · obtain ⟨side, y, hy, he⟩ := l.wideSeparatorHoles_depth p hw
    exact .work (he.symm ▸ working_row_mem l p side hy)
  · exact hs.elim (endpoint_fixed_stock l p hl hM e he) (endpoint_signal_stock l p hl hM state e he)
  · have hi : first + 1 ∈ l.gateCenterCoordinates := by
      change first + 1 ∈ centers l
      exact List.mem_filterMap.mpr ⟨.gate kind first, hg, rfl⟩
    rcases hs with hs | ⟨internal, hs⟩
    · exact gate_fixed_stock l p hi hs
    · exact gate_signal_stock l p state kind first internal hg hs

end PushPuzzle.PushS.PortLayout
