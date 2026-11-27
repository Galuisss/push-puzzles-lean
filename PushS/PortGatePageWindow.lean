/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointPageWindow
public import PushS.PortWalkBudget
import all PushS.PortWalkBudget
import all PushS.PortEndpointPageWindow
import all PushS.PortEndpointLocality
import all PushS.PortEndpointWide
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortStreetEnumeration
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual hole sources near a lower three-port middle axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem gate_lower_coordinate (p : Scales.Parameters) (v : ℕ) :
    onSide (coordinates p) .lower v = p.H - v := rfl

/-- The emitter's five special gate columns in their physical order. -/
def gateSpecialColumns (p : Scales.Parameters) (middle : ℕ) : List ℕ :=
  specialColumns (coordinates p) middle

/-- The four emitted public long-column coordinates, in fixed-segment order. -/
def gatePublicColumns (p : Scales.Parameters) (middle : ℕ) : List ℕ :=
  [p.x middle - 2, p.x middle + 6, p.x middle + 8, p.x middle + 12]

/-- Every public gate street is one of the actual five special streets. -/
theorem gatePublicColumn_mem_special (p : Scales.Parameters) {middle z : ℕ}
    (hz : z ∈ gatePublicColumns p middle) : z ∈ gateSpecialColumns p middle := by
  have hc : (coordinates p).x = p.x := rfl
  simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hz
  simp only [gateSpecialColumns, specialColumns, hc, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem gate_public_vertical_bounds (p : Scales.Parameters) {x : ℕ} {q : ℕ × ℕ}
    (hq : (segment x (onSide (coordinates p) .lower 1) x
      (onSide (coordinates p) .lower ((coordinates p).depth 1 - 1))).Contains q) :
    p.H - (readDepth p 1 - 1) ≤ q.2 ∧ q.2 ≤ p.H - 1 := by
  have hv := (vertical_coordinates hq).2
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_H p 1
  have hd : (coordinates p).depth 1 = readDepth p 1 := rfl
  simp only [gate_lower_coordinate, hd] at hv
  constructor <;> omega

/-- The interior lower page within one global branch radius of a gate's actual middle axis. -/
@[expose] def gatePageWindow (p : Scales.Parameters) (middle : ℕ) :
    Set (Cell (p.W + 1) (p.H + 1)) :=
  {q | (p.D + 32 < q.2.val ∧ q.2.val < p.H) ∧
    Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 16}

private theorem gate_center_lt (l : PortLayout) (hl : l.pages.Valid) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) : middle < l.portCount := by
  obtain ⟨kind, first, hg, rfl⟩ := center_gate_mem l hi
  exact gate_middle_lt l hl hg

/-- Once a three-port center occurs, every selected depth is at least its first work row. -/
theorem workingDepthCoordinates_gate_min (l : PortLayout) (p : Scales.Parameters)
    {middle v : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hv : v ∈ l.workingDepthCoordinates p) : readDepth p 1 ≤ v := by
  have hn : (centers l).isEmpty = false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro hempty
    have hi : middle ∈ centers l := hi
    rw [hempty] at hi
    exact List.not_mem_nil hi
  obtain ⟨j, hj, hv⟩ := List.mem_flatMap.mp hv
  change v ∈ (if (centers l).isEmpty then _ else _) at hv
  rw [hn] at hv
  have hm := readDepth_le_level p (show 1 ≤ j + 1 by omega)
  have hjM : j + 1 ≤ p.levels := by have := List.mem_range.mp hj; change j < p.levels at this; omega
  rw [← readDepth_eq p (by omega) hjM] at hm
  change v ∈ [readDepth p (j + 1), readDepth p (j + 1) + 2] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

/-- Near a lower gate center, the actual selected page columns are precisely its own six columns. -/
theorem gatePageColumns_near (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle z : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hz : z ∈ l.pageColumnCoordinates p .lower)
    (hnear : Nat.dist z (p.x middle) ≤ p.L p.levels + 12) :
    z ∈ p.x middle :: gateSpecialColumns p middle := by
  have hm := readLength_add_lt_x p middle p.levels
  have hW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hm hW
  change z ∈ pageColumns l (coordinates p) .lower at hz
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc,
    ite_true] at hz
  change z = 0 ∨ z = p.W ∨ _ at hz
  rcases hz with rfl | rfl | hz | hz
  · simp only [Nat.dist] at hnear
    omega
  · simp only [Nat.dist] at hnear
    omega
  · obtain ⟨e, he, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨he, hs⟩ := List.mem_filter.mp he
    have hs : e.side = .lower := of_decide_eq_true hs
    have hp := nearby_axis_eq p (i := middle) (by omega) (endpoint_columns_span p e hz)
    obtain ⟨kind, first, hg, hcenter⟩ := center_gate_mem l hi
    exact False.elim (l.endpoints_lower_ne_gate_middle hl hg he hs (hp.trans hcenter))
  · obtain ⟨i, _, hz⟩ := List.mem_flatMap.mp hz
    have hp := nearby_axis_eq p (i := middle) (by omega) (center_columns_span p i hz)
    have hc : (coordinates p).x = p.x := rfl
    simpa only [hp, gateSpecialColumns, hc] using hz

/-- Every actual special gate column belongs to the original lower page streets. -/
theorem gateSpecialColumn_mem_page (l : PortLayout) (p : Scales.Parameters)
    {middle z : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hz : z ∈ gateSpecialColumns p middle) : z ∈ l.pageColumnCoordinates p .lower := by
  change z ∈ pageColumns l (coordinates p) .lower
  simp only [pageColumns, List.mem_append, ite_true]
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨middle, hi, List.mem_cons_of_mem _ hz⟩

/-- No special gate street is a principal axis or a frame column. -/
theorem gateSpecialColumn_not_main (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {x : Fin (p.W + 1)} (hx : x.val ∈ gateSpecialColumns p middle) :
    x ∉ l.mainColumnSet p := by
  have hspan := center_columns_span p middle (List.mem_cons_of_mem _ hx)
  have hm := readLength_add_lt_x p middle p.levels
  have hW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hm hW
  have hn : x.val ≠ p.x middle := by
    change x.val ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  intro hxmain
  rcases (l.mainColumnSet_iff p x).mp hxmain with hx0 | hxW | ⟨i, _, hxi⟩
  · dsimp only [columnRadius] at hspan
    omega
  · dsimp only [columnRadius] at hspan
    omega
  · have hp : i = middle := nearby_axis_eq p (i := middle) (k := i) (z := x.val) (by dsimp only [columnRadius] at hspan; simp only [Nat.dist]; omega)
      (by rw [← hxi]; omega)
    exact hn (hxi.trans (congrArg p.x hp))

/-- Every original fixed gate segment survives the emitter's conditional even rounding. -/
theorem gateFixedSegments_mem_fixed (l : PortLayout) (p : Scales.Parameters)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {s : Segment}
    (hs : s ∈ gateFixedSegments (coordinates p) middle) : s ∈ l.fixedSegments p := by
  have hb : s ∈ interiorFixed l (coordinates p) := by
    simp only [interiorFixed, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨middle, hi, hs⟩)))
  change s ∈ frame (coordinates p) ++ markedInterior l (coordinates p)
  apply List.mem_append_right
  simp only [markedInterior, List.mem_append, or_assoc]
  left
  rw [roundedInterior_eq]
  exact List.mem_map.mpr ⟨s, hb, rounded_gate l p middle hs⟩

/-- Actual fixed holes near this middle axis, or actual core signals with this middle owner. -/
inductive GateHoleSource (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (middle : ℕ) (q : ℕ × ℕ) : Prop
  | fixed (contains : q ∈ pointHoles (gateFixedSegments (coordinates p) middle))
  | signal {kind : Shuttle.Kind} {first internal : ℕ}
      (gate : .gate kind first ∈ l.lowerGroups) (center : first + 1 = middle)
      (contains : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal))

/-- Coordinate classes of the actual fixed gate pieces. -/
inductive GateFixedLocation (p : Scales.Parameters) (middle : ℕ) (q : ℕ × ℕ) : Prop
  | publicStreet (column : q.1 ∈ gatePublicColumns p middle)
      (depth : p.H - (readDepth p 1 - 1) ≤ q.2 ∧ q.2 ≤ p.H - 1)
  | privateCap (column : q.1 = p.x middle + 4) (row : q.2 = p.H - (readDepth p 1 + 1))
  | privateBranch (row : q.2 = p.H - (readDepth p 1 + 2))
      (span : p.x middle + 1 ≤ q.1 ∧ q.1 ≤ p.x middle + 4)
  | halfDepth (row : q.2 = p.H - readDepth p 1 / 2)
  | marker (levels : 1 < p.levels) (column : q.1 ∈ gateSpecialColumns p middle)
      (row : q.2 = p.H - (readDepth p 1 + readDepth p 2) / 2)

/-- Reading an actual fixed source yields its public, private, half-depth or marker coordinates. -/
theorem gateFixedSegments_location (p : Scales.Parameters) (middle : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) middle)) : GateFixedLocation p middle q := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hq
  have hd : (coordinates p).depth 1 = readDepth p 1 := rfl
  have hc : (coordinates p).x = p.x := rfl
  dsimp only [gateFixedSegments] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    apply GateFixedLocation.publicStreet ?_ (gate_public_vertical_bounds p hq)
    have hxq := (vertical_coordinates hq).1
    rw [hxq]
    simpa only [gatePublicColumns, hc] using hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · have hp := point_coordinates hq
      simp only [gate_lower_coordinate, hd, hc] at hp
      exact .privateCap hp.1 hp.2
    · have hp := horizontal_coordinates hq
      simp only [gate_lower_coordinate, hd, hc] at hp
      exact .privateBranch hp.1 ⟨by omega, by omega⟩
    · exact .halfDepth (by simpa only [gate_lower_coordinate, hd] using (point_coordinates hq).2)
    · exact .halfDepth (by simpa only [gate_lower_coordinate, hd] using (point_coordinates hq).2)
  · split at hs
    · rename_i hlevels
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      have hp := point_coordinates hq
      refine .marker hlevels ?_ hp.2
      rw [hp.1]
      exact hx
    · cases hs

/-- The actual horizontal work-row holes or middle-axis near holes of a gate signal. -/
inductive GateSignalLocation (p : Scales.Parameters) (middle : ℕ) (q : ℕ × ℕ) : Prop
  | horizontal (row : q.2 = p.H - readDepth p 1)
  | axis (column : q.1 = p.x middle)
      (depth : p.H - (readDepth p 1 + 2) ≤ q.2 ∧ q.2 ≤ p.H - (readDepth p 1 + 1))

/-- Every literal core signal hole lies on its work row or its middle-axis near segment. -/
theorem gateSegments_location (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) :
    GateSignalLocation p (first + 1) q := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hq
  have hd : (coordinates p).depth 1 = readDepth p 1 := rfl
  have hc : (coordinates p).x = p.x := rfl
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  dsimp only [gateSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact .horizontal (by simpa only [gate_lower_coordinate, hd] using (horizontal_coordinates hq).1)
  · exact .horizontal (by simpa only [gate_lower_coordinate, hd] using (horizontal_coordinates hq).1)
  · have hp := vertical_coordinates hq
    have hb := Bool.toNat_le (state.axes.getD (first + 1) false)
    simp only [gate_lower_coordinate, hd, hc] at hp
    exact .axis hp.1 ⟨by omega, by omega⟩

private theorem gate_window_not_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ gatePageWindow p middle) : q ∉ Boundary.frame := by
  have hm := readLength_add_lt_x p middle p.levels
  have hW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hm hW
  have hx := hw.2
  have hy := hw.1
  simp only [Nat.dist] at hx
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega

private theorem gate_window_not_wide (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ gatePageWindow p middle) : q ∉ l.wideSeparatorHoles p := by
  have hm := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) 0
  let col : Fin (p.W + 1) := ⟨p.x middle, by omega⟩
  have hc : col ∈ l.streetColumnSet p := axis_in_streetColumns l p (gate_center_lt l hl hi)
  intro hwide
  have hfar := l.wideSeparatorHoles_street_gap p hl hwide col hc
  have hb := local_radius_budget p p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hb
  have hnear := hw.2
  change 2 * p.b p.levels + 2 < Nat.dist q.1.val (p.x middle) at hfar
  omega

private theorem gate_window_no_endpoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ gatePageWindow p middle)
    (e : Endpoint) (he : e ∈ l.endpoints)
    (hsource : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e) ∨
      (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) state e)) : False := by
  have hport : e.port = middle := nearby_axis_eq p hw.2 (by
    have hs := endpoint_source_near l p state e hsource
    simp only [Nat.dist] at hs
    omega)
  have hside : e.side = .lower := by
    have hp := hsource.elim (fixed_endpoint_page l p e) (signal_endpoint_page p state e)
    have hpage := hw.1.1
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hp ⊢; omega
  obtain ⟨kind, first, hg, hcenter⟩ := center_gate_mem l hi
  exact l.endpoints_lower_ne_gate_middle hl hg he hside (hport.trans hcenter)

/-- Every complete-board hole in a gate page window belongs to that gate's own physical core. -/
theorem encodedSegments_gatePageWindow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ gatePageWindow p middle)
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    GateHoleSource l p state middle (q.1.val, q.2.val) := by
  rcases encoded_sources l p hl hM state hq (gate_window_not_frame l p hl ha hi hw) with
    hc | hwide | ⟨e, he, hsource⟩ | ⟨kind, first, hg, hsource⟩
  · have hy := (Finset.mem_filter.mp hc).2
    have hpage := hw.1.1
    omega
  · exact False.elim (gate_window_not_wide l p hl ha hi hw hwide)
  · exact False.elim (gate_window_no_endpoint l p hl state hi hw e he hsource)
  · have hspan : p.x (first + 1) - 2 ≤ q.1.val ∧ q.1.val ≤ p.x (first + 1) + 12 := by
      rcases hsource with hs | ⟨internal, hs⟩
      · exact gate_fixed_span p _ hs
      · exact gate_signal_span p state kind first internal hs
    have hcenter : first + 1 = middle := nearby_axis_eq p hw.2 (by omega)
    rcases hsource with hs | ⟨internal, hs⟩
    · exact .fixed (by simpa only [hcenter] using hs)
    · exact .signal hg hcenter hs

end PushPuzzle.PushS.PortLayout
