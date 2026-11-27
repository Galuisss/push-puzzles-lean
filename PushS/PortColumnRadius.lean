/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryWalks
public import PushS.PortGatePageWindow
import all PushS.PortInterlevelFreeze
import all PushS.PortDeeperBudget
import all PushS.PortEndpointLocality
import all PushS.PortCentralStrip
import all PushS.PortLayoutCoordinates
import all PushS.PortStreetEnumeration
import all PushS.PortSegments
import all PushS.PortGatePageWindow
import all PushS.PortCoreCrossing
import all PushS.PortWalkBudget

/-! Deep crossings near a shallower axis are beyond the actual remaining-hole budget. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The physical page band beyond a level's interlevel depth, near one original port axis. -/
@[expose] def axisDeepBand (p : Scales.Parameters) (side : Side) (port j : ℕ) :
    Set (Cell (p.W + 1) (p.H + 1)) :=
  {q | Nat.dist q.1.val (p.x port) ≤ p.L p.levels + 12 ∧
    (if side = .upper then (readDepth p j + readDepth p (j + 1)) / 2 ≤ q.2.val ∧
        q.2.val ≤ p.Y p.levels + 2
      else p.H - (p.Y p.levels + 2) ≤ q.2.val ∧
        q.2.val ≤ p.H - (readDepth p j + readDepth p (j + 1)) / 2)}

/-- A page axis with no deeper endpoint on that page is separated from every deeper walk
throughout its deep band. -/
theorem axisDeepBand_far (l : PortLayout) (p : Scales.Parameters) (ha : l.portCount ≤ p.axes)
    {side : Side} {port j : ℕ} (hp : port < l.portCount) (hj : 1 ≤ j) (hjM : j < p.levels)
    (howner : ∀ e ∈ l.endpoints, e.side = side → e.port = port → e.level ≤ j)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p side port j) :
    ∀ a ∈ l.deeperWalkHoles p j, p.b j < distance a q := by
  have hqspan : p.x port - columnRadius p ≤ q.1.val ∧ q.1.val ≤ p.x port + columnRadius p := by
    have hx := hq.1
    simp only [Nat.dist, columnRadius] at hx ⊢
    omega
  have ho := budget_outer p (le_of_lt hjM)
  have hm := middle_depth_bounds p hj hjM
  have hH : p.H = 2 * p.D := rfl
  have hband := hq.2
  intro a haP
  rcases Finset.mem_union.mp haP with hframe | hwalk
  · have hleft : p.D ≤ p.x port := by
      have hx := Nat.mul_le_mul_right p.D (show 1 ≤ port + 1 by omega)
      simpa only [Nat.one_mul, Scales.Parameters.x] using hx
    have hright : p.x port + p.D ≤ p.W := by
      have hx := axis_spacing p (hp.trans_le ha)
      simpa only [Scales.Parameters.x, Scales.Parameters.W] using hx
    obtain ⟨d, hd⟩ := (Boundary.mem_frame a).mp hframe
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;>
      cases hs : side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hband <;>
      simp only [distance, Nat.dist_eq_max_sub_min] <;> omega
  · obtain ⟨s, hs, hac⟩ := (SegmentRecipe.mem_holes _ a).mp hwalk
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨he, hlevel⟩ := List.mem_filter.mp he
    have hlevel : j < e.level := of_decide_eq_true hlevel
    have hae : (a.1.val, a.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e) :=
      (mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_take hs, hac⟩
    have haspan := fixed_endpoint_span l p e hae
    have hL := readLength_le_last p e.level
    by_cases hport : e.port = port
    · have hside : e.side ≠ side := fun hs => by have := howner e he hs hport; omega
      have haband := endpoint_page_band l p e hae
      cases hs : side <;> cases hes : e.side <;>
        simp only [hs, hes, ne_eq, reduceCtorEq, not_true_eq_false, ite_true, ite_false] at hside haband hband <;>
        simp only [distance, Nat.dist_eq_max_sub_min] <;> omega
    · apply distinct_axis_far p hport (by omega) ?_ hqspan
      dsimp only [columnRadius]
      omega

private theorem axis_deep_actual_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {side : Side} {port j : ℕ}
    (hp : port < l.portCount) (hj : 1 ≤ j) (hjM : j < p.levels)
    (howner : ∀ e ∈ l.endpoints, e.side = side → e.port = port → e.level ≤ j)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p side port j) :
    ∀ a ∈ l.deeperWalkHoles p j,
      (holes (l.physicalInstance p hl hM ha initial target).initial \ l.deeperWalkHoles p j).card < distance a q := by
  have hb : (holes (l.physicalInstance p hl hM ha initial target).initial \ l.deeperWalkHoles p j).card ≤ p.b j := by
    rw [l.physicalInstance_initial_holes p hl hM ha initial target]
    exact l.encodedSegments_outside_deeperWalk_card_le p hl hM ha initial hj
  exact fun a hap => hb.trans_lt (l.axisDeepBand_far p ha hp hj hjM howner hq a hap)

private theorem ordinary_deep_actual_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p e.side e.port e.level) :
    ∀ a ∈ l.deeperWalkHoles p e.level,
      (holes (l.physicalInstance p hl hM ha initial target).initial \ l.deeperWalkHoles p e.level).card < distance a q := by
  apply axis_deep_actual_far l p hl hM ha initial target (l.endpoints_port_lt hl he)
    (l.endpoints_level_bounds p hl hM he).1 heM ?_ hq
  intro f hf hs hp
  have hfe := l.endpoints_key_injective hl hf he hs hp
  exact hfe ▸ le_rfl

private theorem gate_deep_actual_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hlevels : 1 < p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p .lower middle 1) :
    ∀ a ∈ l.deeperWalkHoles p 1,
      (holes (l.physicalInstance p hl hM ha initial target).initial \ l.deeperWalkHoles p 1).card < distance a q := by
  apply axis_deep_actual_far l p hl hM ha initial target (gate_center_lt l hl hi) le_rfl hlevels ?_ hq
  intro e he hs hp
  obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
  exact False.elim (l.endpoints_lower_ne_gate_middle hl hg he hs (hp.trans hm))

/-- No successful physical player enters the deep band of an actual shallower endpoint axis. -/
theorem physicalInstance_endpoint_deep_unvisited (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p e.side e.port e.level)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) : u.player ≠ q := by
  apply Radius.player_ne_distant
    (l.physicalInstance_deeper_preserving p hl hM ha initial target e.level hsu hut ht)
    (l.physicalInstance_deeperWalk_empty p hl hM ha initial target e.level .refl (hsu.trans hut) ht)
    (Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target))
  exact ordinary_deep_actual_far l p hl hM ha initial target e he heM hq

/-- An initially occupied point in an actual ordinary axis's deep band remains occupied. -/
theorem physicalInstance_endpoint_deep_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p e.side e.port e.level)
    (hbox : q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) : q ∈ u.boxes := by
  by_contra hno
  have hh := Radius.distant_hole_source
    (l.physicalInstance_deeper_preserving p hl hM ha initial target e.level hsu hut ht)
    (l.physicalInstance_deeperWalk_empty p hl hM ha initial target e.level .refl (hsu.trans hut) ht)
    (Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target))
    (ordinary_deep_actual_far l p hl hM ha initial target e he heM hq) ((mem_holes _).mpr hno)
  exact (mem_holes _).mp hh hbox

/-- The lower middle axis of an actual three-port group has no deeper player access. -/
theorem physicalInstance_gate_deep_unvisited (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hlevels : 1 < p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p .lower middle 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) : u.player ≠ q := by
  apply Radius.player_ne_distant
    (l.physicalInstance_deeper_preserving p hl hM ha initial target 1 hsu hut ht)
    (l.physicalInstance_deeperWalk_empty p hl hM ha initial target 1 .refl (hsu.trans hut) ht)
    (Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target))
  exact gate_deep_actual_far l p hl hM ha initial target hi hlevels hq

/-- Initially occupied cells in an actual lower gate axis's deep band remain occupied. -/
theorem physicalInstance_gate_deep_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hlevels : 1 < p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p .lower middle 1)
    (hbox : q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) : q ∈ u.boxes := by
  by_contra hno
  have hh := Radius.distant_hole_source
    (l.physicalInstance_deeper_preserving p hl hM ha initial target 1 hsu hut ht)
    (l.physicalInstance_deeperWalk_empty p hl hM ha initial target 1 .refl (hsu.trans hut) ht)
    (Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target))
    (gate_deep_actual_far l p hl hM ha initial target hi hlevels hq) ((mem_holes _).mpr hno)
  exact (mem_holes _).mp hh hbox

end PushPuzzle.PushS.PortLayout
