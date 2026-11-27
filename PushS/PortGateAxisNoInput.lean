/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxis
public import PushS.PortGateBlockers
public import PushS.PortUpperAxisNoInput
import all PushS.PortGatePrivateWalk
import all PushS.PortGatePageWindow
import all PushS.PortAxisFixed
import all PushS.PortEndpointFStock
import all PushS.PortCoreCrossing
import all PushS.PortCentralStrip
import all PushS.PortStreetSeparation
import all PushS.PortBackground
import all PushS.PortSegments

/-! The actual four-hole middle-axis segment cannot receive boxes from a three-port work row. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem gate_deep_axis_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle depth : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hv : depth ∈ l.workingDepthCoordinates p) (hdeep : readDepth p 1 + 2 < depth)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x middle) (hy : q.2.val = p.H - depth) :
    q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  have hmax := workingRows_le_last l p hv
  have hD := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hx0 := readLength_add_lt_x p middle 0
  have hw : q ∈ gatePageWindow p middle := ⟨⟨by omega, by omega⟩, by rw [hx, Nat.dist_self]; omega⟩
  by_contra hbox
  have hh := (mem_holes q).mpr hbox
  have hinit : holes ((l.physicalInstance p hl hM ha initial target).initial : State (p.W + 1) (p.H + 1)) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) :=
    l.physicalInstance_initial_holes p hl hM ha initial target
  have hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) := hinit ▸ hh
  cases l.encodedSegments_gatePageWindow p hl hM ha initial hi hw hq with
  | fixed hf =>
    cases gateFixedSegments_location p middle hf with
    | publicStreet hc _ =>
      simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    | privateCap hc _ => omega
    | privateBranch _ hs => omega
    | halfDepth hr => omega
    | marker _ hc _ => exact special_off_axis p middle middle hc hx
  | @signal kind first internal _ _ hs =>
    cases gateSegments_location p initial kind first internal hs with
    | horizontal hr => omega
    | axis _ hr => omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem lower_gate_horizontal_impossible {middle depth : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hv : depth ∈ l.workingDepthCoordinates p) (hdepth : readDepth p 1 < depth)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x middle)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = p.H - depth) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change z.1.val = _ at hx
  change z.2.val = _ at hy
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hqy : q.2.val = p.H - depth := by rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.2).symm.trans hy
  rcases l.workingDepthCoordinates_bands p (show 1 ≤ 1 by omega) p.levels_pos hv with hshallow | hbranch | ⟨hlevels, hdeep⟩
  · omega
  · have hx0 := readLength_add_lt_x p middle 0
    have hqx : q.1.val = p.x middle - 1 ∨ q.1.val = p.x middle + 1 := by
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    rcases hqx with hleft | hright
    · have hg := l.physicalInstance_gate_private_step_avoiding p hl hM ha initial target hi hsu hm hvt ht
      exact hg.2 d n run hn hp hb ⟨n, by omega⟩
        (private_bottom l p hl hM ha hi (Or.inl hleft) (hbranch ▸ hqy))
    · have hwalk : q ∈ gatePrivateWalk p middle := (mem_gatePrivateWalk p middle).mpr
        (Or.inr (Or.inr ⟨hbranch ▸ hqy, by omega, by omega⟩))
      have he := l.physicalInstance_gate_privateWalk_empty p hl hM ha initial target hi hsu
        ((Relation.ReflTransGen.single hm).trans hvt) ht
      exact (mem_holes q).mp (he hwalk) (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
  · have hmax := workingRows_le_last l p hv
    have hband : z ∈ axisDeepBand p .lower middle 1 := by
      refine ⟨by rw [hx, Nat.dist_self]; omega, ?_⟩
      simp only [reduceCtorEq, ite_false]
      omega
    have hgap := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
    have hfull := gate_deep_axis_initial_full l p hl hM ha initial target hi hv (by omega) hx hy
    exact run.empty (l.physicalInstance_gate_deep_occupied p hl hM ha initial target hi hlevels hband hfull hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ht)

private theorem gate_axis_horizontal_impossible {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (upper : Endpoint) (hu : upper ∈ l.endpoints) (hs : upper.side = .upper) (hport : upper.port = middle)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hz : run.cell ⟨n + 1, by omega⟩ ∈ gateAxis p middle) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  have hr := (Finset.mem_filter.mp hz).2
  change z.1.val = _ ∧ 0 < z.2.val ∧ z.2.val < _ at hr
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have heven := x_even p middle
  have hstreet := l.physicalInstance_push_run_on_streets p hl hM ha initial target hsu run hn hp hb hvt ht ⟨n, by omega⟩
  change q.1 ∈ l.streetColumnSet p ∨ q.2 ∈ l.workingRowSet p at hstreet
  have hrow : z.2 ∈ l.workingRowSet p := by
    rcases hstreet with hcol | hrow
    · have hx := l.streetColumnSet_even p hcol
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · rcases hd with rfl | rfl <;> exact hadj.2 ▸ hrow
  rcases (l.workingRowSet_iff p _).mp hrow with hzero | hH | ⟨depth, hv, hy | hy⟩
  · omega
  · omega
  · exact l.physicalInstance_upper_axis_no_horizontal_input p hl hM ha initial target upper hu hs
      hsu hm hvt ht run hn hp hb hd hv (by simpa only [hport] using hr.1) hy
  · exact lower_gate_horizontal_impossible l p hl hM ha initial target hi hsu hm hvt ht run hn hp hb hd hv
      (by have hmax := workingRows_le_last l p hv; have hD := last_depth_margin p; have hH : p.H = 2 * p.D := rfl; omega) hr.1 hy

/-- No actual successful push imports a box into the gate middle-axis open segment. -/
theorem physicalInstance_gateAxis_no_input {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.ForwardStep (I).board none (gateAxis p middle)ᶜ u v := by
  obtain ⟨upper, hu, hs, hport⟩ := l.endpoints_upper_exists hl (gate_center_lt l hl hi)
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb hfirst
  by_contra hlast
  have hz : run.cell ⟨n + 1, by omega⟩ ∈ gateAxis p middle := by
    by_contra hnot
    exact hlast (Finset.mem_compl.mpr hnot)
  have hfirst : run.cell 1 ∉ gateAxis p middle := Finset.mem_compl.mp hfirst
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  let first : Cell (p.W + 1) (p.H + 1) := run.cell 1
  change first ∉ gateAxis p middle at hfirst
  have hr := (Finset.mem_filter.mp hz).2
  change z.1.val = _ ∧ 0 < z.2.val ∧ z.2.val < _ at hr
  have hp1 := run.position 1
  simp only [Fin.val_one] at hp1
  change d.position first = d.position u.player + 1 at hp1
  have hpN := run.position ⟨n + 1, by omega⟩
  change d.position z = d.position u.player + (n + 1 : ℕ) at hpN
  cases d with
  | east =>
    exact gate_axis_horizontal_impossible l p hl hM ha initial target hi upper hu hs hport
      hsu hm hvt ht run hn hp hb (Or.inl rfl) hz
  | west =>
    exact gate_axis_horizontal_impossible l p hl hM ha initial target hi upper hu hs hport
      hsu hm hvt ht run hn hp hb (Or.inr rfl) hz
  | north =>
    simp only [Direction.position] at hp1 hpN
    have hx1 : first.1.val = p.x middle := (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm |>.trans hr.1
    have hf : p.H - readDepth p 1 ≤ first.2.val := by
      by_contra hnot
      exact hfirst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, by omega, by omega⟩)
    have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
    have hH := readDepth_add_lt_H p 1
    let q : Cell (p.W + 1) (p.H + 1) := (z.1, ⟨p.H - (readDepth p 1 - 1), by omega⟩)
    have hq := l.gatePrivateBlockers_back_mem p hl hM ha hi (q := q) (Or.inl hr.1) rfl
    have hg := l.physicalInstance_gate_private_step_avoiding p hl hM ha initial target hi hsu hm hvt ht
    obtain ⟨i, hi⟩ := run_hits_position run q (run.lane ⟨n + 1, by omega⟩)
      (by change -(u.player.2.val : ℤ) ≤ -((p.H - (readDepth p 1 - 1) : ℕ) : ℤ); omega)
      (by change -((p.H - (readDepth p 1 - 1) : ℕ) : ℤ) ≤ -(z.2.val : ℤ); omega)
    exact hg.2 .north n run hn hp hb i (hi.symm ▸ hq)
  | south =>
    simp only [Direction.position] at hp1 hpN
    have hx1 : first.1.val = p.x middle := (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm |>.trans hr.1
    have hy0 : first.2.val = 0 := by
      by_contra hnot
      exact hfirst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, by omega, by omega⟩)
    have hframe : first ∈ Boundary.frame := (Boundary.mem_frame _).mpr ⟨.north, by
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; exact hy0⟩
    have hpub := l.physicalInstance_allPublicWalk_empty p hl hM ha initial target hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ht
    exact (mem_holes first).mp (hpub (Finset.mem_union_left _ hframe)) (run.first_occupied hn)

/-- The actual no-input relation holds on every successful middle-axis prefix. -/
theorem physicalInstance_gateAxis_no_input_prefix {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (gateAxis p middle)ᶜ) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact l.physicalInstance_gateAxis_no_input p hl hM ha initial target hi hsa hm (hbu.trans hut) ht

/-- The same no-input relation holds throughout the actual successful suffix. -/
theorem physicalInstance_gateAxis_no_input_suffix {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (gateAxis p middle)ᶜ) u t := by
  apply enrich_path hut
  intro a b hua hm hbt
  exact l.physicalInstance_gateAxis_no_input p hl hM ha initial target hi (hsu.trans hua) hm hbt ht

end Solution
end PushPuzzle.PushS.PortLayout
