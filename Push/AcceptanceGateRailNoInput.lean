/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.AcceptanceGateAxisInventory
public import Push.AcceptanceSoundnessWireNoInput
public import PushS.PortGateColumns
import all Push.AcceptanceSoundnessWireNoInput
import all PushS.PortWireNoInput
import all PushS.PortGateIndexing
import all PushS.PortGatePrivateWalk
import all PushS.PortGateHalfRods
import all PushS.PortGatePublicWalk
import all PushS.PortGatePageWindow
import all PushS.PortEndpointFStock
import all PushS.PortCoreCrossing
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual accepted gate rails cannot receive boxes once their middle-axis deficit vanishes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness


open PushFS PushS PushS.PortLayout AcceptanceProgram

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem gate_special_vertical_impossible {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val ∈ gateSpecialColumns p middle)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = p.H - readDepth p 1) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change z.1.val ∈ _ at hx
  change z.2.val = _ at hy
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hqx : q.1.val = z.1.val := by rcases hd with rfl | rfl <;> exact congrArg Fin.val hadj.1.symm
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  have hqy : q.2.val = p.H - (readDepth p 1 - 1) ∨ q.2.val = p.H - (readDepth p 1 + 1) := by
    rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
  have hcols : q.1.val ∈ gatePublicColumns p middle ∨ q.1.val = p.x middle + 4 := by
    change z.1.val ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hx
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega
  have hguard := canonical_gate_private_step_avoiding l p hl hM haxes initial target hgate hi hsu hm hvt accepted
  rcases hcols with hpublic | hprivate
  · rcases hqy with hbefore | hcap
    · have he := canonical_gate_publicWalk_empty l p hl hM haxes initial target hgate hi hsu
        ((Relation.ReflTransGen.single hm).trans hvt) accepted
      have hwalk : q ∈ gatePublicWalk p middle := (mem_gatePublicWalk p middle).mpr
        (Or.inr ⟨hpublic, by omega⟩)
      exact (mem_holes q).mp (he hwalk) (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
    · have hcap := gate_public_cap l p hl hM haxes hi hpublic hcap
      exact hguard.2 d n run hn hp hb ⟨n, by omega⟩
        (Finset.mem_union_left _ (Finset.mem_union_left _ hcap))
  · rcases hqy with hback | hcap
    · exact hguard.2 d n run hn hp hb ⟨n, by omega⟩
        (l.gatePrivateBlockers_back_mem p hl hM haxes hi (Or.inr hprivate) hback)
    · have he := canonical_gate_privateWalk_empty l p hl hM haxes initial target hgate hi hsu
        ((Relation.ReflTransGen.single hm).trans hvt) accepted
      have hwalk : q ∈ gatePrivateWalk p middle := (mem_gatePrivateWalk p middle).mpr
        (Or.inr (Or.inl ⟨hprivate, hcap⟩))
      exact (mem_holes q).mp (he hwalk) (run.occupied_at ⟨n, by omega⟩ hn le_rfl)

private theorem gate_middle_vertical_impossible {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x (g.left + 1))
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = p.H - readDepth p 1) : False := by
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  change z.1.val = _ at hx
  change z.2.val = _ at hy
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  rcases hd with rfl | rfl
  · have hqx : q.1.val = p.x (g.left + 1) := (congrArg Fin.val hadj.1.symm).trans hx
    have hqy : q.2.val = p.H - (readDepth p 1 - 1) := by simp only [Adjacent] at hadj; omega
    have hguard := canonical_gate_private_step_avoiding l p hl hM haxes initial target hgate hi hsu hm hvt accepted
    exact hguard.2 .north n run hn hp hb ⟨n, by omega⟩
      (l.gatePrivateBlockers_back_mem p hl hM haxes hi (Or.inl hqx) hqy)
  · have hz : z ∉ gateAxis p (g.left + 1) := by
      intro hz
      have hr := (Finset.mem_filter.mp hz).2
      omega
    let first : Cell (p.W + 1) (p.H + 1) := run.cell 1
    have hf : first ∉ gateAxis p (g.left + 1) := fun h => hz
      ((canonical_gateAxis_transfer_iff_of_terminal l p hl hM haxes initial target hgate hg hk hsu hm hvt accepted axisInventory run hn hb).mp h)
    have hx1 : first.1.val = p.x (g.left + 1) :=
      (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm |>.trans hx
    have hp1 := run.position 1
    have hpN := run.position ⟨n + 1, by omega⟩
    simp only [Direction.position, Fin.val_one] at hp1 hpN
    change (first.2.val : ℤ) = _ at hp1
    change (z.2.val : ℤ) = _ at hpN
    have hy0 : first.2.val = 0 := by
      by_contra hn0
      exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, by omega, by omega⟩)
    have hframe : first ∈ Boundary.frame := (Boundary.mem_frame _).mpr ⟨.north, by
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; exact hy0⟩
    exact Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target
      ((Relation.ReflTransGen.single hm).trans hvt) accepted) (run.first_occupied hn) hframe

private theorem gate_vertical_impossible {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south) (hz : run.cell ⟨n + 1, by omega⟩ ∈ gateOpenRail p g) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  have hr := (Finset.mem_filter.mp hz).2
  change z.2.val = _ ∧ _ at hr
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hqx : q.1 = z.1 := by rcases hd with rfl | rfl <;> exact hadj.1.symm
  have heven : z.2.val % 2 = 0 := by have := H_even p; have := readDepth_even p 1; omega
  have hside : p.D < q.2.val := by
    have hY := readDepth_add_lt_D p 1
    have hH : p.H = 2 * p.D := rfl
    rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
  have hsupp := canonical_push_run_on_pages l p hl hM haxes initial target hsu run hn hp hb hvt accepted ⟨n, by omega⟩
  have hcol : z.1 ∈ l.pageColumnSet p .lower := by
    rcases (l.page_support_iff_side p hl .lower q hside).mp hsupp with hrow | hcol
    · have hodd := l.workingRowSet_even p hrow
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · exact hqx ▸ hcol
  have hs := (placement_gate_shape l hg hk).1
  have hlevel := gate_level_one l hg hk
  obtain ⟨heL, heR⟩ := gate_endpoints l hg hk
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  rcases l.gateOpenRail_page_columns p hl haxes hg hk hz hcol with hxL | hxR | hxAxis | hxSpecial
  · apply receiving_vertical_impossible l p hl hM haxes initial target hgate (gateLeft g) heL hsu hm hvt accepted run hn hp hb hd hxL
    change z.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level
    simpa only [hs, hlevel, reduceCtorEq, ite_false] using hr.1
  · apply receiving_vertical_impossible l p hl hM haxes initial target hgate (gateRight g) heR hsu hm hvt accepted run hn hp hb hd hxR
    change z.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level
    simpa only [hs, hlevel, reduceCtorEq, ite_false] using hr.1
  · exact gate_middle_vertical_impossible l p hl hM haxes initial target hgate hg hk hsu hm hvt accepted axisInventory run hn hp hb hd hxAxis hr.1
  · exact gate_special_vertical_impossible l p hl hM haxes initial target hgate hi hsu hm hvt accepted run hn hp hb hd hxSpecial hr.1

private theorem gate_horizontal_no_input {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hz : run.cell ⟨n + 1, by omega⟩ ∈ gateOpenRail p g)
    (hfirst : run.cell 1 ∉ gateOpenRail p g) : False := by
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  have hr := (Finset.mem_filter.mp hz).2
  change z.2.val = _ ∧ p.x g.left < z.1.val ∧ z.1.val < p.x g.right at hr
  have hout := horizontal_first_outside run hd hfirst hr.1
  have hp1 := run.position 1
  have hpN := run.position ⟨n + 1, by omega⟩
  have hports := gate_port_bounds l hl hg hk
  have hx0 := readLength_add_lt_x p g.left 0
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le haxes) 0
  have hs := (placement_gate_shape l hg hk).1
  have hlevel := gate_level_one l hg hk
  have hv := (l.workingDepthCoordinates_mem p 0 (by have := p.levels_pos; omega)).1
  have hle : readDepth p 1 ≤ readDepth p g.level := by rw [hlevel]
  obtain ⟨heL, heR⟩ := gate_endpoints l hg hk
  rcases hd with rfl | rfl
  · simp only [Direction.position, Fin.val_one] at hp1 hpN
    change (z.1.val : ℤ) = _ at hpN
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨p.x g.left - 1, by have := z.1.isLt; omega⟩, z.2)
    have hq := l.endpointOrdinaryBlockers_front_mem p hl hM haxes (gateLeft g) heL hv hle (q := q) rfl (by
      change z.2.val = if g.side = .upper then readDepth p 1 else p.H - readDepth p 1
      simpa only [hs, reduceCtorEq, ite_false] using hr.1)
    have hguard := canonical_ordinary_reader_step_avoiding l p hl hM haxes initial target hgate (gateLeft g) heL hsu hm hvt accepted
    obtain ⟨i, hi⟩ := run_hits_position run q (run.lane ⟨n + 1, by omega⟩)
      (by change (u.player.1.val : ℤ) ≤ (p.x g.left - 1 : ℕ); omega)
      (by change ((p.x g.left - 1 : ℕ) : ℤ) ≤ z.1.val; omega)
    exact hguard.2 .east n run hn hp hb i (hi.symm ▸ hq)
  · simp only [Direction.position, Fin.val_one] at hp1 hpN
    change -(z.1.val : ℤ) = _ at hpN
    let q : Cell (p.W + 1) (p.H + 1) := (⟨p.x g.right + 1, by omega⟩, z.2)
    have hq := l.endpointOrdinaryBlockers_front_mem p hl hM haxes (gateRight g) heR hv hle (q := q) rfl (by
      change z.2.val = if g.side = .upper then readDepth p 1 else p.H - readDepth p 1
      simpa only [hs, reduceCtorEq, ite_false] using hr.1)
    have hguard := canonical_ordinary_reader_step_avoiding l p hl hM haxes initial target hgate (gateRight g) heR hsu hm hvt accepted
    obtain ⟨i, hi⟩ := run_hits_position run q (run.lane ⟨n + 1, by omega⟩)
      (by change -(u.player.1.val : ℤ) ≤ -(p.x g.right + 1 : ℕ); omega)
      (by change -((p.x g.right + 1 : ℕ) : ℤ) ≤ -(z.1.val : ℤ); omega)
    exact hguard.2 .west n run hn hp hb i (hi.symm ▸ hq)

/-- A successful physical push cannot import a box into an actual three-port horizontal rail. -/
theorem canonical_gateRail_no_input_of_axis_inventory {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    Inventory.ForwardStep (I).board none (gateOpenRail p g)ᶜ u v := by
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb hfirst
  by_contra hlast
  have hz : run.cell ⟨n + 1, by omega⟩ ∈ gateOpenRail p g := by
    by_contra hnot
    exact hlast (Finset.mem_compl.mpr hnot)
  have hfirst : run.cell 1 ∉ gateOpenRail p g := Finset.mem_compl.mp hfirst
  cases d with
  | north => exact gate_vertical_impossible l p hl hM haxes initial target hgate hg hk hsu hm hvt accepted axisInventory run hn hp hb (Or.inl rfl) hz
  | south => exact gate_vertical_impossible l p hl hM haxes initial target hgate hg hk hsu hm hvt accepted axisInventory run hn hp hb (Or.inr rfl) hz
  | east => exact gate_horizontal_no_input l p hl hM haxes initial target hgate hg hk hsu hm hvt accepted run hn hp hb (Or.inl rfl) hz hfirst
  | west => exact gate_horizontal_no_input l p hl hM haxes initial target hgate hg hk hsu hm hvt accepted run hn hp hb (Or.inr rfl) hz hfirst

/-- The same actual successful prefix carries the three-port rail's no-input relation. -/
theorem canonical_gateRail_no_input_prefix_of_axis_inventory {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (gateOpenRail p g)ᶜ) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact canonical_gateRail_no_input_of_axis_inventory l p hl hM haxes initial target hgate hg hk hsa hm (hbu.trans hut) accepted axisInventory

/-- The rail's no-input relation also holds along the actual successful suffix. -/
theorem canonical_gateRail_no_input_suffix_of_axis_inventory {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (gateOpenRail p g)ᶜ) u t := by
  apply enrich_path hut
  intro a b hua hm hbt
  exact canonical_gateRail_no_input_of_axis_inventory l p hl hM haxes initial target hgate hg hk (hsu.trans hua) hm hbt accepted axisInventory

end Solution
end PushPuzzle.Push.AcceptanceSoundness
