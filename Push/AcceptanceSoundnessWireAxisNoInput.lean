/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireEndpointNoInput
public import Push.AcceptanceAxisNoExport
public import Push.Partner
import all PushS.PortStreetSeparation
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! Main axes attached below to ordinary WIREs have no physical box input, so their signed surplus vanishes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem ordinary_lower_wire_endpoint (l : PortLayout) {port : ℕ} (hp : Partner.Ordinary l port) :
    ∃ g ∈ placements l, g.gate = none ∧ ∃ e ∈ l.endpoints,
      e.side = .lower ∧ e.port = port ∧ (e = wireWorkLeft g ∨ e = wireWorkRight g) := by
  obtain ⟨a, b, hab, hport⟩ := hp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hab
  let g : Placement := ⟨.lower, a, b, l.lowerLevel i.val, l.lowerOffset i.val, none⟩
  have hzip : (LowerGroup.wire a b, i.val) ∈ l.lowerGroups.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    rw [List.getElem?_eq_getElem i.isLt]
    exact congrArg some hi
  have hg : g ∈ placements l := by
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(.wire a b, i.val), hzip, by simp [encLowerGroup_elim, encLowerGroup_toSum, g]⟩
  obtain ⟨hL, hR⟩ := wire_endpoints l hg (show g.gate = none from rfl)
  refine ⟨g, hg, rfl, ?_⟩
  rcases hport with rfl | rfl
  · refine ⟨wireWorkLeft g, ?_, rfl, rfl, Or.inl rfl⟩
    simpa only [wireWorkLeft, wireLeft] using hL
  · refine ⟨wireWorkRight g, ?_, rfl, rfl, Or.inr rfl⟩
    simpa only [wireWorkRight, wireRight, g, Option.isSome_none, ite_false, Nat.add_zero] using hR

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem wire_axis_horizontal_impossible {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (upper lower : Endpoint) (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    (hlower : lower = wireWorkLeft g ∨ lower = wireWorkRight g)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hz : run.cell ⟨n + 1, by omega⟩ ∈ ordinaryAxis p upper.port) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  have hr := (Finset.mem_filter.mp hz).2
  change z.1.val = _ ∧ 0 < z.2.val ∧ z.2.val < _ at hr
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have heven := x_even p upper.port
  have hstreet := canonical_push_run_on_original l p hl hM haxes initial target hsu run hn hp hb hvt ha ⟨n, by omega⟩
  change q.1 ∈ l.streetColumnSet p ∨ q.2 ∈ l.workingRowSet p at hstreet
  have hrow : z.2 ∈ l.workingRowSet p := by
    rcases hstreet with hcol | hrow
    · have hx := l.streetColumnSet_even p hcol
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · rcases hd with rfl | rfl <;> exact hadj.2 ▸ hrow
  rcases (l.workingRowSet_iff p _).mp hrow with hzero | hH | ⟨depth, hv, hy | hy⟩
  · omega
  · omega
  · exact canonical_upper_axis_no_horizontal_input l p hl hM haxes initial target hgate upper hu hsuSide
      hsu hm hvt ha run hn hp hb hd hv hr.1 hy
  · exact canonical_wire_endpoint_no_horizontal_input l p hl hM haxes initial target hgate hg hw lower hlow hlower
      hsu hm hvt ha run hn hp hb hd hv (by simpa only [hport] using hr.1)
      (by simpa only [hslSide, reduceCtorEq, ite_false] using hy)

/-- An actual main axis whose lower endpoint belongs to a WIRE cannot receive boxes. -/
private theorem canonical_wire_axis_no_input {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    (upper lower : Endpoint) (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    (hlower : lower = wireWorkLeft g ∨ lower = wireWorkRight g)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Inventory.ForwardStep (I).board none (ordinaryAxis p upper.port)ᶜ u v := by
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb hfirst
  by_contra hlast
  have hz : run.cell ⟨n + 1, by omega⟩ ∈ ordinaryAxis p upper.port := by
    by_contra hnot
    exact hlast (Finset.mem_compl.mpr hnot)
  have hfirst : run.cell 1 ∉ ordinaryAxis p upper.port := Finset.mem_compl.mp hfirst
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  let first : Cell (p.W + 1) (p.H + 1) := run.cell 1
  change first ∉ ordinaryAxis p upper.port at hfirst
  have hr := (Finset.mem_filter.mp hz).2
  change z.1.val = _ ∧ 0 < z.2.val ∧ z.2.val < _ at hr
  have hp1 := run.position 1
  simp only [Fin.val_one] at hp1
  change d.position first = d.position u.player + 1 at hp1
  have hpN := run.position ⟨n + 1, by omega⟩
  change d.position z = d.position u.player + (n + 1 : ℕ) at hpN
  have hframe := canonical_frame_empty_at l p hl hM haxes initial target
    ((Relation.ReflTransGen.single hm).trans hvt) ha
  cases d with
  | east =>
    exact wire_axis_horizontal_impossible l p hl hM haxes initial target hgate hg hw upper lower hu hlow
      hsuSide hslSide hport hlower hsu hm hvt ha run hn hp hb (Or.inl rfl) hz
  | west =>
    exact wire_axis_horizontal_impossible l p hl hM haxes initial target hgate hg hw upper lower hu hlow
      hsuSide hslSide hport hlower hsu hm hvt ha run hn hp hb (Or.inr rfl) hz
  | north =>
    simp only [Direction.position] at hp1 hpN
    have hx1 : first.1.val = p.x upper.port := (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm |>.trans hr.1
    have hyH : first.2.val = p.H := by
      have hf := first.2.isLt
      by_contra hnot
      exact hfirst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, by omega, by omega⟩)
    have hf : first ∈ Boundary.frame := (Boundary.mem_frame _).mpr
      ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    exact Finset.disjoint_left.mp hframe (run.first_occupied hn) hf
  | south =>
    simp only [Direction.position] at hp1 hpN
    have hx1 : first.1.val = p.x upper.port := (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm |>.trans hr.1
    have hy0 : first.2.val = 0 := by
      by_contra hnot
      exact hfirst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, by omega, by omega⟩)
    have hf : first ∈ Boundary.frame := (Boundary.mem_frame _).mpr
      ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩⟩
    exact Finset.disjoint_left.mp hframe (run.first_occupied hn) hf

/-- Both one-way constraints preserve the complete actual WIRE-attached ordinary-axis count in every step. -/
private theorem canonical_wire_axis_inventory_step {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    (upper lower : Endpoint) (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    (hlower : lower = wireWorkLeft g ∨ lower = wireWorkRight g)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Inventory.count (ordinaryAxis p upper.port) u = Inventory.count (ordinaryAxis p upper.port) v := by
  have hex : Inventory.count (ordinaryAxis p upper.port) u ≤ Inventory.count (ordinaryAxis p upper.port) v :=
    Inventory.step_mono (canonical_ordinaryAxis_no_export l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hsu hm hvt ha)
  have hin : Inventory.count (ordinaryAxis p upper.port)ᶜ u ≤ Inventory.count (ordinaryAxis p upper.port)ᶜ v :=
    Inventory.step_mono (canonical_wire_axis_no_input l p hl hM haxes initial target hgate
      hg hw upper lower hu hlow hsuSide hslSide hport hlower hsu hm hvt ha)
  have hcu := Inventory.count_add_compl (ordinaryAxis p upper.port) u
  have hcv := Inventory.count_add_compl (ordinaryAxis p upper.port) v
  have hb : v.boxes.card = u.boxes.card := hm.card_boxes
  omega

/-- Every actual prefix preserves the WIRE-attached ordinary axis's original box count. -/
private theorem canonical_wire_axis_count_eq {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    (upper lower : Endpoint) (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    (hlower : lower = wireWorkLeft g ∨ lower = wireWorkRight g)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Inventory.count (ordinaryAxis p upper.port) (I).initial = Inventory.count (ordinaryAxis p upper.port) u := by
  have hp : Relation.ReflTransGen (fun a b : State (p.W + 1) (p.H + 1) =>
      Inventory.count (ordinaryAxis p upper.port) a = Inventory.count (ordinaryAxis p upper.port) b) (I).initial u := by
    apply Path.enrich hsu
    intro a b hsa hm hbu
    exact canonical_wire_axis_inventory_step l p hl hM haxes initial target hgate hg hw upper lower hu hlow
      hsuSide hslSide hport hlower hsa hm (hbu.trans hut) ha
  clear hsu hut
  induction hp with
  | refl => rfl
  | tail _ he ih => exact ih.trans he

/-- Every actual lower-WIRE incidence has zero ordinary-axis surplus throughout the accepted trajectory. -/
theorem canonical_ordinary_wire_surplus_zero {port : ℕ} (hp : Partner.Ordinary l port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Inventory.count (ordinaryAxis p port) u - Inventory.count (ordinaryAxis p port) (I).initial = 0 := by
  obtain ⟨g, hg, hw, lower, hlow, hsl, hport, hlower⟩ := ordinary_lower_wire_endpoint l hp
  obtain ⟨upper, hu, hsuSide, hupperPort⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl hlow)
  have hcount := canonical_wire_axis_count_eq l p hl hM haxes initial target hgate hg hw upper lower hu hlow
    hsuSide hsl hupperPort.symm hlower hsu hut ha
  rw [hupperPort, hport] at hcount
  exact Nat.sub_eq_zero_of_le (le_of_eq hcount.symm)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
