/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireColumns
public import PushS.PortOrdinaryBlockers
import all PushS.PortEndpointReaderWalk
import all PushS.PortEndpointFStock
import all PushS.PortWireIndexing
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! Successful physical pushes cannot import a box into an ordinary WIRE's open rail. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem wire_workDepth (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    {g : Placement} (hg : g ∈ placements l) : readDepth p g.level ∈ l.workingDepthCoordinates p := by
  have hb := placement_level_bounds l hl hg
  have hv := (l.workingDepthCoordinates_mem p (g.level - 1) (by omega)).1
  simpa only [Nat.sub_add_cancel hb.1] using hv

private theorem horizontal_first_outside {w h n row a b : ℕ} {B : Board w h}
    {d : Direction} {s : State w h} (run : Run B d s n) (hd : d = .east ∨ d = .west)
    (hfirst : run.cell 1 ∉ Finset.univ.filter (fun q : Cell w h => q.2.val = row ∧ a < q.1.val ∧ q.1.val < b))
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = row) :
    ¬(a < (run.cell 1).1.val ∧ (run.cell 1).1.val < b) := by
  intro hspan
  apply hfirst
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hspan⟩
  rcases hd with rfl | rfl <;> exact ((run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm).trans hy

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem receiving_vertical_impossible (e : Endpoint) (he : e ∈ l.endpoints)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = EndpointStreet.r.column p e)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val =
      if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q (run.cell ⟨n + 1, by omega⟩) at hadj
  have hqx : q.1.val = EndpointStreet.r.column p e := by
    rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.1.symm).trans hx
  have hY := readDepth_add_lt_H p e.level
  have hqy : (if e.side = .upper then q.2.val < readDepth p e.level
      else p.H - readDepth p e.level < q.2.val) ∨
      q.2.val = (if e.side = .upper then readDepth p e.level + 1
        else p.H - (readDepth p e.level + 1)) := by
    rcases hd with rfl | rfl <;> cases hs : e.side <;>
      simp only [hs, reduceCtorEq, ite_true, ite_false, Adjacent] at hadj hy ⊢ <;>
      omega
  rcases hqy with hreader | hcap
  · have he := l.physicalInstance_ordinaryReaders_empty p hl hM ha initial target e he hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ht
    have hq : q ∈ l.endpointReaderWalk p e := Finset.mem_union_right _
      (Finset.mem_union_left _ ((mem_endpointRWalk_iff p e q).mpr ⟨hqx, hreader⟩))
    exact (mem_holes q).mp (he hq) (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
  · have hg := l.physicalInstance_ordinary_reader_step_avoiding p hl hM ha initial target e he hsu hm hvt ht
    exact hg.2 d n run hn hp hb ⟨n, by omega⟩
      (l.endpointOrdinaryBlockers_cap_mem p hl hM ha e he hqx hcap)

private theorem wire_vertical_impossible {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south) (hz : run.cell ⟨n + 1, by omega⟩ ∈ wireOpenRail p g) : False := by
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  have hr := (Finset.mem_filter.mp hz).2
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  change z.2.val = _ ∧ p.x g.left < z.1.val ∧ z.1.val < p.x g.right at hr
  have hqx : q.1 = z.1 := by rcases hd with rfl | rfl <;> exact hadj.1.symm
  have heven := l.workingRowSet_even p
    (l.mem_workingRowSet_of_onSide p (wire_workDepth l p hl hM hg) g.side z.2 hr.1)
  have hside : if g.side = .upper then q.2.val < p.D else p.D < q.2.val := by
    have hY := readDepth_add_lt_D p g.level
    have hH : p.H = 2 * p.D := rfl
    rcases hd with rfl | rfl <;> cases hs : g.side <;>
      simp only [hs, reduceCtorEq, ite_true, ite_false, Adjacent] at hadj hr ⊢ <;> omega
  have hsupp := l.physicalInstance_push_run_on_pages p hl hM ha initial target hsu run hn hp hb hvt ht ⟨n, by omega⟩
  have hcol : z.1 ∈ l.pageColumnSet p g.side := by
    rcases (l.page_support_iff_side p hl g.side q hside).mp hsupp with hrow | hcol
    · have hodd := l.workingRowSet_even p hrow
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · exact hqx ▸ hcol
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  by_cases hxL : z.1.val = p.x g.left + 2
  · exact receiving_vertical_impossible l p hl hM ha initial target (wireLeft g) heL hsu hm hvt ht
      run hn hp hb hd hxL hr.1
  · by_cases hxR : z.1.val = p.x g.right - 2
    · exact receiving_vertical_impossible l p hl hM ha initial target (wireRight g) heR hsu hm hvt ht
        run hn hp hb hd hxR hr.1
    · exact run.empty (l.physicalInstance_wire_internal_column p hl hM ha initial target hg hw hz hcol
        hxL hxR hsu ((Relation.ReflTransGen.single hm).trans hvt) ht).2

private theorem wire_horizontal_no_input {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hz : run.cell ⟨n + 1, by omega⟩ ∈ wireOpenRail p g)
    (hfirst : run.cell 1 ∉ wireOpenRail p g) : False := by
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  have hr := (Finset.mem_filter.mp hz).2
  change z.2.val = _ ∧ p.x g.left < z.1.val ∧ z.1.val < p.x g.right at hr
  have hout := horizontal_first_outside run hd hfirst hr.1
  have hp1 := run.position 1
  have hpN := run.position ⟨n + 1, by omega⟩
  have hports := wire_ports l hl hg hw
  have hx0 := readLength_add_lt_x p g.left 0
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le ha) 0
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  rcases hd with rfl | rfl
  · simp only [Direction.position, Fin.val_one] at hp1 hpN
    change (z.1.val : ℤ) = _ at hpN
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨p.x g.left - 1, by have := z.1.isLt; omega⟩, z.2)
    have hq := l.endpointOrdinaryBlockers_front_mem p hl hM ha (wireLeft g) heL
      (wire_workDepth l p hl hM hg) le_rfl (q := q) rfl hr.1
    have hg := l.physicalInstance_ordinary_reader_step_avoiding p hl hM ha initial target
      (wireLeft g) heL hsu hm hvt ht
    obtain ⟨i, hi⟩ := run_hits_position run q (run.lane ⟨n + 1, by omega⟩)
      (by change (u.player.1.val : ℤ) ≤ (p.x g.left - 1 : ℕ); omega)
      (by change ((p.x g.left - 1 : ℕ) : ℤ) ≤ z.1.val; omega)
    exact hg.2 .east n run hn hp hb i (hi.symm ▸ hq)
  · simp only [Direction.position, Fin.val_one] at hp1 hpN
    change -(z.1.val : ℤ) = _ at hpN
    let q : Cell (p.W + 1) (p.H + 1) := (⟨p.x g.right + 1, by omega⟩, z.2)
    have hq := l.endpointOrdinaryBlockers_front_mem p hl hM ha (wireRight g) heR
      (wire_workDepth l p hl hM hg) le_rfl (q := q) rfl hr.1
    have hg := l.physicalInstance_ordinary_reader_step_avoiding p hl hM ha initial target
      (wireRight g) heR hsu hm hvt ht
    obtain ⟨i, hi⟩ := run_hits_position run q (run.lane ⟨n + 1, by omega⟩)
      (by change -(u.player.1.val : ℤ) ≤ -(p.x g.right + 1 : ℕ); omega)
      (by change -((p.x g.right + 1 : ℕ) : ℤ) ≤ -(z.1.val : ℤ); omega)
    exact hg.2 .west n run hn hp hb i (hi.symm ▸ hq)

/-- An actual successful push never imports a box into an ordinary WIRE's open interval. -/
theorem physicalInstance_wire_no_input {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.ForwardStep (I).board none (wireOpenRail p g)ᶜ u v := by
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb hfirst
  by_contra hlast
  have hz : run.cell ⟨n + 1, by omega⟩ ∈ wireOpenRail p g := by
    by_contra hnot
    exact hlast (Finset.mem_compl.mpr hnot)
  have hfirst : run.cell 1 ∉ wireOpenRail p g := Finset.mem_compl.mp hfirst
  cases d with
  | north => exact wire_vertical_impossible l p hl hM ha initial target hg hw hsu hm hvt ht run hn hp hb (Or.inl rfl) hz
  | south => exact wire_vertical_impossible l p hl hM ha initial target hg hw hsu hm hvt ht run hn hp hb (Or.inr rfl) hz
  | east => exact wire_horizontal_no_input l p hl hM ha initial target hg hw hsu hm hvt ht run hn hp hb (Or.inl rfl) hz hfirst
  | west => exact wire_horizontal_no_input l p hl hM ha initial target hg hw hsu hm hvt ht run hn hp hb (Or.inr rfl) hz hfirst

/-- The actual prefix carries the no-input inventory relation on the same physical states. -/
theorem physicalInstance_wire_no_input_prefix {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (wireOpenRail p g)ᶜ) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact l.physicalInstance_wire_no_input p hl hM ha initial target hg hw hsa hm (hbu.trans hut) ht

/-- The same no-input relation holds throughout any actual successful suffix. -/
theorem physicalInstance_wire_no_input_suffix {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (wireOpenRail p g)ᶜ) u t := by
  apply enrich_path hut
  intro a b hua hm hbt
  exact l.physicalInstance_wire_no_input p hl hM ha initial target hg hw (hsu.trans hua) hm hbt ht

end Solution
end PushPuzzle.PushS.PortLayout
