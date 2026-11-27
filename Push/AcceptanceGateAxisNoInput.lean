/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateAxisLowerBarrier
public import Push.AcceptanceSoundnessUpperAxisNoInput
import all PushS.PortGatePrivateWalk
import all PushS.PortGatePageWindow
import all PushS.PortEndpointFStock
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual accepted gate middle axes cannot import boxes, retaining their possible signed deficit. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM ha initial target

include hgate

private theorem gate_axis_horizontal_impossible {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (upper : Endpoint) (hu : upper ∈ l.endpoints) (hs : upper.side = .upper) (hport : upper.port = middle)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
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
  have hstreet := canonical_push_run_on_original l p hl hM ha initial target hsu run hn hp hb hvt accepted ⟨n, by omega⟩
  change q.1 ∈ l.streetColumnSet p ∨ q.2 ∈ l.workingRowSet p at hstreet
  have hrow : z.2 ∈ l.workingRowSet p := by
    rcases hstreet with hcol | hrow
    · have hx := l.streetColumnSet_even p hcol
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · rcases hd with rfl | rfl <;> exact hadj.2 ▸ hrow
  rcases (l.workingRowSet_iff p _).mp hrow with hzero | hH | ⟨depth, hv, hy | hy⟩
  · omega
  · omega
  · exact canonical_upper_axis_no_horizontal_input l p hl hM ha initial target hgate upper hu hs
      hsu hm hvt accepted run hn hp hb hd hv (by simpa only [hport] using hr.1) hy
  · exact canonical_lower_gate_horizontal_impossible l p hl hM ha initial target hgate hi hsu hm hvt accepted run hn hp hb hd hv
      (by have hmax := workingRows_le_last l p hv; have hD := last_depth_margin p; have hH : p.H = 2 * p.D := rfl; omega) hr.1 hy

/-- No actual successful push imports a box into the gate middle-axis open segment. -/
theorem canonical_gateAxis_no_input {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
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
    exact gate_axis_horizontal_impossible l p hl hM ha initial target hgate hi upper hu hs hport
      hsu hm hvt accepted run hn hp hb (Or.inl rfl) hz
  | west =>
    exact gate_axis_horizontal_impossible l p hl hM ha initial target hgate hi upper hu hs hport
      hsu hm hvt accepted run hn hp hb (Or.inr rfl) hz
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
    have hg := canonical_gate_private_step_avoiding l p hl hM ha initial target hgate hi hsu hm hvt accepted
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
    have hpub := canonical_publicWalkInvariant l p hl hM ha initial target hgate accepted _ hsu
      ((Relation.ReflTransGen.single hm).trans hvt)
    exact (mem_holes first).mp (hpub (Finset.mem_union_left _ hframe)) (run.first_occupied hn)

/-- The actual no-input relation holds on every successful middle-axis prefix. -/
theorem canonical_gateAxis_no_input_prefix {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (gateAxis p middle)ᶜ) (I).initial u := by
  apply Path.enrich hsu
  intro a b hsa hm hbu
  exact canonical_gateAxis_no_input l p hl hM ha initial target hgate hi hsa hm (hbu.trans hut) accepted

/-- The same no-input relation holds throughout the actual successful suffix. -/
theorem canonical_gateAxis_no_input_suffix {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (gateAxis p middle)ᶜ) u t := by
  apply Path.enrich hut
  intro a b hua hm hbt
  exact canonical_gateAxis_no_input l p hl hM ha initial target hgate hi (hsu.trans hua) hm hbt accepted

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
