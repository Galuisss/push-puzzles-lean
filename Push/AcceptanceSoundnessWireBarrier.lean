/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.AcceptanceSoundnessWireBalanced
public import Push.AcceptanceOrdinaryReaderClosure
import all PushS.PortWireIndexing
import all PushS.PortWireNoInput
import all PushS.PortEndpointFStock
import all PushS.PortSegments

/-! A balanced three-hole ordinary WIRE blocks horizontal box input at either main-axis boundary. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness


open PushFS PushS PushS.PortLayout AcceptanceProgram

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem wire_inside_barrier {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val =
      if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = if d = .east then p.x g.right else p.x g.left) : False := by
  let first : Cell (p.W + 1) (p.H + 1) := run.cell 1
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change z.1.val = _ at hx
  change z.2.val = _ at hy
  have hnotz : z ∉ wireOpenRail p g := by
    intro hz
    have hr := (Finset.mem_filter.mp hz).2
    rcases hd with rfl | rfl <;> simp only [ite_true, reduceCtorEq, ite_false] at hx <;> omega
  have hnotfirst : first ∉ wireOpenRail p g := fun h => hnotz
    ((canonical_wire_transfer_iff l p hl hM haxes initial target hgate hg hw hsu hm hvt ha run hn hb).mp h)
  have hrowfirst : first.2.val = z.2.val := by
    rcases hd with rfl | rfl <;> exact (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm
  have hout : ¬(p.x g.left < first.1.val ∧ first.1.val < p.x g.right) := by
    intro hspan
    exact hnotfirst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrowfirst.trans hy, hspan⟩)
  have hc := canonical_wireOpenRail_holes l p hl hM haxes initial target hgate hg hw hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ha
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < (holes u ∩ wireOpenRail p g).card by omega)
  obtain ⟨hqhole, hqrail⟩ := Finset.mem_inter.mp hq
  have hqr := (Finset.mem_filter.mp hqrail).2
  have hp1 := run.position 1
  simp only [Fin.val_one] at hp1
  change d.position first = d.position u.player + 1 at hp1
  have hpN := run.position ⟨n + 1, by omega⟩
  change d.position z = d.position u.player + (n + 1 : ℕ) at hpN
  obtain ⟨i, hi⟩ := run_hits_position run q
    (by rcases hd with rfl | rfl <;> exact (hqr.1.trans hy.symm).trans (run.lane ⟨n + 1, by omega⟩))
    (by rcases hd with rfl | rfl <;> simp only [Direction.position, ite_true, reduceCtorEq, ite_false] at hp1 hpN hx ⊢ <;> omega)
    (by change d.position q ≤ d.position z
        rcases hd with rfl | rfl <;> simp only [Direction.position, ite_true, reduceCtorEq, ite_false] at hpN hx ⊢ <;> omega)
  have hpi := run.position i
  change d.position (run.cell i : Cell (p.W + 1) (p.H + 1)) = d.position u.player + i.val at hpi
  rw [hi] at hpi
  have hi0 : 0 < i.val := by
    rcases hd with rfl | rfl <;> simp only [Direction.position, ite_true, reduceCtorEq, ite_false] at hp1 hpN hpi hx <;> omega
  have hin : i.val ≤ n := by
    rcases hd with rfl | rfl <;> simp only [Direction.position, ite_true, reduceCtorEq, ite_false] at hpN hpi hx <;> omega
  exact (mem_holes q).mp hqhole (hi ▸ run.occupied_at i hi0 hin)

private theorem endpoint_outward_input_impossible (e : Endpoint) (he : e ∈ l.endpoints)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n depth : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = if e.inward then .east else .west)
    (hv : depth ∈ l.workingDepthCoordinates p) (hle : depth ≤ readDepth p e.level)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x e.port)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = if e.side = .upper then depth else p.H - depth) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q (run.cell ⟨n + 1, by omega⟩) at hadj
  have hqx : q.1.val = if e.inward then p.x e.port - 1 else p.x e.port + 1 := by
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hd ⊢ <;>
      subst d <;> simp only [Adjacent] at hadj <;> omega
  have hqy : q.2.val = if e.side = .upper then depth else p.H - depth := by
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hd <;>
      subst d <;> exact (congrArg Fin.val hadj.2).symm.trans hy
  have hg := canonical_ordinary_reader_step_avoiding l p hl hM haxes initial target hgate e he hsu hm hvt ha
  exact hg.2 d n run hn hp hb ⟨n, by omega⟩
    (l.endpointOrdinaryBlockers_front_mem p hl hM haxes e he hv hle hqx hqy)

/-- A complete successful horizontal push cannot end at either main-axis boundary of an ordinary WIRE. -/
theorem canonical_wire_axis_destination_impossible {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val =
      if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x g.left ∨
      (run.cell ⟨n + 1, by omega⟩).1.val = p.x g.right) : False := by
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  have hv := wire_workDepth l p hl hM hg
  rcases hd with rfl | rfl <;> rcases hx with hx | hx
  · exact endpoint_outward_input_impossible l p hl hM haxes initial target hgate (wireLeft g) heL hsu hm hvt ha
      run hn hp hb rfl hv le_rfl hx hy
  · exact wire_inside_barrier l p hl hM haxes initial target hgate hg hw hsu hm hvt ha run hn hb (Or.inl rfl) hy hx
  · exact wire_inside_barrier l p hl hM haxes initial target hgate hg hw hsu hm hvt ha run hn hb (Or.inr rfl) hy hx
  · exact endpoint_outward_input_impossible l p hl hM haxes initial target hgate (wireRight g) heR hsu hm hvt ha
      run hn hp hb rfl hv le_rfl hx hy

end Solution
end PushPuzzle.Push.AcceptanceSoundness
