/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryAxis
public import PushS.PortAxisBlockers
public import PushS.PortDepthBands
public import PushS.PortColumnRadius
public import PushS.Inventory
import all PushS.PortEndpointFStock
import all PushS.PortStreetSeparation
import all PushS.PortCentralStrip
import all PushS.PortBackground

/-! An actual ordinary main axis cannot export boxes during a successful storage play. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem horizontal_neighbor_hit {w h n : ℕ} {B : Board w h} {d : Direction}
    {s : State w h} (run : Run B d s n) (hn : 0 < n) (hd : d = .east ∨ d = .west)
    (q : Cell w h) (hy : q.2.val = (run.cell 1).2.val)
    (hx : Nat.dist q.1.val (run.cell 1).1.val = 1) : ∃ i, run.cell i = q := by
  have hp1 := run.position 1
  have hpN := run.position ⟨n + 1, by omega⟩
  simp only [Fin.val_one] at hp1
  simp only [Nat.dist] at hx
  apply run_hits_position run q
  · rcases hd with rfl | rfl <;> exact hy.trans (run.lane 1)
  · rcases hd with rfl | rfl <;> simp only [Direction.position] at hp1 ⊢ <;> omega
  · rcases hd with rfl | rfl <;> simp only [Direction.position] at hp1 hpN ⊢ <;> omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem endpoint_axis_horizontal_impossible (e : Endpoint) (he : e ∈ l.endpoints)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n vdepth : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hv : vdepth ∈ l.workingDepthCoordinates p)
    (hx : (run.cell 1).1.val = p.x e.port)
    (hy : (run.cell 1).2.val = if e.side = .upper then vdepth else p.H - vdepth) : False := by
  have hx0 := readLength_add_lt_x p e.port 0
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) 0
  have havoid := l.physicalInstance_ordinary_reader_step_avoiding p hl hM ha initial target e he hsu hm hvt ht
  rcases l.workingDepthCoordinates_bands p (l.endpoints_level_bounds p hl hM he).1
      (l.endpoints_level_bounds p hl hM he).2 hv with hshallow | hbranch | ⟨heM, hdeep⟩
  · let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨if e.inward then p.x e.port - 1 else p.x e.port + 1, by split <;> omega⟩, (run.cell 1).2)
    have hq := l.endpointOrdinaryBlockers_front_mem p hl hM ha e he hv hshallow (q := q) rfl hy
    obtain ⟨i, hi⟩ := horizontal_neighbor_hit run hn hd q rfl (by
      dsimp only [q]
      rw [hx]
      cases e.inward <;> simp only [Bool.false_eq_true, ite_true, ite_false, Nat.dist] <;> omega)
    exact havoid.2 d n run hn hp hb i (hi.symm ▸ hq)
  · let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨if e.inward then p.x e.port + 1 else p.x e.port - 1, by split <;> omega⟩, (run.cell 1).2)
    have hq := l.endpointOrdinaryBlockers_branch_mem p hl hM ha e he (q := q) rfl (hbranch ▸ hy)
    obtain ⟨i, hi⟩ := horizontal_neighbor_hit run hn hd q rfl (by
      dsimp only [q]
      rw [hx]
      cases e.inward <;> simp only [Bool.false_eq_true, ite_true, ite_false, Nat.dist] <;> omega)
    exact havoid.2 d n run hn hp hb i (hi.symm ▸ hq)
  · have hmax := workingRows_le_last l p hv
    have hband : run.cell 1 ∈ axisDeepBand p e.side e.port e.level := by
      refine ⟨?_, ?_⟩
      · rw [hx, Nat.dist_self]
        omega
      · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
    exact (l.physicalInstance_endpoint_deep_unvisited p hl hM ha initial target e he heM hband
      (hsu.tail hm) hvt ht) hp

private theorem axis_horizontal_impossible {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hfirst : run.cell 1 ∈ ordinaryAxis p upper.port) : False := by
  have hr := (Finset.mem_filter.mp hfirst).2
  have hadj : Adjacent d u.player (run.cell 1) := by
    have h := run.adjacent 0
    change Adjacent d (run.cell 0) (run.cell 1) at h
    rw [run.start] at h
    exact h
  have heven := x_even p upper.port
  have hstreet := l.physicalInstance_player_on_streets p hl hM ha initial target hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hrow : (run.cell 1).2 ∈ l.workingRowSet p := by
    rcases hstreet with hcol | hrow
    · have hx := l.streetColumnSet_even p hcol
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · rcases hd with rfl | rfl <;> exact hadj.2.symm ▸ hrow
  rcases (l.workingRowSet_iff p _).mp hrow with hzero | hH | ⟨vdepth, hv, hy | hy⟩
  · omega
  · omega
  · exact endpoint_axis_horizontal_impossible l p hl hM ha initial target upper hu hsu hm hvt ht run hn hp hb hd hv hr.1
      (by simpa only [hsuSide, ite_true] using hy)
  · exact endpoint_axis_horizontal_impossible l p hl hM ha initial target lower hlow hsu hm hvt ht run hn hp hb hd hv
      (by simpa only [hport] using hr.1) (by simpa only [hslSide, reduceCtorEq, ite_false] using hy)

/-- An actual successful step never exports a box from an ordinary shared main axis. -/
theorem physicalInstance_ordinaryAxis_no_export {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.ForwardStep (I).board none (ordinaryAxis p upper.port) u v := by
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb hfirst
  have hr := (Finset.mem_filter.mp hfirst).2
  have hframe : run.cell ⟨n + 1, by omega⟩ ∉ Boundary.frame := by
    intro hf
    have he := l.physicalInstance_ordinaryReaders_empty p hl hM ha initial target upper hu (hsu.tail hm) hvt ht
    have hhole := (mem_holes _).mp (he (Finset.mem_union_left _ hf))
    apply hhole
    rw [hb]
    exact Finset.mem_insert_self _ _
  cases d with
  | east => exact False.elim (axis_horizontal_impossible l p hl hM ha initial target hu hlow hsuSide hslSide hport
      hsu hm hvt ht run hn hp hb (Or.inl rfl) hfirst)
  | west => exact False.elim (axis_horizontal_impossible l p hl hM ha initial target hu hlow hsuSide hslSide hport
      hsu hm hvt ht run hn hp hb (Or.inr rfl) hfirst)
  | north | south =>
    have hl1 := run.lane 1
    have hlN := run.lane ⟨n + 1, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · have he : (run.cell ⟨n + 1, by omega⟩).1.val = (run.cell 1).1.val := hlN.trans hl1.symm
      exact he.trans hr.1
    · by_contra hnorth
      apply hframe
      exact (Boundary.mem_frame _).mpr ⟨.north, by
        simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
    · by_contra hsouth
      apply hframe
      exact (Boundary.mem_frame _).mpr ⟨.south, by
        simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]
        change (run.cell ⟨n + 1, by omega⟩).2.val + 1 = p.H + 1
        have hbound : (run.cell ⟨n + 1, by omega⟩).2.val < p.H + 1 := (run.cell ⟨n + 1, by omega⟩).2.isLt
        omega⟩

/-- The actual prefix carries the ordinary axis's no-export inventory relation. -/
theorem physicalInstance_ordinaryAxis_no_export_prefix {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (ordinaryAxis p upper.port)) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact l.physicalInstance_ordinaryAxis_no_export p hl hM ha initial target hu hlow hsuSide hslSide hport
    hsa hm (hbu.trans hut) ht

/-- The same no-export relation holds along every successful suffix. -/
theorem physicalInstance_ordinaryAxis_no_export_suffix {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Inventory.ForwardStep (I).board none (ordinaryAxis p upper.port)) u t := by
  apply enrich_path hut
  intro a b hua hm hbt
  exact l.physicalInstance_ordinaryAxis_no_export p hl hM ha initial target hu hlow hsuSide hslSide hport
    (hsu.trans hua) hm hbt ht

end Solution
end PushPuzzle.PushS.PortLayout
