/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.InventoryEmpty
public import PushS.PortEndpointRWall
public import PushS.PortEndpointOuterWalls
import all PushS.EndpointWalking
import all PushS.PortStreetSeparation
import all PushS.PortSegmentBounds
import all PushS.PortCentralStrip
import all PushS.PortSegments
import all PushS.Support
import all PushS.PortPageBackground
import all PushS.PortBackground

/-! Successful empty inventories on the actual last-level f corridors. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The complete ordinary f corridor, including its cell on the page frame. -/
@[expose] noncomputable def endpointFWalk (p : Scales.Parameters) (e : Endpoint) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q.1.val = EndpointStreet.f.column p e ∧
    ∃ v ≤ readDepth p e.level + 2, q.2.val = if e.side = .upper then v else p.H - v

private theorem mem_endpointFWalk (p : Scales.Parameters) (e : Endpoint)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointFWalk p e ↔ q.1.val = EndpointStreet.f.column p e ∧
      ∃ v ≤ readDepth p e.level + 2, q.2.val = if e.side = .upper then v else p.H - v := by
  classical
  simp only [endpointFWalk, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mem_endpointFWalk_iff (p : Scales.Parameters) (e : Endpoint)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointFWalk p e ↔ q.1.val = EndpointStreet.f.column p e ∧
      (if e.side = .upper then q.2.val ≤ readDepth p e.level + 2
        else p.H - (readDepth p e.level + 2) ≤ q.2.val) := by
  have hm := readDepth_add_lt_H p e.level
  have hq := q.2.isLt
  rw [mem_endpointFWalk]
  cases e.side <;> simp only [reduceCtorEq, ite_true, ite_false]
  · exact ⟨fun ⟨hx, v, hv, hy⟩ => ⟨hx, by omega⟩, fun ⟨hx, hy⟩ => ⟨hx, q.2.val, hy, rfl⟩⟩
  · constructor
    · rintro ⟨hx, v, hv, hy⟩
      exact ⟨hx, by omega⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, p.H - q.2.val, by omega, by omega⟩

/-- Every f-walk cell is emitted as a hole for every physical signal state. -/
theorem endpointFWalk_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointFWalk p e ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨hx, v, hv, hy⟩ := (mem_endpointFWalk p e q).mp hq
  have hc : q = l.endpointStreetCell p hl ha e he .f v hv :=
    Prod.ext (Fin.ext hx) (Fin.ext hy)
  rw [hc]
  exact l.endpointStreet_hole p hl hM ha state e he .f v hv

private theorem run_hits_position {w h n : ℕ} {B : Board w h} {d : Direction}
    {s : State w h} (run : Run B d s n) (q : Cell w h)
    (hl : d.lane q = d.lane s.player) (hlo : d.position s.player ≤ d.position q)
    (hhi : d.position q ≤ d.position (run.cell ⟨n + 1, by omega⟩)) :
    ∃ i, run.cell i = q := by
  have hp := run.position ⟨n + 1, by omega⟩
  let k := (d.position q - d.position s.player).toNat
  have hk : (k : ℤ) = d.position q - d.position s.player :=
    Int.toNat_of_nonneg (by omega)
  let i : Fin (n + 2) := ⟨k, by omega⟩
  refine ⟨i, d.cell_ext ((run.lane i).trans hl.symm) ?_⟩
  rw [run.position i]
  change d.position s.player + (k : ℤ) = d.position q
  omega

private theorem fwalk_vertical_retained (p : Scales.Parameters) (e : Endpoint)
    {G : Finset (Cell (p.W + 1) (p.H + 1))}
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.f.column p e →
      q.2.val = (if e.side = .upper then readDepth p e.level + 3 else p.H - (readDepth p e.level + 3)) → q ∈ G)
    {B : Board (p.W + 1) (p.H + 1)} {s : State (p.W + 1) (p.H + 1)} {n : ℕ}
    {d : Direction} (hd : d = .north ∨ d = .south) (run : Run B d s n)
    (havoid : ∀ i, run.cell i ∉ G) (hfirst : run.cell 1 ∈ endpointFWalk p e) :
    run.cell ⟨n + 1, by omega⟩ ∈ endpointFWalk p e := by
  obtain ⟨hx, hy⟩ := (mem_endpointFWalk_iff p e _).mp hfirst
  have hY := readDepth_add_lt_H p e.level
  let q : Cell (p.W + 1) (p.H + 1) := ((run.cell 1).1,
    ⟨if e.side = .upper then readDepth p e.level + 3 else p.H - (readDepth p e.level + 3), by split <;> omega⟩)
  have hqG := hdeep q hx rfl
  have hp1 := run.position 1
  have hpN := run.position ⟨n + 1, by omega⟩
  simp only [Fin.val_one] at hp1 hpN
  have hl1 := run.lane 1
  have hlN := run.lane ⟨n + 1, by omega⟩
  have hxN : (run.cell ⟨n + 1, by omega⟩).1.val = EndpointStreet.f.column p e := by
    rcases hd with rfl | rfl <;> simp only [Direction.lane] at hl1 hlN <;> omega
  by_contra hout
  have hnot : ¬(if e.side = .upper then (run.cell ⟨n + 1, by omega⟩).2.val ≤ readDepth p e.level + 2
      else p.H - (readDepth p e.level + 2) ≤ (run.cell ⟨n + 1, by omega⟩).2.val) := by
    intro hh
    exact hout ((mem_endpointFWalk_iff p e _).mpr ⟨hxN, hh⟩)
  apply (show (∃ i, run.cell i = q) → False from fun ⟨i, hi⟩ => havoid i (hi.symm ▸ hqG))
  apply run_hits_position run q
  · rcases hd with rfl | rfl <;> exact hl1
  · rcases hd with rfl | rfl <;> cases hs : e.side <;>
      dsimp only [q] <;>
      simp only [Direction.position, hs, reduceCtorEq, ite_true, ite_false] at hp1 hpN hy hnot ⊢ <;> omega
  · rcases hd with rfl | rfl <;> cases hs : e.side <;>
      dsimp only [q] <;>
      simp only [Direction.position, hs, reduceCtorEq, ite_true, ite_false] at hp1 hpN hy hnot ⊢ <;> omega

private theorem fwalk_horizontal_impossible (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {G : Finset (Cell (p.W + 1) (p.H + 1))}
    (houter : ∀ q ∈ endpointFWalk p e, q ∉ Boundary.frame → q.2 ∈ l.workingRowSet p →
      ∀ r, Adjacent (if e.inward then .west else .east) q r → r ∈ G)
    {B : Board (p.W + 1) (p.H + 1)} {s : State (p.W + 1) (p.H + 1)} {n : ℕ}
    {d : Direction} (hd : d = .east ∨ d = .west) (run : Run B d s n) (hn : 0 < n)
    (havoid : ∀ i, run.cell i ∉ G) (hfirst : run.cell 1 ∈ endpointFWalk p e)
    (hf : run.cell 1 ∉ Boundary.frame) (hrow : (run.cell 1).2 ∈ l.workingRowSet p) : False := by
  have hx := ((mem_endpointFWalk p e _).mp hfirst).1
  have hm := auxiliary_margin p e ((l.endpoints_port_lt hl he).trans_le ha)
  have hx0 := readLength_add_lt_x p e.port e.level
  have hfpos : 0 < (run.cell 1).1.val := by
    rw [hx, EndpointStreet.column_f]
    split <;> omega
  have hfend : (run.cell 1).1.val + 1 < p.W + 1 := by
    have hb : EndpointStreet.f.column p e + 32 < p.W := hm.1
    omega
  let r : Cell (p.W + 1) (p.H + 1) :=
    (⟨if e.inward then (run.cell 1).1.val - 1 else (run.cell 1).1.val + 1, by split <;> omega⟩,
      (run.cell 1).2)
  have hadj : Adjacent (if e.inward then .west else .east) (run.cell 1) r := by
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true, Adjacent, r] <;>
      constructor <;> first | trivial | omega
  have hr := houter _ hfirst hf hrow r hadj
  have hp1 := run.position 1
  have hpN := run.position ⟨n + 1, by omega⟩
  simp only [Fin.val_one] at hp1 hpN
  have hhit : ∃ i, run.cell i = r := by
    apply run_hits_position run r
    · rcases hd with rfl | rfl <;> exact run.lane 1
    · rcases hd with rfl | rfl <;> cases hi : e.inward <;>
        simp only [Direction.position, r, hi, Bool.false_eq_true, ite_true, ite_false] at hp1 hpN ⊢ <;> omega
    · rcases hd with rfl | rfl <;> cases hi : e.inward <;>
        simp only [Direction.position, r, hi, Bool.false_eq_true, ite_true, ite_false] at hp1 hpN ⊢ <;> omega
  obtain ⟨i, hi⟩ := hhit
  exact havoid i (hi.symm ▸ hr)

private theorem fwalk_forward (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {G : Finset (Cell (p.W + 1) (p.H + 1))}
    (houter : ∀ q ∈ endpointFWalk p e, q ∉ Boundary.frame → q.2 ∈ l.workingRowSet p →
      ∀ r, Adjacent (if e.inward then .west else .east) q r → r ∈ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.f.column p e →
      q.2.val = (if e.side = .upper then readDepth p e.level + 3 else p.H - (readDepth p e.level + 3)) → q ∈ G)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hm : Freeze.AvoidingStep B cap G s t) (hframe : Disjoint s.boxes Boundary.frame)
    (hs : s.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p))
    (ht : t.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p)) :
    Inventory.ForwardStep B cap (endpointFWalk p e) s t := by
  refine ⟨hm.1, ?_⟩
  intro d n run hn hp hb hfirst
  have havoid := hm.2 d n run hn hp hb
  have hf : run.cell 1 ∉ Boundary.frame := fun hf =>
    Finset.disjoint_left.mp hframe (run.first_occupied hn) hf
  have hadj : Adjacent d s.player (run.cell 1) := by
    simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, run.start] using run.adjacent 0
  rw [hp] at ht
  cases d with
  | north => exact fwalk_vertical_retained p e hdeep (Or.inl rfl) run havoid hfirst
  | south => exact fwalk_vertical_retained p e hdeep (Or.inr rfl) run havoid hfirst
  | east =>
    have hr := Support.horizontal_row (l.streetColumnSet_separated p) hs ht hadj.2 hadj.1.symm
    exact (fwalk_horizontal_impossible l p hl ha e he houter (Or.inl rfl) run hn
      havoid hfirst hf (hadj.2.symm ▸ hr)).elim
  | west =>
    have hr := Support.horizontal_row (l.streetColumnSet_separated p) ht hs hadj.2.symm hadj.1
    exact (fwalk_horizontal_impossible l p hl ha e he houter (Or.inr rfl) run hn
      havoid hfirst hf hr).elim

private theorem fwalk_empty_of_forward (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {u t : State (p.W + 1) (p.H + 1)}
    (hr : Relation.ReflTransGen (Inventory.ForwardStep
      (l.physicalInstance p hl hM ha initial target).board none (endpointFWalk p e)) u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    endpointFWalk p e ⊆ holes u := by
  have htR : Disjoint t.boxes (endpointFWalk p e) := by
    apply Finset.disjoint_left.mpr
    intro q hq hwalk
    have hh := l.endpointFWalk_subset_encoded p hl hM ha target e he hwalk
    rw [← l.physicalInstance_goal_holes p hl hM ha initial target, ← ht] at hh
    exact (Finset.mem_compl.mp hh) hq
  have huR := Inventory.reachable_source_empty hr htR
  intro q hq
  exact (mem_holes _).mpr (fun hb => Finset.disjoint_left.mp huR hb hq)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels)

include he heM

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- No actual step in a successful play exports a box from a last-level f corridor. -/
theorem physicalInstance_endpoint_fwalk_forward {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.ForwardStep (I).board none (endpointFWalk p e) u v := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  have hpre := l.physicalInstance_page_avoiding_prefix p hl hM ha initial target hsu hut ht
  have hstep := step_page_avoiding l p hl hM ha initial target hsu hm hvt ht
  have hguard := (l.endpointOuterWalls_closure p hl hM ha initial target e he heM).step hpre hstep
  have hholes : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
    change t.boxesᶜ = _
    rw [ht]
    exact l.physicalInstance_goal_holes p hl hM ha initial target
  have hf : Disjoint t.boxes Boundary.frame := by
    apply Finset.disjoint_left.mpr
    intro q hq hframe
    have hh := l.encodedSegments_frame_subset p target hframe
    rw [← hholes] at hh
    exact (mem_holes _).mp hh hq
  apply fwalk_forward l p hl ha e he ?_ ?_ hguard
    (Boundary.reachable_frame_empty hut hf)
    (l.physicalInstance_player_on_streets p hl hM ha initial target hsu hut ht)
    (l.physicalInstance_player_on_streets p hl hM ha initial target (hsu.tail hm) hvt ht)
  · intro q hq hqf hy r hadj
    have hq' := (mem_endpointFWalk_iff p e q).mp hq
    apply l.endpointOuterWalls_guard p hl hM ha e he heM hq'.1 hy hqf ?_ hadj
    have hd : readDepth p e.level = p.Y p.levels := by
      rw [heM, readDepth_eq p p.levels_pos le_rfl]
    have hqy := q.2.isLt
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false, hd] at hq' ⊢ <;> omega
  · intro q hx hy
    have hd : readDepth p e.level = p.Y p.levels := by
      rw [heM, readDepth_eq p p.levels_pos le_rfl]
    exact Finset.mem_union_right _ (l.endpointStreet_deep_blocker p hl hM ha e he heM .f hx
      (by simpa only [hd] using hy))

/-- Every last-level f corridor stays empty throughout every successful physical play. -/
theorem physicalInstance_endpoint_fwalk_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : endpointFWalk p e ⊆ holes u := by
  have hr : Relation.ReflTransGen (Inventory.ForwardStep (I).board none (endpointFWalk p e)) u t := by
    apply enrich_path hut
    intro a b hua hm hbt
    exact l.physicalInstance_endpoint_fwalk_forward p hl hM ha initial target e he heM
      (hsu.trans hua) hm hbt ht
  exact fwalk_empty_of_forward l p hl hM ha initial target e he hr ht

end Solution
end PushPuzzle.PushS.PortLayout
