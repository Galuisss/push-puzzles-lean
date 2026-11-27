/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateGapMotion
public import PushS.PortGatePlayerColumns
public import PushS.PortGateTrainUnique
import all PushS.PortGateIndexing
import all PushS.PortBackground

/-! A current relay-fault J cannot be entered or restored from outside on a successful physical play. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- A genuine actual relay fault whose player is outside the current J interval. -/
structure GateRelayFault (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (u : State (p.W + 1) (p.H + 1)) (blocks : ThreeBlocks) : Prop where
  shape : GateTrainShape p g kind u blocks
  short : 6 ≤ (gateTrainPlacement p g blocks).short
  right : 2 ≤ (gateTrainPlacement p g blocks).right
  outside : u.player ∉ gateRightGap p g (gateTrainPlacement p g blocks)

private theorem horizontal_excluded {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks} (hs : GateTrainShape p g kind u b)
    (hshape : g.right = g.left + 2) (hshort : 6 ≤ (gateTrainPlacement p g b).short)
    (hright : 2 ≤ (gateTrainPlacement p g b).right) {q r : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∉ gateRightGap p g (gateTrainPlacement p g b)) (hr : r ∈ gateRightGap p g (gateTrainPlacement p g b))
    (hy : q.2.val = p.H - readDepth p 1) (hdx : q.1.val + 1 = r.1.val ∨ r.1.val + 1 = q.1.val)
    (hhole : q ∈ holes u) : False := by
  have hb := gateRightGap_relay_bounds p g _ hshort hright hr
  have hrange : -2 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧ (q.1.val : ℤ) - p.x (g.left + 1) ≤ 12 := by
    rcases hdx with hdx | hdx <;> omega
  have hc := (hs.core_hole hshape hy hrange).mp hhole
  have hrleft := (Finset.mem_filter.mp hr).2.2.1
  rcases hc with hG | hJ
  · have hGright := hG.2
    rcases hdx with hdx | hdx <;> omega
  · exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hJ⟩)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The real next player cannot enter the previous J of an actual relay fault. -/
theorem physicalInstance_gate_relay_no_entry {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) :
    v.player ∉ gateRightGap p g (gateTrainPlacement p g b) := by
  intro hin
  have hb := gateRightGap_relay_bounds p g _ fault.short fault.right hin
  have hy := (Finset.mem_filter.mp hin).2.1
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  obtain ⟨d, hmove⟩ := hm
  have hadj := players_adjacent hmove
  have hh : u.player ∈ holes u := (mem_holes _).mpr hmove.valid_source.2.2
  have hshape := (placement_gate_shape l hg hk).2
  cases d with
  | north =>
    have hx := congrArg Fin.val hadj.1
    have hyy := hadj.2
    exact l.physicalInstance_gate_relay_vertical_excluded p hl hM ha initial target hg hk hsu hut ht
      (Or.inr (by omega)) ⟨by omega, by omega⟩
  | south =>
    have hx := congrArg Fin.val hadj.1
    have hyy := hadj.2
    exact l.physicalInstance_gate_relay_vertical_excluded p hl hM ha initial target hg hk hsu hut ht
      (Or.inl (by omega)) ⟨by omega, by omega⟩
  | east =>
    have hyy := congrArg Fin.val hadj.2
    exact horizontal_excluded fault.shape hshape fault.short fault.right fault.outside hin
      (by omega) (Or.inl hadj.1.symm) hh
  | west =>
    have hyy := congrArg Fin.val hadj.2
    exact horizontal_excluded fault.shape hshape fault.short fault.right fault.outside hin
      (by omega) (Or.inr hadj.1) hh

/-- One actual successful step preserves the complete relay fault and keeps the player outside its current J. -/
theorem physicalInstance_gate_relay_failure_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) : ∃ c, GateRelayFault p g kind v c := by
  obtain ⟨before, after, motion⟩ := l.physicalInstance_gate_train_motion p hl hM ha initial target hg hk hsu hm hvt ht
  have heq := motion.before_shape.unique fault.shape
  subst before
  have hshape := (placement_gate_shape l hg hk).2
  have hp := motion.relay_fault_preserved hshape fault.outside fault.short fault.right
  have hout := l.physicalInstance_gate_relay_no_entry p hl hM ha initial target hg hk hsu hm hvt ht fault
  exact ⟨after, motion.after_shape, hp.1, hp.2, fun h => hout (motion.right_gap_subset hshape fault.outside h)⟩

/-- The same actual successful suffix preserves a relay fault and its inaccessible current J. -/
theorem physicalInstance_gate_relay_failure_suffix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) :
    ∃ c, GateRelayFault p g kind t c := by
  have hr : Relation.ReflTransGen (fun x y => Step (I).board none x y ∧
      ∀ blocks, GateRelayFault p g kind x blocks → ∃ next, GateRelayFault p g kind y next) u t := by
    apply enrich_path hut
    intro x y hux hxy hyt
    exact ⟨hxy, fun blocks hf => l.physicalInstance_gate_relay_failure_step p hl hM ha initial target hg hk
      (hsu.trans hux) hxy hyt ht hf⟩
  clear hut ht
  induction hr with
  | refl => exact ⟨b, fault⟩
  | tail _ hm ih => obtain ⟨c, hc⟩ := ih; exact hm.2 c hc

end Solution

/-- A relay fault outside its J cannot successfully reach a canonical complete physical goal. -/
theorem physicalInstance_gate_relay_failure_impossible (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial : SignalState) (axes : List Bool) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial (l.canonical axes)).board none
      (l.physicalInstance p hl hM ha initial (l.canonical axes)).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial (l.canonical axes)).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial (l.canonical axes)).board.goals)
    {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) : False := by
  obtain ⟨c, hf⟩ := l.physicalInstance_gate_relay_failure_suffix p hl hM ha initial (l.canonical axes) hg hk hsu hut ht fault
  have hc := l.physicalInstance_gate_train_target_shape p hl hM ha initial (l.canonical axes) hg hk ht
  have heq := hf.shape.unique hc
  have hp := hf.short
  have hr := hf.right
  rw [heq] at hp hr
  exact l.canonical_gate_no_relay_fault p axes hg hk ⟨hp, hr⟩

end PushPuzzle.PushS.PortLayout
