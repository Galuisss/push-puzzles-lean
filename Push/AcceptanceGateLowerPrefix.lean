/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateLowerPrefixStep
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortWalkBudget

/-! The real gate middle-axis lower half has one work-adjacent hole gap before any deficit cancellation. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceColumnPrefix

private theorem canonical_gate_lower_prefix_initial (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    Closed (w := p.W + 1) (h := p.H + 1) (p.x (g.left + 1)) p.D (p.H - readDepth p 1)
      (l.canonicalInstance p hl hM haxes initial target).initial := by
  let I := l.canonicalInstance p hl hM haxes initial target
  obtain ⟨upper, hu, hs, hp⟩ := l.endpoints_upper_exists hl (gate_middle_lt l hl (placement_gate_mem l hg hk))
  have holes : PushS.holes (I.initial : State (p.W + 1) (p.H + 1)) = targetHoles l p initial :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  have raw (q : Cell (p.W + 1) (p.H + 1)) := l.encodedSegments_gateAxis_train_boxes p hl hM haxes
    (l.canonical initial) hg hk hu hs hp (I.initial : State (p.W + 1) (p.H + 1)) holes q
  have hDu := readDepth_add_lt_D p upper.level
  have hYu := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have hbit := Bool.toNat_le ((l.canonical initial).axes.getD upper.port false)
  intro q hq r hr hqr hbox
  obtain ⟨_, hqx, hqlo, hqhi⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, hrx, hrlo, hrhi⟩ := Finset.mem_filter.mp hr
  have hrR : r ∈ gateAxis p (g.left + 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrx, by omega, hrhi⟩
  have hrbox : r ∈ (BoxMask.keep I.initial (gateAxis p (g.left + 1))).boxes := Finset.mem_inter.mpr ⟨hbox, hrR⟩
  have hrslots := ((raw r).mp hrbox).2
  rw [TwoBlocks.mem_slots] at hrslots
  simp only [gateAxisTrainBlocks] at hrslots
  have hqslots : (q.2.val : ℤ) ∈ (gateAxisTrainBlocks p upper (l.canonical initial)).slots := by
    rw [TwoBlocks.mem_slots]
    simp only [gateAxisTrainBlocks]
    right
    omega
  exact (Finset.mem_inter.mp ((raw q).mpr ⟨hqx, hqslots⟩)).1

/-- Every real accepted gate lower half remains a prefix of boxes, followed by a single work-adjacent hole gap. -/
theorem canonical_gate_lower_prefix (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Closed (p.x (g.left + 1)) p.D (p.H - readDepth p 1) u := by
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have start := canonical_gate_lower_prefix_initial l p hl hM haxes initial target hg hk
  let P : State (p.W + 1) (p.H + 1) → Prop := Closed (p.x (g.left + 1)) p.D (p.H - readDepth p 1)
  have decorated : Relation.ReflTransGen (fun a b => Step
      (l.canonicalInstance p hl hM haxes initial target).board none a b ∧ (P a → P b))
      (l.canonicalInstance p hl hM haxes initial target).initial u := by
    apply Path.enrich hsu
    intro a b hsa step hbu
    exact ⟨step, canonical_gate_lower_prefix_step l p hl hM haxes initial target hgate hi
      hsa step (hbu.trans hut) accepted⟩
  clear hsu hut
  induction decorated with
  | refl => exact start
  | tail _ step ih => exact step.2 ih

/-- The complete actual terminal lower-half hole stock is one interval ending immediately before the gate work row. -/
theorem canonical_gate_lower_holes_suffix (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∃ gap : ℕ, gap ≤ (p.H - readDepth p 1) - p.D - 1 ∧
      ∀ q ∈ gateAxis p (g.left + 1), p.D < q.2.val →
        (q ∈ holes t ↔ (p.H - readDepth p 1) - gap ≤ q.2.val) := by
  obtain ⟨gap, hbound, hgap⟩ := (canonical_gate_lower_prefix l p hl hM haxes initial target hgate hg hk run .refl accepted).holes_suffix
  refine ⟨gap, hbound, ?_⟩
  intro q hq hlow
  have hr := (Finset.mem_filter.mp hq).2
  exact hgap q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1, hlow, hr.2.2⟩)

/-- Any actual lower-half terminal gate-axis hole forces the nearest-work-row cell to be a hole as well. -/
theorem canonical_gate_lower_hole_near_work (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q r : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ holes t ∩ gateAxis p (g.left + 1))
    (hqlo : p.D < q.2.val) (hrx : r.1.val = p.x (g.left + 1))
    (hry : r.2.val + 1 = p.H - readDepth p 1) : r ∈ holes t := by
  have closed := canonical_gate_lower_prefix l p hl hM haxes initial target hgate hg hk run .refl accepted
  obtain ⟨hqhole, hqaxis⟩ := Finset.mem_inter.mp hq
  have hqdata := (Finset.mem_filter.mp hqaxis).2
  apply (mem_holes r).mpr
  intro hrbox
  have hqBand : q ∈ band (p.x (g.left + 1)) p.D (p.H - readDepth p 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqdata.1, hqlo, hqdata.2.2⟩
  have hrBand : r ∈ band (p.x (g.left + 1)) p.D (p.H - readDepth p 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrx, by omega, by omega⟩
  exact (mem_holes q).mp hqhole (closed q hqBand r hrBand (by omega) hrbox)

end PushPuzzle.Push.AcceptanceSoundness
