/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateProbeReadoutGeometry
public import Push.AcceptanceProbeNumerics
public import Push.AcceptanceRoundLaneProjection
public import Push.AcceptanceSoundnessGateProbeLedger
public import Push.AcceptanceAxisReadoutOuter
public import Push.AcceptanceProgramProbeStockCells
import all Push.AcceptanceGateProbeReadoutGeometry
import all Push.AcceptanceProbePartners
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramPrefix
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceSoundnessCentralRead

/-! Genuine terminal gate words determine the real numerical probe threshold. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hs : upper.side = .upper)
  (hp : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hg hk hu hs hp

/-- The actual residual keeps the literal upper probe exactly at the genuine gate word's threshold. -/
theorem canonical_gate_probe_mem {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : GateAxisPlacement} (word : GateAxisReadout p g upper t a)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x upper.port)
    (hy : q.2.val = p.Y upper.level + 2) :
    q ∈ AcceptanceProbeNumerics.residual l p target t ↔ a.parameter ≤ 1 := by
  classical
  let T := targetHoles l p target
  let E := holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let A := roundResidual stages T E 6
  let B := roundResidual stages T E 7
  let C := roundResidual stages T E 8
  let x := p.x upper.port
  let cells := Scan.lineCells (w := p.W + 1) (h := p.H + 1) .north x
  let front := cells.take (readDepth p upper.level + 2)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have hshift := canonical_endpoint_shift_zero l p hl hM haxes initial target hr accepted hu
    (word.upper_endpoint hs hp)
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
  have hY := readDepth_ge p hj hjm
  have hD := readDepth_add_lt_D p upper.level
  have hH : p.H = 2 * p.D := rfl
  have hread := readDepth_eq p hj hjm
  have hhalf : 0 < q.2.val ∧ q.2.val < p.D := by omega
  have hword := word.upper_holes q (hx.trans (congrArg p.x hp)) hhalf
  rw [hshift] at hword
  constructor
  · intro hq
    have hqE := scan_subset (roundResidual_eval stages T E 13 hc) hq
    have hw := hword.mp hqE
    omega
  · intro hthreshold
    have hfront : ((A.filter fun q => q.1.val = x).filter fun q => q ∈ front) =
        mainSourceFront l p target upper := by
      have hinput : (A.filter fun q => q.1.val = x) = holes t ∩ ordinaryAxis p upper.port :=
        canonical_main_input_axis l p hl hM haxes initial target (l.endpoints_port_lt hl hu) hr accepted
      rw [hinput]
      exact gate_upper_front_eq l p hl hM haxes target hu hs hp word hshift hthreshold
    have hcard : ((A.filter fun q => q.1.val = x).filter fun q => q ∈ front).card = 2 := by
      rw [hfront]
      exact mainSourceFront_card l p hl hM haxes target upper hu
    have i6 : stages[6]? = some (mainRound l p .upper) := by
      simp only [stages, schedule, preparation, frameSchedule, mainRound, mainTop,
        List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, ite_true]
    have loss := canonical_main_column_loss l p hl hM haxes initial target upper hu hr accepted
    simp only [hs, ite_true, Nat.reduceAdd] at loss
    have north := round_lane_projection .north _ (emit (stages.take 6) T).remaining x 2
      (roundResidual_step stages T E 6 hc i6).1 loss
    change Scan.consume cells 2 (A.filter fun q => q.1.val = x) = some (B.filter fun q => q.1.val = x) at north
    have expected := consume_prefix front (cells.drop (readDepth p upper.level + 2))
      (A.filter fun q => q.1.val = x)
    rw [hcard] at expected
    have hlist : front ++ cells.drop (readDepth p upper.level + 2) = cells := List.take_append_drop _ _
    rw [hlist] at expected
    have hremaining : (B.filter fun q => q.1.val = x) =
        (A.filter fun q => q.1.val = x) \ front.toFinset := Option.some.inj (north.symm.trans expected)
    have hqA : q ∈ A.filter (fun q => q.1.val = x) := by
      have hinput := canonical_main_input_axis l p hl hM haxes initial target
        (l.endpoints_port_lt hl hu) hr accepted
      apply (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hinput).mpr
      exact Finset.mem_inter.mpr ⟨hword.mpr (by right; omega),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hhalf.1, by omega⟩⟩
    have hq7 : q ∈ B.filter (fun q => q.1.val = x) := by
      rw [hremaining]
      apply Finset.mem_sdiff.mpr
      refine ⟨hqA, ?_⟩
      intro hqfront
      have hdepth := (mem_line_prefix .north _ _ q).mp (List.mem_toFinset.mp hqfront)
      change q.1.val = x ∧ q.2.val < readDepth p upper.level + 2 at hdepth
      omega
    have hlower := canonical_gate_main_lower_stock l p hl hM haxes initial target hg hk hr accepted
    rw [← hp] at hlower
    have hq8 : q ∈ C.filter (fun q => q.1.val = x) := hlower.symm ▸ hq7
    have hkeep := canonical_main_to_probe_stock l p hl hM haxes initial target
      (l.endpoints_port_lt hl hu) hr accepted
    have hq13 : q ∈ (AcceptanceProbeNumerics.residual l p target t).filter
        (fun q => q.1.val = x) := hkeep.symm ▸ hq8
    exact (Finset.mem_filter.mp hq13).1

/-- The real one-point numerical observation of a genuine terminal gate word is its upper threshold. -/
theorem canonical_gate_probe_threshold (i : Fin l.portCount) (hi : i.val = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : GateAxisPlacement} (word : GateAxisReadout p g upper t a) :
    AcceptanceProbeNumerics.observed l p hl target t i = if a.parameter ≤ 1 then 1 else 0 := by
  classical
  obtain ⟨chosenMem, chosenSide, chosenPort⟩ := AcceptanceProbe.upperEndpoint_spec l hl i
  have chosen := l.endpoints_key_injective hl chosenMem hu (chosenSide.trans hs.symm) (chosenPort.trans hi)
  have hlevel : AcceptanceProbe.level l hl i = upper.level := congrArg Endpoint.level chosen
  let point := probeCell l p hl hM haxes i
  have hpointX : point.1.val = p.x upper.port := by change p.x i.val = _; rw [hi]
  have hpointY : point.2.val = p.Y upper.level + 2 := by change p.Y (AcceptanceProbe.level l hl i) + 2 = _; rw [hlevel]
  have hmem := canonical_gate_probe_mem l p hl hM haxes initial target hg hk hu hs hp hr accepted word hpointX hpointY
  have unique (q : Cell (p.W + 1) (p.H + 1))
      (hx : q.1.val = p.x i.val) (hy : q.2.val = p.Y (AcceptanceProbe.level l hl i) + 2) : q = point :=
    Prod.ext (Fin.ext hx) (Fin.ext hy)
  let R := AcceptanceProbeNumerics.residual l p target t
  change (R.filter fun q => q.1.val = p.x i.val ∧ q.2.val = p.Y (AcceptanceProbe.level l hl i) + 2).card = _
  by_cases hthreshold : a.parameter ≤ 1
  · have he : (R.filter fun q => q.1.val = p.x i.val ∧
        q.2.val = p.Y (AcceptanceProbe.level l hl i) + 2) = {point} := by
      ext q
      constructor
      · intro hq
        obtain ⟨_, hx, hy⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_singleton.mpr (unique q hx hy)
      · intro hq
        have hqp := Finset.mem_singleton.mp hq
        subst q
        exact Finset.mem_filter.mpr ⟨hmem.mpr hthreshold, rfl, rfl⟩
    rw [he, Finset.card_singleton, ite_eq_left hthreshold]
  · have he : (R.filter fun q => q.1.val = p.x i.val ∧
        q.2.val = p.Y (AcceptanceProbe.level l hl i) + 2) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro q hq
      obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
      exact hthreshold (hmem.mp (unique q hx hy ▸ hq))
    rw [he, Finset.card_empty, ite_eq_right hthreshold]

/-- A genuine gate word whose actual observation equals the target bit decodes that target threshold. -/
theorem canonical_gate_target_threshold (i : Fin l.portCount) (hi : i.val = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : GateAxisPlacement} (word : GateAxisReadout p g upper t a)
    (observed : AcceptanceProbeNumerics.observed l p hl target t i = (target.getD i.val false).toNat) :
    target.getD i.val false = true ↔ a.parameter ≤ 1 := by
  have threshold := canonical_gate_probe_threshold l p hl hM haxes initial target hg hk hu hs hp i hi hr accepted word
  rw [threshold] at observed
  by_cases hthreshold : a.parameter ≤ 1 <;> cases bit : target.getD i.val false <;>
    simp only [hthreshold, ite_true, ite_false, bit, Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, iff_false, iff_true] at observed ⊢ <;> omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
