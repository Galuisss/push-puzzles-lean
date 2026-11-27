/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceRoundLaneProjection
public import Push.AcceptanceSoundnessProbeOrdinary
public import Push.AcceptanceAxisReadoutMedian
public import Push.AcceptanceAxisReadoutOuter
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramMainStockGeometry
import all PushS.PortOrdinaryAxis
import all Push.Scan

/-! The actual main reads retain the genuine ordinary word's median probe on its physical column. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- Two real main reads leave precisely the physical median probe of a genuine terminal ordinary axis. -/
theorem canonical_ordinary_main_probe_stock {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : OrdinaryAxisPlacement} (word : OrdinaryAxisReadout p upper lower t a) :
    (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (holes t) 13).filter (fun q => q.1.val = p.x upper.port) =
      {ordinaryProbe p upper lower a.parameter ((l.endpoints_port_lt hl hu).trans_le haxes)} := by
  let T := targetHoles l p target
  let E := holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let A := roundResidual stages T E 6
  let B := roundResidual stages T E 7
  let C := roundResidual stages T E 8
  let F := E \ Boundary.frame
  let x := p.x upper.port
  let probe := ordinaryProbe p upper lower a.parameter ((l.endpoints_port_lt hl hu).trans_le haxes)
  let result := insert probe (F.filter fun q => q.1.val ≠ x)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have i6 : stages[6]? = some (mainRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainTop, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, ite_true]
  have i7 : stages[7]? = some (mainRound l p .lower) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainBottom, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, reduceCtorEq, ite_false]
  have loss6 := canonical_main_column_loss l p hl hM haxes initial target upper hu hr accepted
  have loss7 := canonical_main_column_loss l p hl hM haxes initial target lower hlow hr accepted
  simp only [hsuSide, hslSide, hport, ite_true, reduceCtorEq, ite_false, Nat.reduceAdd] at loss6 loss7
  have north := round_lane_projection .north _ (emit (stages.take 6) T).remaining x 2
    (roundResidual_step stages T E 6 hc i6).1 loss6
  have south := round_lane_projection .south _ (emit (stages.take 7) T).remaining x 2
    (roundResidual_step stages T E 7 hc i7).1 loss7
  have hu0 := canonical_endpoint_shift_zero l p hl hM haxes initial target hr accepted hu (word.upper_endpoint hsuSide)
  have hl0 := canonical_endpoint_shift_zero l p hl hM haxes initial target hr accepted hlow
    (word.lower_endpoint hslSide hport)
  have upperDepth := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have lowerDepth := readDepth_ge p (l.endpoints_level_bounds p hl hM hlow).1 (l.endpoints_level_bounds p hl hM hlow).2
  have median : Scan.eval [.read .north x 2, .read .south x 2] F = some result :=
    ordinary_two_reads_probe word ((l.endpoints_port_lt hl hu).trans_le haxes) (by omega) (by omega) hu0 hl0
      (fun q hx hy hq => (mem_holes q).mp hq
        (canonical_main_central_occupied l p hl hM haxes initial target (l.endpoints_port_lt hl hu) hx (by omega) hr .refl accepted))
  obtain ⟨G, hG, hresult⟩ := Option.bind_eq_some_iff.mp median
  have hSouth : (Scan.Instruction.read .south x 2).eval G = some result := by
    simpa only [Scan.eval, Option.bind_fun_some] using hresult
  have northExpected := Scan.read_lane_restrict hG
  have southExpected := Scan.read_lane_restrict hSouth
  have initialStock : A.filter (fun q => q.1.val = x) = F.filter (fun q => q.1.val = x) := by
    have axisInput : (A.filter (fun q => q.1.val = x) : Finset (Cell (p.W + 1) (p.H + 1))) =
        holes t ∩ ordinaryAxis p upper.port :=
      canonical_main_input_axis l p hl hM haxes initial target (l.endpoints_port_lt hl hu) hr accepted
    apply axisInput.trans
    ext q
    have hb := q.2.isLt
    have hx0 := readLength_add_lt_x p upper.port 0
    have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl hu).trans_le haxes) 0
    simp only [F, E, ordinaryAxis, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, Boundary.frame, Boundary.edge, Finset.mem_union, x]
    by_cases hx : q.1.val = p.x upper.port
    · have qx0 : 0 < q.1.val := by omega
      have qxW : q.1.val < p.W := by omega
      simp only [hx, true_and, and_true]
      apply and_congr_right
      intro _
      omega
    · simp only [hx, false_and, and_false]
  change Scan.consume (Scan.lineCells .north x) 2 (A.filter fun q => q.1.val = x) = some (B.filter fun q => q.1.val = x) at north
  rw [initialStock] at north
  have mid : B.filter (fun q => q.1.val = x) = G.filter (fun q => q.1.val = x) :=
    Option.some.inj (north.symm.trans northExpected)
  change Scan.consume (Scan.lineCells .south x) 2 (B.filter fun q => q.1.val = x) = some (C.filter fun q => q.1.val = x) at south
  rw [mid] at south
  have final := Option.some.inj (south.symm.trans southExpected)
  rw [canonical_main_to_probe_stock l p hl hM haxes initial target (l.endpoints_port_lt hl hu) hr accepted]
  change C.filter (fun q => q.1.val = x) = {probe}
  rw [final]
  ext q
  simp only [result, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  have probeX : probe.1.val = x := rfl
  constructor
  · rintro ⟨h | ⟨_, hn⟩, hx⟩
    · exact h
    · exact False.elim (hn hx)
  · rintro rfl
    exact ⟨Or.inl rfl, probeX⟩

include hM in
/-- The genuine physical median lies on a selected probe row exactly at the upper-input threshold. -/
private theorem ordinaryProbe_mem_probeRows_iff {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hsuSide : upper.side = .upper)
    (parameter : ℕ) :
    (ordinaryProbe p upper lower parameter ((l.endpoints_port_lt hl hu).trans_le haxes)).2.val ∈ probeRows l p ↔
      parameter ≤ 1 := by
  have upperDepth := l.endpoints_level_bounds p hl hM hu
  by_cases threshold : parameter ≤ 1
  · simp only [ordinaryProbe, threshold, ite_true, readDepth_eq p upperDepth.1 upperDepth.2]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨upper, List.mem_filter.mpr ⟨hu, by simp only [hsuSide, beq_self_eq_true]⟩, rfl⟩)
  · have lowerPage := readDepth_add_lt_D p lower.level
    have hH : p.H = 2 * p.D := rfl
    simp only [ordinaryProbe, threshold, ite_false]
    refine ⟨fun hrow => ?_, fun h => h.elim⟩
    obtain ⟨e, he, row⟩ := List.mem_map.mp (List.mem_toFinset.mp hrow)
    have levels := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
    have above := readDepth_add_lt_D p e.level
    rw [readDepth_eq p levels.1 levels.2] at above
    omega

/-- The actual observed ordinary probe inventory is the genuine upper-threshold bit. -/
private theorem canonical_ordinary_probe_card {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : OrdinaryAxisPlacement} (word : OrdinaryAxisReadout p upper lower t a) :
    (probeColumnStock l p target (holes t) upper.port).card = if a.parameter ≤ 1 then 1 else 0 := by
  have stock := canonical_ordinary_main_probe_stock l p hl hM haxes initial target
    hu hlow hsuSide hslSide hport hr accepted word
  have split : probeColumnStock l p target (holes t) upper.port =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (holes t) 13).filter (fun q => q.1.val = p.x upper.port)).filter
          (fun q => q.2.val ∈ probeRows l p) := by
    ext q
    simp only [probeColumnStock, Finset.mem_filter]
    tauto
  rw [split, stock]
  have row := ordinaryProbe_mem_probeRows_iff l p hl hM haxes (lower := lower) hu hsuSide a.parameter
  by_cases threshold : a.parameter ≤ 1
  · simp only [Finset.filter_singleton, ite_eq_left (row.mpr threshold), ite_eq_left threshold, Finset.card_singleton]
  · simp only [Finset.filter_singleton, ite_eq_right (fun h => threshold (row.mp h)), ite_eq_right threshold, Finset.card_empty]

/-- A genuine accepted ordinary terminal word decodes precisely its original target axis bit. -/
theorem canonical_ordinary_target_threshold (hgate : l.gateCenterCoordinates ≠ []) {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : OrdinaryAxisPlacement} (word : OrdinaryAxisReadout p upper lower t a) :
    target.getD upper.port false = true ↔ a.parameter ≤ 1 := by
  have stock := canonical_ordinary_main_probe_stock l p hl hM haxes initial target
    hu hlow hsuSide hslSide hport hr accepted word
  have remaining := congrArg Finset.card stock
  simp only [Finset.card_singleton] at remaining
  have main := canonical_ordinaryAxis_probe_input_card l p hl hM haxes initial target hu hlow hsuSide hslSide hport hr accepted
  have balance := canonical_ordinaryAxis_surplus_balance l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hr .refl accepted
  have inventory : (holes t ∩ ordinaryAxis p upper.port).card = 5 := by
    omega
  have zero : Inventory.count (ordinaryAxis p upper.port) t - Inventory.count (ordinaryAxis p upper.port) (I).initial = 0 := by
    omega
  have observed := canonical_ordinary_probe_card l p hl hM haxes initial target
    hu hlow hsuSide hslSide hport hr accepted word
  have signed := canonical_ordinary_probe_balance l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hr accepted
  rw [zero, Nat.zero_add, observed] at signed
  by_cases threshold : a.parameter ≤ 1 <;> cases bit : target.getD upper.port false <;>
    simp only [threshold, ite_true, ite_false, bit, Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, iff_false, iff_true] at signed ⊢ <;> omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
