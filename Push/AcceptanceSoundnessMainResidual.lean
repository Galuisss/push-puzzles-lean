/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessMainPayment
public import Push.AcceptanceMainCut
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceSoundnessSupportCutResidual
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The ordinary-axis main reads reserve four holes before the actual probe-row inventory. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- Immediately before the main reads, an actual principal column consists of its original non-frame axis holes. -/
theorem canonical_main_input_axis {port : ℕ} (hp : port < l.portCount)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 6).filter (fun q => q.1.val = p.x port) =
      PushS.holes t ∩ ordinaryAxis p port := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have haxis : p.x port ∈ axes l p := List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨port, List.mem_range.mpr hp, rfl⟩)
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha 6 (by omega) hq
    refine Finset.mem_inter.mpr ⟨scan_subset (roundResidual_eval stages T E 6 hc) hq, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hx, ?_, ?_⟩
    · by_contra hn
      exact hf ((Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    · by_contra hn
      have hb := q.2.isLt
      exact hf ((Boundary.mem_frame q).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
  · intro hq
    obtain ⟨hqE, hqaxis⟩ := Finset.mem_inter.mp hq
    obtain ⟨_, hx, hy0, hyH⟩ := Finset.mem_filter.mp hqaxis
    have hxin : 0 < q.1.val ∧ q.1.val < p.W := by
      have h0 := readLength_add_lt_x p port 0
      have hW := x_add_readLength_lt_W p (hp.trans_le haxes) 0
      omega
    have hf : q ∉ Boundary.frame := by
      intro hf
      obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
      cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega
    have htake3 : stages.take 3 = sideClearSchedule l p target := by
      simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T, List.cons_append,
        List.nil_append, List.take_succ_cons, List.take_zero]
    have hq3 : q ∈ roundResidual stages T E 3 := by
      unfold roundResidual
      rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
        program_sideClear_remaining l p hl hM haxes initial target hr
          (canonical_initial_holes l p hl hM haxes initial target) ha]
      exact Finset.mem_sdiff.mpr ⟨hqE, hf⟩
    have trim_unread (side : Side) : ¬ReadTouches (trimRound l p side) q := by
      intro ht
      obtain ⟨request, hrequest, hqx⟩ := ht
      obtain ⟨a, hac, heq⟩ := List.mem_map.mp hrequest
      have hcol : q.1.val = a.column := by
        cases side <;> simpa only [← heq, Direction.lane, ite_true, reduceCtorEq, ite_false] using hqx
      have haux := l.acceptancePageColumn_aux p hl hM haxes side (List.mem_filter.mp hac).1
      exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ ((hcol.symm.trans hx) ▸ haxis))
    have i3 : stages[3]? = some (trimRound l p .lower) := by
      simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem?_cons_zero]
    have hq4 := roundResidual_unread_keeps stages T E 3 hc i3 hq3 (trim_unread .lower)
    have i4 : stages[4]? = some (trimRound l p .upper) := by
      simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem?_cons_zero]
    have hq5 := roundResidual_unread_keeps stages T E 4 hc i4 hq4 (trim_unread .upper)
    have i5 : stages[5]? = some (.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)) := by
      simp only [stages, schedule, preparation, frameSchedule, firstRowKeep, List.cons_append,
        List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
    exact Finset.mem_filter.mpr ⟨(roundResidual_clear_keeps stages T E 5 hc i5 hq5).1, hx⟩

/-- After both actual main reads, the remaining principal-column stock is unchanged until the probe-row read. -/
theorem canonical_main_to_probe_stock {port : ℕ} (hp : port < l.portCount)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13).filter (fun q => q.1.val = p.x port) =
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 8).filter (fun q => q.1.val = p.x port) := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  apply Finset.Subset.antisymm (Finset.filter_subset_filter _ (roundResidual_antitone stages T E hc (by omega)))
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  have hqE := scan_subset (roundResidual_eval stages T E 8 hc) hq
  have haxis : q.1.val ∈ axes l p := List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨port, List.mem_range.mpr hp, hx.symm⟩)
  have hfar : q.2.val ∉ newMarkerRows p := by
    intro hy
    have hb := canonical_main_central_occupied l p hl hM haxes initial target hp hx
      (by simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hy; omega) hr .refl ha
    exact (PushS.mem_holes _).mp hqE hb
  have i8 : stages[8]? = some (.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, secondRowKeep, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq9 := (roundResidual_clear_keeps stages T E 8 hc i8 hq).1
  have i9 : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq10 := roundResidual_unread_keeps stages T E 9 hc i9 hq9 (by
    intro ht
    have haux := private_column_aux l p hl hM haxes (prefix_touches p .south _ _ ht)
    exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ haxis))
  have i10 : stages[10]? = some (readRows p .east {p.D - 2, p.D + 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq11 := roundResidual_unread_keeps stages T E 10 hc i10 hq10 (by
    intro ht
    have hh := row_touches p .east _ (Or.inr rfl) ht
    apply hfar
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    exact hh.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
  have i11 : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq12 := roundResidual_unread_keeps stages T E 11 hc i11 hq11
    (fun ht => guard_not_axis l p (prefix_touches p .north _ _ ht) haxis)
  have i12 : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq13 := roundResidual_unread_keeps stages T E 12 hc i12 hq12 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    exact hfar (by simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inl hh))))
  exact Finset.mem_filter.mpr ⟨hq13, hx⟩

/-- The remaining ordinary principal-column stock at the probe read is its terminal axis inventory minus four real payments. -/
theorem canonical_ordinaryAxis_probe_input_card {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hupper : upper.side = .upper) (hlower : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13).filter fun q => q.1.val = p.x upper.port).card + 4 =
      (PushS.holes t ∩ ordinaryAxis p upper.port).card := by
  have hupperPay := canonical_main_column_loss l p hl hM haxes initial target upper hu hr ha
  have hlowerPay := canonical_main_column_loss l p hl hM haxes initial target lower hlow hr ha
  simp only [hupper, hlower, hport, ite_true, reduceCtorEq, ite_false, Nat.reduceAdd] at hupperPay hlowerPay
  have hinput := congrArg Finset.card (canonical_main_input_axis l p hl hM haxes initial target
    (l.endpoints_port_lt hl hu) hr ha)
  have hretained := congrArg Finset.card (canonical_main_to_probe_stock l p hl hM haxes initial target
    (l.endpoints_port_lt hl hu) hr ha)
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
