/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessTrimBarrier
public import Push.AcceptanceProgramFTrimStock
public import Push.AcceptanceSoundnessInterlevelPage
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortEndpointFStock
import all PushS.PortEndpointTail
import all PushS.PortCentralFreeze
import all PushFS.Grid

/-! Actual f-column trim payments saturate the complete original f corridor. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem fwalk_terminal_of_trim_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (e : Endpoint) (he : e ∈ l.endpoints)
    (hwindow : ∀ q : Cell (p.W + 1) (p.H + 1),
      q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3) →
      q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) ((if e.side = .upper then 4 else 3) + 1) →
      q.1.val = EndpointStreet.f.column p e → q ∈ endpointFWalk p e) :
    endpointFWalk p e ⊆ PushS.holes t := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if e.side = .upper then 4 else 3
  let dir : Direction := if e.side = .upper then .north else .south
  let requests := ((AcceptanceProgram.pageColumns l p e.side).filter fun a => !a.privateColumn).map fun a =>
    (a.column, trimDepth p a.level)
  let R := (emit (stages.take i) T).remaining
  let A := roundResidual stages T (PushS.holes t) i
  let F := roundResidual stages T (PushS.holes t) (i + 1)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[i]? = some (.read dir requests) := by
    cases hs : e.side <;> simp only [i, stages, schedule, preparation, frameSchedule, trimRound, hs,
      dir, requests, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have htake : stages.take i = trimBeforeSchedule l p target e.side := by
    cases hs : e.side <;> simp only [i, stages, schedule, preparation, frameSchedule, trimBeforeSchedule, hs,
      sideClearSchedule, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero, List.append_nil, T]
  have hread := (roundResidual_step stages T (PushS.holes t) i hc hi).1
  have hstock : A.filter (fun q => dir.lane q = EndpointStreet.f.column p e) \
      F.filter (fun q => dir.lane q = EndpointStreet.f.column p e) ⊆ endpointFWalk p e \ Boundary.frame := by
    intro q hq
    obtain ⟨hqA, hqF⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqA, hqx⟩ := Finset.mem_filter.mp hqA
    have hqF' : q ∉ F := fun h => hqF (Finset.mem_filter.mpr ⟨h, hqx⟩)
    have hx : q.1.val = EndpointStreet.f.column p e := by
      cases hs : e.side <;> simpa only [dir, hs, ite_true, reduceCtorEq, ite_false, Direction.lane] using hqx
    exact Finset.mem_sdiff.mpr ⟨hwindow q hqA hqF' hx,
      canonical_residual_not_frame l p hl hM haxes initial target hr ha i
        (by cases hs : e.side <;> simp [i, hs]) hqA⟩
  have href : ((emit [.read dir requests] R).remaining.filter fun q => dir.lane q = EndpointStreet.f.column p e).card +
      (endpointFWalk p e \ Boundary.frame).card ≤ (R.filter fun q => dir.lane q = EndpointStreet.f.column p e).card := by
    have hf := endpoint_f_trim_target_loss l p hl hM haxes target e he
    rw [endpoint_f_interior_card l p hl hM haxes e he]
    dsimp only [R]
    rw [htake]
    cases hs : e.side <;> simpa only [dir, requests, trimRound, Direction.lane, hs, ite_true, reduceCtorEq, ite_false, T] using hf
  have hpaid := round_lane_saturation dir requests R A F (endpointFWalk p e \ Boundary.frame)
    (EndpointStreet.f.column p e) hread hstock href
  intro q hq
  by_cases hframe : q ∈ Boundary.frame
  · exact program_accepts_frame l p target ha hframe
  · have hqpaid := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hpaid).mp
      (Finset.mem_sdiff.mpr ⟨hq, hframe⟩)
    exact scan_subset (roundResidual_eval stages T (PushS.holes t) i hc)
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hqpaid).1).1

/-- At a nondeepest level, a full frozen tail confines every actual f-trim payment to its original corridor. -/
theorem canonical_f_trim_payment_in_walk_of_tail (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    (htail : endpointTail p e .f ⊆ t.boxes) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3))
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) ((if e.side = .upper then 4 else 3) + 1))
    (hx : q.1.val = EndpointStreet.f.column p e) : q ∈ endpointFWalk p e := by
  obtain ⟨a, hac, hcol, hlevel, _⟩ := endpoint_trim_column l p e he .f
  have hd := canonical_trim_payment_depth l p hl hM haxes initial target hr ha e.side hac (hx.trans hcol.symm) hq hqout
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  rw [hlevel, trimDepth, ite_eq_left heM] at hd
  have hread : readDepth p e.level = p.Y e.level := readDepth_eq p hj hjm
  have hnext : readDepth p (e.level + 1) = p.Y (e.level + 1) := readDepth_eq p (by omega) (by omega)
  by_contra hnot
  have hdeep : readDepth p e.level + 2 < pageDepth p e.side q := by
    by_contra hn
    apply hnot
    apply (mem_endpointFWalk_iff p e q).mpr
    refine ⟨hx, ?_⟩
    have hb := q.2.isLt
    cases hs : e.side <;> simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at hn ⊢ <;> omega
  have htailq : q ∈ endpointTail p e .f := by
    apply (mem_endpointTail p e .f q).mpr
    refine ⟨hx, pageDepth p e.side q, by omega, ?_, ?_⟩
    · simpa only [endpointMarkerDepth, hread, hnext] using hd
    · have hb := q.2.isLt
      cases e.side <;> simp only [pageDepth, reduceCtorEq, ite_true, ite_false]
      omega
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  exact (PushS.mem_holes _).mp (scan_subset (roundResidual_eval _ _ _ _ hc) hq) (htail htailq)

/-- At the deepest level, the actual full central auxiliary strip bounds every f-trim payment. -/
theorem canonical_last_f_trim_payment_in_walk (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3))
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) ((if e.side = .upper then 4 else 3) + 1))
    (hx : q.1.val = EndpointStreet.f.column p e) : q ∈ endpointFWalk p e := by
  obtain ⟨a, hac, hcol, hlevel, _⟩ := endpoint_trim_column l p e he .f
  have hd := canonical_trim_payment_depth l p hl hM haxes initial target hr ha e.side hac (hx.trans hcol.symm) hq hqout
  have hread : readDepth p e.level = p.Y p.levels := by rw [heM, readDepth_eq p p.levels_pos le_rfl]
  rw [hlevel, heM, trimDepth, ite_eq_right (by omega)] at hd
  by_contra hnot
  have hdeep : readDepth p e.level + 2 < pageDepth p e.side q := by
    by_contra hn
    apply hnot
    apply (mem_endpointFWalk_iff p e q).mpr
    refine ⟨hx, ?_⟩
    have hb := q.2.isLt
    cases hs : e.side <;> simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at hn ⊢ <;> omega
  have haux : q.1.val ∈ auxiliaries l p :=
    (hx.trans hcol.symm) ▸ l.acceptancePageColumn_aux p hl hM haxes e.side hac
  have hstreet : q.1 ∈ l.streetColumnSet p := List.mem_toFinset.mp (Finset.mem_sdiff.mp haux).1
  have hmain : q.1 ∉ l.mainColumnSet p := by
    intro hm
    have hn := (Finset.mem_sdiff.mp haux).2
    rcases (l.mainColumnSet_iff p q.1).mp hm with h0 | hW | ⟨i, hi, hx⟩
    · exact hn (Finset.mem_union_right _ (by simp [h0]))
    · exact hn (Finset.mem_union_right _ (by simp [hW]))
    · exact hn (Finset.mem_union_left _ (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, hx.symm⟩)))
  have hcentral := canonical_trim_payment_not_central l p hl hM haxes initial target hr ha e.side hqout
  have hbox : q ∈ l.centralAuxiliaryBoxes p := by
    apply (mem_centralAuxiliaryBoxes l p q).mpr
    refine ⟨hstreet, hmain, ?_, ?_, hcentral⟩
    all_goals
      have hD := readDepth_add_lt_D p p.levels
      rw [readDepth_eq p p.levels_pos le_rfl] at hD
      have hH : p.H = 2 * p.D := rfl
      have hb := q.2.isLt
      rw [hread] at hdeep
      cases hs : e.side <;> simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at hd hdeep <;> omega
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  exact (PushS.mem_holes _).mp (scan_subset (roundResidual_eval _ _ _ _ hc) hq)
    (canonical_central_auxiliary_full l p hl hM haxes initial target hr .refl ha hbox)

/-- The deepest actual f trim forces its complete original corridor empty at the accepted endpoint. -/
theorem canonical_last_fwalk_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) : endpointFWalk p e ⊆ PushS.holes t := by
  apply fwalk_terminal_of_trim_stock l p hl hM haxes initial target hr ha e he
  exact fun q hq hqout hx => canonical_last_f_trim_payment_in_walk l p hl hM haxes initial target hr ha e he heM hq hqout hx

/-- Under the descending deeper-walk invariant, the actual current f trim saturates its complete corridor. -/
theorem canonical_level_fwalk_terminal_of_deeper (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (hgate : l.gateCenterCoordinates ≠ []) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) : endpointFWalk p e ⊆ PushS.holes t := by
  have htail := canonical_endpoint_tail_full_of_deeper l p hl hM haxes initial target hgate e he heM .f hr .refl ha hP
  apply fwalk_terminal_of_trim_stock l p hl hM haxes initial target hr ha e he
  exact fun q hq hqout hx => canonical_f_trim_payment_in_walk_of_tail l p hl hM haxes initial target hr ha
    e he heM htail hq hqout hx

end PushPuzzle.Push.AcceptanceSoundness
