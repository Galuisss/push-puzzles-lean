/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeBitmap
import all Push.AcceptanceSoundnessFWalkPayment
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortEndpointFStock
import all PushS.PortEndpointTail

/-! Actual first trims pay their complete fixed f corridors, as literal destructive-scan accounts. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem fwalk_paid_of_trim_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
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
    endpointFWalk p e \ Boundary.frame =
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3) \
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) ((if e.side = .upper then 4 else 3) + 1)).filter
          fun q => q.1.val = EndpointStreet.f.column p e := by
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
  have he : A.filter (fun q => dir.lane q = EndpointStreet.f.column p e) \
      F.filter (fun q => dir.lane q = EndpointStreet.f.column p e) =
      (A \ F).filter (fun q => q.1.val = EndpointStreet.f.column p e) := by
    ext q
    cases hs : e.side <;> simp only [dir, hs, ite_true, reduceCtorEq, ite_false, Direction.lane,
      Finset.mem_filter, Finset.mem_sdiff]
    all_goals
      constructor
      · rintro ⟨⟨ha, hx⟩, hf⟩
        exact ⟨⟨ha, fun h => hf ⟨h, hx⟩⟩, hx⟩
      · rintro ⟨⟨ha, hf⟩, hx⟩
        exact ⟨⟨ha, hx⟩, fun h => hf h.1⟩
  exact hpaid.trans he

/-- Every ordinary f corridor is exactly the same-column payment of its actual first trim. -/
theorem canonical_fwalk_trim_paid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (hgate : l.gateCenterCoordinates ≠ []) (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    endpointFWalk p e \ Boundary.frame =
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3) \
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) ((if e.side = .upper then 4 else 3) + 1)).filter
          fun q => q.1.val = EndpointStreet.f.column p e := by
  apply fwalk_paid_of_trim_stock l p hl hM haxes initial target hr ha e he
  by_cases hlast : e.level = p.levels
  · exact fun q hq hn hx => canonical_last_f_trim_payment_in_walk l p hl hM haxes initial target hr ha e he hlast hq hn hx
  · have heM : e.level < p.levels := by have := (l.endpoints_level_bounds p hl hM he).2; omega
    have htail := canonical_endpoint_tail_full_of_deeper l p hl hM haxes initial target hgate e he heM .f hr .refl ha
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level hs ht ha)
    exact fun q hq hn hx => canonical_f_trim_payment_in_walk_of_tail l p hl hM haxes initial target hr ha e he heM htail hq hn hx

end PushPuzzle.Push.AcceptanceSoundness
