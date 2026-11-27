/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireInventory
public import Push.AcceptanceProgramWireRowStockRTrim
public import Push.AcceptanceProgramTrimStock
import all Push.AcceptanceProgramTrimStock
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortEndpointReaderWalk
import all PushFS.Grid

/-! The actual r-trim first pays its complete empty outer corridor before any working-row collateral. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The non-frame portion of an ordinary r corridor. -/
def rTrimCorridor (p : Scales.Parameters) (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1.val = EndpointStreet.r.column p e ∧
    1 ≤ pageDepth p e.side q ∧ pageDepth p e.side q < p.Y e.level

/-- A same-page outer hole on an auxiliary column reaches that page's first trim unchanged. -/
private theorem canonical_trim_outer_input (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : Side) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t)
    (hf : q ∉ Boundary.frame) (hx : q.1.val ∈ auxiliaries l p)
    (hy : pageDepth p side q < p.D - 2) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if side = .upper then 4 else 3) := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
  have hq3 : q ∈ roundResidual stages T (PushS.holes t) 3 := by
    unfold roundResidual
    rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
      program_sideClear_remaining l p hl hM haxes initial target hr
        (canonical_initial_holes l p hl hM haxes initial target) ha]
    exact Finset.mem_sdiff.mpr ⟨hq, hf⟩
  cases side with
  | lower => exact hq3
  | upper =>
    have hD := p.outer_distance
    have hH : p.H = 2 * p.D := rfl
    let down : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D + 2, by omega⟩)
    have hd := auxiliary_flank_marker l p (q := down) hx (Or.inr rfl)
    have hd10 := flank_markers_residual l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hd) (Or.inr rfl)
    have i3 : stages[3]? = some (trimRound l p .lower) := by
      simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem?_cons_zero]
    exact roundResidual_marker_keeps stages T (PushS.holes t) 3 10 hc i3 hd10 (by omega) hq3 rfl (by
      change p.H - (p.D + 2) ≤ p.H - q.2.val
      change q.2.val < p.D - 2 at hy
      omega)

/-- The non-frame outer r corridor contains exactly Y−1 physical cells. -/
private theorem rTrimCorridor_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : (rTrimCorridor p e).card = p.Y e.level - 1 := by
  obtain ⟨a, hac, hcol, hlevel, _⟩ := endpoint_trim_column l p e he .r
  obtain ⟨hj, hjm, _, hxW⟩ := pageColumn_bounds l p hl hM haxes e.side hac
  have hY := readDepth_add_lt_H p a.level
  rw [readDepth_eq p hj hjm] at hY
  have hc := corridor_card p e.side a hxW (by omega)
  simpa only [rTrimCorridor, hcol, hlevel] using hc

/-- A complete physical outer prefix is fully paid when the emitted same-line quota covers its cardinality. -/
private theorem round_prefix_stock_paid {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T E F B : Finset (Cell w h)) (x rank : ℕ)
    (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    (hBE : B ⊆ E) (hB : ∀ q ∈ B, side.lane q = x ∧ prefixRank side q < rank)
    (hwindow : ∀ q ∈ E, side.lane q = x → prefixRank side q < rank → q ∈ B)
    (href : ((emit [.read side requests] T).remaining.filter fun q => side.lane q = x).card +
      B.card ≤ (T.filter fun q => side.lane q = x).card) : B ⊆ E \ F := by
  intro b hb
  refine Finset.mem_sdiff.mpr ⟨hBE hb, ?_⟩
  intro hbF
  have hpaid : E.filter (fun q => side.lane q = x) \ F.filter (fun q => side.lane q = x) ⊆ B := by
    intro q hq
    obtain ⟨hqE, hqF⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqE, hqx⟩ := Finset.mem_filter.mp hqE
    have hnot : q ∉ F := fun h => hqF (Finset.mem_filter.mpr ⟨h, hqx⟩)
    have hlt := round_deleted_before_retained side requests T he hbF hqE hnot ((hB b hb).1.trans hqx.symm)
    exact hwindow q hqE hqx (hlt.trans (hB b hb).2)
  have heq := round_lane_saturation side requests T E F B x he hpaid href
  have hp := (congrArg (fun S : Finset (Cell w h) => b ∈ S) heq).mp hb
  exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hbF, (hB b hb).1⟩)

/-- Same-column actual trim payments after reserving its entire outer r corridor. -/
def rTrimCollateral (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  let stages := schedule l p (targetHoles l p target \ Boundary.frame).card
  let i := if e.side = .upper then 4 else 3
  ((roundResidual stages (targetHoles l p target) E i \
    roundResidual stages (targetHoles l p target) E (i + 1)).filter
      fun q => q.1.val = EndpointStreet.r.column p e) \ rTrimCorridor p e

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- All Y−1 outer r-corridor holes are physically present when their actual page trim begins. -/
private theorem canonical_r_corridor_before_trim (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    rTrimCorridor p e ⊆ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3) := by
  intro q hq
  obtain ⟨_, hx, hy0, hy⟩ := Finset.mem_filter.mp hq
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hY := readDepth_add_lt_D p e.level
  have hYH := readDepth_add_lt_H p e.level
  rw [readDepth_eq p hj hjm] at hY hYH
  obtain ⟨a, hac, hcol, hlevel, _⟩ := endpoint_trim_column l p e he .r
  have haux : q.1.val ∈ auxiliaries l p :=
    (hx.trans hcol.symm) ▸ l.acceptancePageColumn_aux p hl hM haxes e.side hac
  have hwalk : q ∈ l.endpointReaderWalk p e := by
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply (mem_endpointRWalk_iff p e q).mpr
    refine ⟨hx, ?_⟩
    rw [readDepth_eq p hj hjm]
    cases hs : e.side <;> simp only [pageDepth, hs, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega
  have hh := canonical_ordinaryReaders_empty l p hl hM haxes initial target hgate e he hr .refl ha hwalk
  apply canonical_trim_outer_input l p hl hM haxes initial target hr ha e.side hh _ haux (by omega)
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  have hcols := pageColumn_bounds l p hl hM haxes e.side hac
  rw [hcol, ← hx] at hcols
  have hrow := q.2.isLt
  cases hs : e.side <;> cases d <;>
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and,
      pageDepth, hs, ite_true, reduceCtorEq, ite_false] at hd hy0 hy <;> omega

/-- The real public trim pays every one of its Y−1 outer r-corridor holes. -/
theorem canonical_r_corridor_paid (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    rTrimCorridor p e ⊆
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (if e.side = .upper then 4 else 3) \
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) ((if e.side = .upper then 4 else 3) + 1) := by
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
  obtain ⟨a, hac, hcol, hlevel, hpublic⟩ := endpoint_trim_column l p e he .r
  apply round_prefix_stock_paid dir requests R A F (rTrimCorridor p e)
    (EndpointStreet.r.column p e) (p.Y e.level) hread
    (canonical_r_corridor_before_trim l p hl hM haxes initial target hgate e he hr ha)
  · intro q hq
    obtain ⟨_, hx, _, hy⟩ := Finset.mem_filter.mp hq
    cases hs : e.side <;> simpa only [dir, pageDepth, prefixRank, Direction.lane, hs,
      ite_true, reduceCtorEq, ite_false, Nat.add_sub_cancel] using And.intro hx hy
  · intro q hq hx hy
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha i
      (by cases hs : e.side <;> simp [i, hs]) hq
    have hx' : q.1.val = EndpointStreet.r.column p e := by
      cases hs : e.side <;> simpa only [dir, Direction.lane, hs, ite_true, reduceCtorEq, ite_false] using hx
    have hy' : pageDepth p e.side q < p.Y e.level := by
      cases hs : e.side <;> simpa only [dir, pageDepth, prefixRank, hs, ite_true, reduceCtorEq,
        ite_false, Nat.add_sub_cancel] using hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hx', ?_, hy'⟩
    by_contra hn
    have hzero : pageDepth p e.side q = 0 := by omega
    apply hf
    apply (Boundary.mem_frame q).mpr
    have hybound := q.2.isLt
    cases hs : e.side
    · exact ⟨.north, by simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and,
        pageDepth, hs, ite_true] using hzero⟩
    · refine ⟨.south, ?_⟩
      simp only [pageDepth, hs, reduceCtorEq, ite_false] at hzero
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  · have href := trim_target_column_loss l p hl hM haxes target e.side hac hpublic
    rw [rTrimCorridor_card l p hl hM haxes e he]
    dsimp only [R]
    rw [htake]
    rw [hcol, hlevel] at href
    cases hs : e.side <;> simpa only [dir, requests, trimRound, Direction.lane, hs,
      ite_true, reduceCtorEq, ite_false, T] using href

/-- The real r-trim collateral pays exactly its canonical same-column quota beyond the reserved Y−1 corridor holes. -/
private theorem canonical_r_trim_collateral_balance (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    let T := (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining
    let U := (emit [trimRound l p e.side] T).remaining
    (rTrimCollateral l p target (PushS.holes t) e).card + (p.Y e.level - 1) +
      (U.filter fun q => q.1.val = EndpointStreet.r.column p e).card =
      (T.filter fun q => q.1.val = EndpointStreet.r.column p e).card := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if e.side = .upper then 4 else 3
  let dir : Direction := if e.side = .upper then .north else .south
  let requests := ((AcceptanceProgram.pageColumns l p e.side).filter fun a => !a.privateColumn).map fun a =>
    (a.column, trimDepth p a.level)
  let R := (emit (stages.take i) T).remaining
  let A := roundResidual stages T (PushS.holes t) i
  let F := roundResidual stages T (PushS.holes t) (i + 1)
  let D := (A \ F).filter fun q => q.1.val = EndpointStreet.r.column p e
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
  have hloss : (A.filter fun q => q.1.val = EndpointStreet.r.column p e).card +
      ((emit [.read dir requests] R).remaining.filter fun q => q.1.val = EndpointStreet.r.column p e).card =
      (F.filter fun q => q.1.val = EndpointStreet.r.column p e).card +
        (R.filter fun q => q.1.val = EndpointStreet.r.column p e).card := by
    have h := round_reference_lane_loss dir requests R A F (EndpointStreet.r.column p e) hread
    cases hs : e.side <;> simpa only [dir, Direction.lane, hs, ite_true, reduceCtorEq, ite_false] using h
  have hsub : F.filter (fun q => q.1.val = EndpointStreet.r.column p e) ⊆
      A.filter (fun q => q.1.val = EndpointStreet.r.column p e) :=
    Finset.filter_subset_filter _ (scan_subset hread)
  have hD : D = A.filter (fun q => q.1.val = EndpointStreet.r.column p e) \
      F.filter (fun q => q.1.val = EndpointStreet.r.column p e) := by
    ext q
    simp only [D, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨ha, hf⟩, hx⟩
      exact ⟨⟨ha, hx⟩, fun h => hf h.1⟩
    · rintro ⟨⟨ha, hx⟩, hf⟩
      exact ⟨⟨ha, fun h => hf ⟨h, hx⟩⟩, hx⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [← hD] at hcard
  have hB : rTrimCorridor p e ⊆ D := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨canonical_r_corridor_paid l p hl hM haxes initial target hgate e he hr ha hq,
      (Finset.mem_filter.mp hq).2.1⟩
  have hcoll := Finset.card_sdiff_add_card_eq_card hB
  rw [rTrimCorridor_card l p hl hM haxes e he] at hcoll
  have htotal : (D \ rTrimCorridor p e).card + (p.Y e.level - 1) +
      ((emit [.read dir requests] R).remaining.filter fun q => q.1.val = EndpointStreet.r.column p e).card =
      (R.filter fun q => q.1.val = EndpointStreet.r.column p e).card := by omega
  change (D \ rTrimCorridor p e).card + (p.Y e.level - 1) + _ = _
  dsimp only [R] at htotal
  rw [htake] at htotal
  cases hs : e.side <;> simpa only [dir, requests, trimRound, hs, ite_true, reduceCtorEq, ite_false, T] using htotal

/-- The actual r-trim's collateral has exactly its emitted canonical one-cell work-slot quota. -/
theorem canonical_r_trim_collateral_card (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (rTrimCollateral l p target (PushS.holes t) e).card = endpointWorkDelta l p target e := by
  have hactual := canonical_r_trim_collateral_balance l p hl hM haxes initial target hgate e he hr ha
  have htarget := endpoint_r_trim_card l p hl hM haxes target e he
  dsimp only at hactual htarget
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
