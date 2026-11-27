/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireWorkPrefix
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortWireRail
import all PushS.PortWireIndexing

/-! Every ordinary-rail hole consumed before R23 is charged to one of its two real r-trim collateral sets. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- A certified central flank prevents a public trim from reaching the opposite page. -/
theorem canonical_trim_other_half_keeps (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : if side = .upper then p.D + 2 < q.2.val else q.2.val < p.D - 2)
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if side = .upper then 4 else 3)) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) ((if side = .upper then 4 else 3) + 1) := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if side = .upper then 4 else 3
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[i]? = some (trimRound l p side) := by
    cases side <;> simp only [i, stages, schedule, preparation, frameSchedule,
      ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  by_cases hx : q.1.val ∈ auxiliaries l p
  · have hD := p.outer_distance
    have hH : p.H = 2 * p.D := rfl
    let flank : Cell (p.W + 1) (p.H + 1) :=
      (q.1, ⟨if side = .upper then p.D - 2 else p.D + 2, by split <;> omega⟩)
    have hrow : flank.2.val = p.D - 2 ∨ flank.2.val = p.D + 2 := by cases side <;> simp [flank]
    have hf := auxiliary_flank_marker l p (q := flank) hx hrow
    have hf10 := flank_markers_residual l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hf) hrow
    cases side
    · apply roundResidual_marker_keeps stages T E 4 10 hc hi hf10 (by omega) hq rfl
      change p.D - 2 ≤ q.2.val
      simp only [ite_true] at hy
      omega
    · apply roundResidual_marker_keeps stages T E 3 10 hc hi hf10 (by omega) hq rfl
      change p.H - (p.D + 2) ≤ p.H - q.2.val
      simp only [reduceCtorEq, ite_false] at hy
      omega
  · apply roundResidual_unread_keeps stages T E i hc hi hq
    intro ht
    obtain ⟨request, hrequest, hqx⟩ := ht
    obtain ⟨a, hac, heq⟩ := List.mem_map.mp hrequest
    have hcol : q.1.val = a.column := by
      cases side <;> simpa only [← heq, Direction.lane, ite_true, reduceCtorEq, ite_false] using hqx
    exact hx (hcol ▸ l.acceptancePageColumn_aux p hl hM haxes side (List.mem_filter.mp hac).1)

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every own-page WIRE trim payment belongs to one of the two reserved-corridor collateral accounts. -/
private theorem canonical_wire_trim_collateral {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrail : q ∈ wireOpenRail p g)
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if g.side = .upper then 4 else 3))
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) ((if g.side = .upper then 4 else 3) + 1)) :
    q ∈ rTrimCollateral l p target (PushS.holes t) (wireWorkLeft g) ∪
      rTrimCollateral l p target (PushS.holes t) (wireWorkRight g) := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if g.side = .upper then 4 else 3
  let dir : Direction := if g.side = .upper then .north else .south
  let requests := ((AcceptanceProgram.pageColumns l p g.side).filter fun a => !a.privateColumn).map fun a =>
    (a.column, trimDepth p a.level)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[i]? = some (.read dir requests) := by
    cases hs : g.side <;> simp only [i, stages, schedule, preparation, frameSchedule, trimRound, hs,
      dir, requests, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hqE := scan_subset (roundResidual_eval stages T (PushS.holes t) i hc) hq
  obtain ⟨request, hrequest, hqx⟩ := read_block_removed_lane dir requests _ _ _
    (roundResidual_step stages T (PushS.holes t) i hc hi).1 hq hqout
  obtain ⟨a, hac, heq⟩ := List.mem_map.mp hrequest
  have hcol : q.1.val = a.column := by
    cases hs : g.side <;> simpa only [← heq, dir, Direction.lane, hs, ite_true, reduceCtorEq, ite_false] using hqx
  have hpcol : q.1 ∈ l.pageColumnSet p g.side := by
    change q.1.val ∈ l.pageColumnCoordinates p g.side
    exact hcol ▸ acceptance_column_page l p g.side (List.mem_filter.mp hac).1
  have hrec := canonical_wire_receiving_of_page_column l p hl hM haxes initial target hgate
    hg hw hr ha hqE hrail hpcol
  have hrow := (Finset.mem_filter.mp hrail).2.1
  obtain ⟨hj, hjM⟩ := placement_level_bounds l hl hg
  have hjm := hjM.trans hM
  have hY := readDepth_add_lt_H p g.level
  have hdepth : pageDepth p g.side q = p.Y g.level := by
    rw [readDepth_eq p hj hjm] at hrow hY
    have hqH := q.2.isLt
    cases hs : g.side <;> simp only [pageDepth, hs, ite_true, reduceCtorEq, ite_false] at hrow ⊢ <;> omega
  rcases hrec with hleft | hright
  · apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hq, hqout⟩, ?_⟩, ?_⟩
    · simpa only [wireWorkLeft, EndpointStreet.column_r, ite_true] using hleft
    · intro hb
      have hlt := (Finset.mem_filter.mp hb).2.2.2
      change pageDepth p g.side q < p.Y g.level at hlt
      omega
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hq, hqout⟩, ?_⟩, ?_⟩
    · simpa only [wireWorkRight, EndpointStreet.column_r, Bool.false_eq_true, ite_false] using hright
    · intro hb
      have hlt := (Finset.mem_filter.mp hb).2.2.2
      change pageDepth p g.side q < p.Y g.level at hlt
      omega

/-- Every actual ordinary-rail hole lost before the final work-row read was paid by its own r trim. -/
theorem canonical_wire_prework_paid {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (PushS.holes t ∩ wireOpenRail p g) \
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 23 ⊆
      rTrimCollateral l p target (PushS.holes t) (wireWorkLeft g) ∪
        rTrimCollateral l p target (PushS.holes t) (wireWorkRight g) := by
  intro q hq
  obtain ⟨hq, hout⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨hE, hrail⟩ := Finset.mem_inter.mp hq
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hrow := (Finset.mem_filter.mp hrail).2
  obtain ⟨hj, hjM⟩ := placement_level_bounds l hl hg
  have hjm := hjM.trans hM
  have hY := readDepth_ge p hj hjm
  have hD := readDepth_add_lt_D p g.level
  have hH : p.H = 2 * p.D := rfl
  have hports := wire_ports l hl hg hw
  have hx0 := readLength_add_lt_x p g.left 0
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le haxes) 0
  have hf : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases hs : g.side <;> cases d <;>
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hs,
        ite_true, reduceCtorEq, ite_false] at hd hrow <;> omega
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
  have hq3 : q ∈ roundResidual stages T E 3 := by
    unfold roundResidual
    rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
      program_sideClear_remaining l p hl hM haxes initial target hr
        (canonical_initial_holes l p hl hM haxes initial target) ha]
    exact Finset.mem_sdiff.mpr ⟨hE, hf⟩
  have hnot5 : q ∉ roundResidual stages T E 5 := fun h => hout
    (canonical_wire_five_to_work l p hl hM haxes initial target hgate hg hw hr ha hrail h)
  cases hs : g.side
  · have hq4 := canonical_trim_other_half_keeps l p hl hM haxes initial target hr ha .lower
      (by simp only [reduceCtorEq, ite_false]; simp only [hs, ite_true] at hrow; omega) hq3
    exact canonical_wire_trim_collateral l p hl hM haxes initial target hgate hg hw hr ha hrail
      (by simpa only [hs, ite_true, reduceCtorEq, ite_false, Nat.reduceAdd] using hq4) (by simpa only [hs, ite_true] using hnot5)
  · have hnot4 : q ∉ roundResidual stages T E 4 := by
      intro hq4
      exact hnot5 (canonical_trim_other_half_keeps l p hl hM haxes initial target hr ha .upper
        (by simp only [ite_true]; simp only [hs, reduceCtorEq, ite_false] at hrow; omega) hq4)
    exact canonical_wire_trim_collateral l p hl hM haxes initial target hgate hg hw hr ha hrail
      (by simpa only [hs, reduceCtorEq, ite_false] using hq3)
      (by simpa only [hs, reduceCtorEq, ite_false] using hnot4)

/-- At most the two emitted work-slot deltas can be paid from an actual rail before R23. -/
private theorem canonical_wire_prework_loss_bound {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((PushS.holes t ∩ wireOpenRail p g) \
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 23).card ≤
      endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g) := by
  have h := Finset.card_le_card (canonical_wire_prework_paid l p hl hM haxes initial target hgate hg hw hr ha)
  have hu := Finset.card_union_le
    (rTrimCollateral l p target (PushS.holes t) (wireWorkLeft g))
    (rTrimCollateral l p target (PushS.holes t) (wireWorkRight g))
  obtain ⟨hleft, hright⟩ := wire_endpoints l hg hw
  have hleft' : wireWorkLeft g ∈ l.endpoints := by simpa only [wireWorkLeft, wireLeft] using hleft
  have hright' : wireWorkRight g ∈ l.endpoints := by
    simpa only [wireWorkRight, wireRight, hw, Option.isSome_none, ite_false, Nat.add_zero] using hright
  rw [canonical_r_trim_collateral_card l p hl hM haxes initial target hgate _ hleft' hr ha,
    canonical_r_trim_collateral_card l p hl hM haxes initial target hgate _ hright' hr ha] at hu
  exact h.trans hu

/-- The actual R23 rail stock plus its two allowed prior deltas covers every terminal rail hole. -/
theorem canonical_wire_work_stock_bound {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (PushS.holes t ∩ wireOpenRail p g).card ≤
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 23 ∩ wireOpenRail p g).card +
      endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g) := by
  let E := PushS.holes t
  let A := roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) E 23
  let R := wireOpenRail p g
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hsub : A ⊆ E := scan_subset (roundResidual_eval _ _ _ _ hc)
  have hpart := Finset.card_sdiff_add_card_inter (E ∩ R) A
  have he : (E ∩ R) ∩ A = A ∩ R := by
    ext q
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  rw [he] at hpart
  have hle := canonical_wire_prework_loss_bound l p hl hM haxes initial target hgate hg hw hr ha
  change ((E ∩ R) \ A).card ≤ _ at hle
  change (E ∩ R).card ≤ (A ∩ R).card + _ + _
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
