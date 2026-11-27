/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasAgreement

/-! Every parked register assignment pays the same complete seven-round program. -/

public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction)
open Push.AcceptanceProgram

variable {w h : ℕ}

private theorem quota_lanes (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) :
    ((emitReads side requests E).quotas.map Prod.fst) = requests.map Prod.fst := by
  induction requests generalizing E with
  | nil => rfl
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    simpa only [emitReads, List.map_cons] using congrArg (List.cons lane) (ih _)

private theorem quota_cap (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) :
    ∀ a ∈ (emitReads side requests E).quotas,
      a.2 ≤ (E.filter fun p => side.lane p = a.1).card := by
  induction requests generalizing E with
  | nil => simp [emitReads]
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    intro a ha
    simp only [emitReads, List.mem_cons] at ha
    rcases ha with rfl | ha
    · apply Finset.card_le_card
      intro p hp
      obtain ⟨hp, hl⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp, ((mem_line_prefix side lane span p).mp hl).1⟩
    · apply (ih _ a ha).trans
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hp, hl⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hl⟩

private theorem emit_rounds_append (left right : List Template) (E : Finset (Cell w h)) :
    (Push.AcceptanceProgram.emit (left ++ right) E).rounds =
      (Push.AcceptanceProgram.emit left E).rounds ++
        (Push.AcceptanceProgram.emit right (Push.AcceptanceProgram.emit left E).remaining).rounds := by
  induction left generalizing E with
  | nil => rfl
  | cons stage stages ih =>
    cases stage <;> simp only [List.cons_append, emit, ih]

namespace Layout

theorem quotaProgram_decomposition (L : Layout) :
    L.quotaProgram.rounds =
      (Push.AcceptanceProgram.emit (L.quotaTemplates.take 6) L.referenceHoles).rounds ++
        [Round.read .north (emitReads .north L.finalRequests
          (Push.AcceptanceProgram.emit (L.quotaTemplates.take 6) L.referenceHoles).remaining).quotas] := by
  have hs : L.quotaTemplates = L.quotaTemplates.take 6 ++ [.read .north L.finalRequests] := rfl
  change (Push.AcceptanceProgram.emit L.quotaTemplates L.referenceHoles).rounds = _
  conv_lhs => rw [hs, emit_rounds_append]
  rfl

end Layout

namespace Source.Stock

variable {I : Instance}

/-- The original complete program accepts every parked physical register stock. -/
theorem quotaProgram_accepts (S : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop) :
    Push.Scan.eval (instructions (layout false I).quotaProgram.rounds) (S.boxes false)ᶜ = some ∅ := by
  let L := layout false I
  let reference := terminal false I
  let stagesBefore := L.quotaTemplates.take 6
  let start := (S.boxes false)ᶜ
  let remaining := (Push.AcceptanceProgram.emit stagesBefore start).remaining
  let refRemaining := (Push.AcceptanceProgram.emit stagesBefore L.referenceHoles).remaining
  let quotas := (emitReads .north L.finalRequests refRemaining).quotas
  have href : (reference.boxes false)ᶜ = L.referenceHoles :=
    congrArg (fun boxes : Finset (Cell L.width L.height) => boxesᶜ) (terminal_boxes false I)
  have hpref : (Push.AcceptanceProgram.emit stagesBefore start).rounds =
      (Push.AcceptanceProgram.emit stagesBefore L.referenceHoles).rounds := by
    rw [← href]
    exact S.quotaPrefix_rounds_equal reference hs rfl
  have hcounts (x : ℕ) : (remaining.filter fun p => p.1.val = x).card =
      (refRemaining.filter fun p => p.1.val = x).card := by
    dsimp [remaining, refRemaining]
    rw [emit_remaining, emit_remaining, ← href]
    exact S.remaining_columns_equal reference hs rfl x
  have hlanes : (quotas.map Prod.fst).Nodup := by
    rw [quota_lanes]
    simpa [Layout.finalRequests, List.map_map, Function.comp_def] using
      (List.nodup_range (n := L.width))
  have hcap : ∀ a ∈ quotas, a.2 ≤ (remaining.filter fun p => Direction.north.lane p = a.1).card := by
    intro a ha
    change a.2 ≤ (remaining.filter fun p => p.1.val = a.1).card
    rw [hcounts]
    exact quota_cap .north L.finalRequests refRemaining a ha
  obtain ⟨last, hlast⟩ := Push.Scan.lines_accepts .north quotas remaining hlanes hcap
  have hprogram : instructions (w := L.width) (h := L.height) L.quotaProgram.rounds =
      instructions (Push.AcceptanceProgram.emit stagesBefore L.referenceHoles).rounds ++
        Push.Scan.lines .north quotas := by
    rw [L.quotaProgram_decomposition, instructions, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Round.instructions,
      Push.Scan.lines, instructions]
    rfl
  have hprefix : Push.Scan.eval (instructions (Push.AcceptanceProgram.emit stagesBefore L.referenceHoles).rounds)
      start = some remaining := by
    rw [← hpref]
    exact emit_eval stagesBefore start
  have hrun : Push.Scan.eval (instructions L.quotaProgram.rounds) start = some last := by
    rw [hprogram, Push.Scan.eval_append, hprefix, Option.bind_some]
    exact hlast
  have hboxes : (S.boxes false).card = (reference.boxes false).card := by
    rw [S.boxes_parked hs, reference.boxes_parked rfl,
      Finset.card_union_of_disjoint S.registerCells_disjoint_shared,
      Finset.card_union_of_disjoint reference.registerCells_disjoint_shared,
      S.registerCells_card, reference.registerCells_card]
  have hcard : start.card = L.referenceHoles.card := by
    rw [← href]
    change ((S.boxes false)ᶜ).card = ((reference.boxes false)ᶜ).card
    rw [Finset.card_compl, Finset.card_compl, hboxes]
  have hquota : Push.Scan.quota (instructions (w := L.width) (h := L.height) L.quotaProgram.rounds) = start.card :=
    L.quotaProgram_quota.trans hcard.symm
  have hempty := (Push.Scan.full_quota hrun hquota).1
  simpa only [hempty] using hrun

/-- Every quota boundary is blocked in the same parked source stock. -/
theorem quota_cut_blocked (S : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop)
    (side : Direction) (requests : List (ℕ × ℕ))
    (hstage : Template.read side requests ∈ (layout false I).quotaTemplates)
    {request : ℕ × ℕ} (hr : request ∈ requests)
    (p : Cell (layout false I).width (layout false I).height)
    (hl : side.lane p = request.1) (hp : prefixRank side p = request.2) :
    p ∉ (S.boxes false)ᶜ := by
  have hraw := (layout false I).quota_boundary_shared side requests hstage hr p hl hp
  have hbox : p ∈ S.boxes false := by
    rw [S.boxes_parked hs]
    exact Finset.mem_union_left _ (((layout false I).mem_raster _ _).mpr hraw)
  exact fun h => Finset.mem_compl.mp h hbox

end Source.Stock
end PushPuzzle.PushPush.Doors
