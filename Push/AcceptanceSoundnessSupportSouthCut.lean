/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCutUnique
public import Push.AcceptanceSoundnessSupportFreeze
public import PushS.PortTwoPageStreets
public import Push.AcceptanceProgramCut
import all Push.AcceptanceSoundnessSupportCutPayment
import all Push.AcceptanceSoundnessSupportSouthPayment
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceProgramLayout

/-! In the genuine accepted page-check trace, southward reads pay exactly central-cut holes. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Every selected original auxiliary column has its actual central-cut marker. -/
theorem auxiliary_central_marker (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ auxiliaries l p) (hy : q.2.val = p.D) :
    q ∈ l.centralMarkers p := by
  apply l.central_cut_mem_markers p q hy
  · exact List.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1
  · intro hm
    have hn := (Finset.mem_sdiff.mp hx).2
    rcases (l.mainColumnSet_iff p q.1).mp hm with h0 | hW | ⟨i, hi, he⟩
    · exact hn (Finset.mem_union_right _ (by simp [h0]))
    · exact hn (Finset.mem_union_right _ (by simp [hW]))
    · apply hn
      apply Finset.mem_union_left
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, he.symm⟩)

/-- Two actual deletions in a selected one-hole reference front are the same physical hole. -/
private theorem south_round_front_at_most_one_deletion_unique {w h : ℕ} (cols : Finset ℕ)
    (span : ℕ → ℕ)
    (T E F : Finset (Cell w h)) {q r : Cell w h} (hx : q.1.val ∈ cols)
    (he : Scan.eval (instructions (emit [.read .south (prefixRequests cols span)] T).rounds) E = some F)
    (hbound : (T.filter fun a => a.1.val = q.1.val ∧ prefixRank .south a < span q.1.val).card ≤ 1)
    (hq : q ∈ E) (hqF : q ∉ F) (hr : r ∈ E) (hrF : r ∉ F) (hrx : r.1 = q.1) : r = q := by
  have hsub : F.filter (fun a => a.1.val = q.1.val) ⊆ E.filter (fun a => a.1.val = q.1.val) :=
    Finset.filter_subset_filter _ (scan_subset he)
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hloss := south_round_front_loss cols span T E F hx he
  have hdiff : (E.filter (fun a => a.1.val = q.1.val) \ F.filter (fun a => a.1.val = q.1.val)).card ≤ 1 := by omega
  apply Finset.card_le_one.mp hdiff
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hr, congrArg Fin.val hrx⟩,
      fun h => hrF (Finset.mem_filter.mp h).1⟩
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hq, rfl⟩,
      fun h => hqF (Finset.mem_filter.mp h).1⟩

/-- A real southward page-check payment deletes the central marker on its column. -/
theorem canonical_page_south_payment_cut (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (pay : RoundPayment (pageCheckStages l p) (pageCheckTarget l p target)
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 25) q)
    (hsouth : pay.side = .south) : q.2.val = p.D := by
  let g : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D, by have : p.H = 2 * p.D := rfl; omega⟩)
  have hgx : g.1 = q.1 := rfl
  have hgy : g.2.val = p.D := rfl
  have hstage : Template.read pay.side pay.requests ∈ pageCheckStages l p := by
    exact (congrArg (fun stages : List Template => Template.read pay.side pay.requests ∈ stages)
      pay.split).mpr (List.mem_append_right _ (List.mem_cons_self ..))
  have ht : ReadTouches (.read pay.side pay.requests) g := by
    simpa only [ReadTouches, hsouth, Direction.lane] using pay.on_line
  obtain ⟨_, cols, hrequests, haux⟩ := page_cut_payment_shape l p hl hM haxes hstage hgy ht
  have hx : q.1.val ∈ cols := by
    apply prefix_touches p .south cols (fun _ => p.D + 1)
    simpa only [ReadTouches, hsouth, hrequests] using pay.on_line
  have hcol := haux hx
  have hg := auxiliary_central_marker l p (q := g) hcol hgy
  obtain ⟨cut, hcutSouth, cutCols, hcutReq, _⟩ :=
    canonical_cut_payment_lower l p hl hM haxes initial target hr ha hg hgy
  obtain ⟨hbefore, hinput, houtput⟩ := pageCheck_south_payments_same l p hl pay cut hsouth hcutSouth hgx.symm
  have hsplit : pageChecks l p .lower ++ pageChecks l p .upper =
      cut.before ++ .read .south (prefixRequests cutCols fun _ => p.D + 1) :: cut.after := by
    simpa only [pageCheckStages, hcutSouth, hcutReq] using cut.split
  have hcutx : g.1.val ∈ cutCols := by
    apply prefix_touches p .south cutCols (fun _ => p.D + 1)
    simpa only [ReadTouches, hcutSouth, hcutReq] using cut.on_line
  have hbound := lowerFinish_target_front_card_le_one l p hl hM haxes target cut.before cut.after cutCols hsplit g.1.val hcutx
  have hread : Scan.eval (instructions (emit [.read .south (prefixRequests cutCols fun _ => p.D + 1)]
      (emit cut.before (pageCheckTarget l p target)).remaining).rounds) cut.input = some cut.output := by
    simpa only [hcutSouth, hcutReq] using cut.read_eval
  have heq := south_round_front_at_most_one_deletion_unique cutCols (fun _ => p.D + 1) _ _ _
    hcutx hread hbound cut.present cut.removed (hinput ▸ pay.present) (houtput ▸ pay.removed) hgx.symm
  exact (congrArg (fun a : Cell (p.W + 1) (p.H + 1) => a.2.val) heq).trans hgy

end PushPuzzle.Push.AcceptanceSoundness
