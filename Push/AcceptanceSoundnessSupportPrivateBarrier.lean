/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportHalf
import all Push.AcceptanceSoundnessSupportLowerRowStock
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortLayoutCoordinates

/-! The actual private-cap read is bounded by its own certified first marker. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Every selected private column retains its first marker in the output of the real private read. -/
private theorem canonical_private_trim_marker (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (x : Fin (p.W + 1)) (hx : x.val ∈ privateColumns l p) :
    ∃ g : Cell (p.W + 1) (p.H + 1), g.1 = x ∧ pageDepth p .lower g = trimDepth p 1 ∧
      g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 10 := by
  obtain ⟨a, hac, hax⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨hac, hprivate⟩ := List.mem_filter.mp hac
  have hprivate : a.privateColumn = true := hprivate
  have hlevel : a.level = 1 := (pageColumn_public_or_first l p .lower hac).resolve_left (by
    intro hp
    rw [hp] at hprivate
    cases hprivate)
  have haux : x.val ∈ auxiliaries l p := hax ▸ l.acceptancePageColumn_aux p hl hM haxes .lower hac
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hH : p.H = 2 * p.D := rfl
  by_cases hlevels : 1 < p.levels
  · have hb := interlevelDepth_bounds p le_rfl hlevels
    let g : Cell (p.W + 1) (p.H + 1) := (x, ⟨p.H - interlevelDepth p 1, by omega⟩)
    have hy : g.2.val = interlevelRow p .lower 1 := rfl
    have hdepth : pageDepth p .lower g = trimDepth p 1 := by
      simp only [pageDepth, trimDepth, ite_eq_left hlevels, reduceCtorEq, ite_false, g, interlevelDepth]
      unfold interlevelDepth at hb
      omega
    have hm : InterlevelMarker l p .lower g := ⟨a, hac, hlevel ▸ le_rfl,
      hlevel ▸ hlevels, hax.symm, by simpa only [hlevel] using hdepth⟩
    have hinput := canonical_interlevel_marker_input l p hl hM haxes initial target hr ha .lower le_rfl hlevels hm hy
    have hglobal : g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (25 + 3) := by
      rw [canonical_pageResidual_eq l p hl hM haxes initial target hr ha]
      exact hinput
    exact ⟨g, rfl, hdepth, roundResidual_antitone _ _ _ hc (by omega : 10 ≤ 25 + 3) hglobal⟩
  · have hD := p.outer_distance
    let g : Cell (p.W + 1) (p.H + 1) := (x, ⟨p.D + 2, by omega⟩)
    have hg := auxiliary_flank_marker l p (q := g) haux (Or.inr rfl)
    refine ⟨g, rfl, ?_, ?_⟩
    · simp only [pageDepth, trimDepth, ite_eq_right hlevels, reduceCtorEq, ite_false, g]
      omega
    · exact flank_markers_residual l p hl hM haxes initial target hr
        (canonical_initial_frame l p hl hM haxes initial target)
        (canonical_initial_holes l p hl hM haxes initial target) ha
        (newCentralMarkers_subset l p hg) (Or.inr rfl)

/-- Every hole actually paid by the private-cap read lies strictly before its own preserved first marker. -/
theorem canonical_private_payment_depth (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p)
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 9)
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 10) : pageDepth p .lower q < trimDepth p 1 := by
  obtain ⟨g, hgx, hdepth, hg⟩ := canonical_private_trim_marker l p hl hM haxes initial target hr ha q.1 hx
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hlt := round_deleted_before_retained .south _ _ (roundResidual_step stages T (PushS.holes t) 9 hc hi).1
    hg hq hqout (congrArg Fin.val hgx)
  simpa only [prefixRank, Nat.add_sub_cancel, ← hdepth, pageDepth, reduceCtorEq, ite_false] using hlt

end PushPuzzle.Push.AcceptanceSoundness
