/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentralRead
public import Push.AcceptanceProgramColumns
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgramRegions
import all Push.AcceptanceProgramColumns
import all PushS.PortCentralStrip
import all PushS.PortSegments

/-! The actual two central flank reads preserve and saturate all markers on rows D−2 and D+2. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram PushS.PortLayout

private theorem emit_preserves {w h : ℕ} (stages : List Template) (T : Finset (Cell w h)) {q : Cell w h}
    (hq : q ∈ T) (hn : ∀ stage ∈ stages, q ∉ stage.region) : q ∈ (emit stages T).remaining := by
  rw [emit_remaining]
  refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
  rintro h
  obtain ⟨stage, hm, hq⟩ := (mem_allRegions stages q).mp h
  exact hn stage hm hq

private theorem side_target_marker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (haxes : l.portCount ≤ p.axes) (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ l.centralMarkers p) :
    q ∈ (emit (sideClearSchedule l p target) (targetHoles l p target)).remaining := by
  have ht := l.centralMarkers_subset_encoded p (l.canonical target) hq
  have hf : q ∉ Boundary.frame := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).2
  have hx := target_interior_side_margins l p hl haxes target (Finset.mem_sdiff.mpr ⟨ht, hf⟩)
  rw [sideClearSchedule, emit_remaining_append, frame_remaining]
  change q ∈ (targetHoles l p target \ Boundary.frame).filter _
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨ht, hf⟩, ?_⟩
  intro hb
  have h := (Finset.mem_filter.mp hb).2
  change (1 ≤ q.1.val ∧ q.1.val ≤ (targetHoles l p target \ Boundary.frame).card) ∨
    (p.W - (targetHoles l p target \ Boundary.frame).card ≤ q.1.val ∧ q.1.val < p.W) at h
  omega

private theorem acceptance_level (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (side : Side) {a : PageColumn} (ha : a ∈ pageColumns l p side) :
    1 ≤ a.level ∧ a.level ≤ p.levels := by
  rcases PortLayout.acceptance_column_data l p side ha with ⟨e, he, _, hlev, _⟩ | ⟨_, hlev, _⟩
  · rw [hlev]
    exact l.endpoints_level_bounds p hl hM he
  · rw [hlev]
    exact ⟨le_rfl, p.levels_pos⟩

private theorem trim_depth_le (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    trimDepth p j ≤ p.D - 2 := by
  unfold trimDepth
  split
  · rename_i hlt
    have hy := readDepth_le_last p j
    have hy' := readDepth_le_last p (j + 1)
    rw [readDepth_eq p hj hjm] at hy
    rw [readDepth_eq p (by omega) (by omega)] at hy'
    have hD := PortLayout.last_depth_margin p
    omega
  · exact le_rfl

private theorem trim_depth_bound (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (trimRound l p side).region) : pageDepth p side q < p.D - 2 := by
  obtain ⟨a, ha, _, _, hdepth⟩ := (mem_trim_region l p side q).mp hq
  have hj := acceptance_level l p hl hM side ha
  exact hdepth.trans_le (trim_depth_le p hj.1 hj.2)

private theorem main_depth_bound (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (mainRound l p side).region) : pageDepth p side q < p.Y p.levels + 2 := by
  change q ∈ readRegion _ _ at hq
  obtain ⟨request, hm, _, hdepth⟩ := (mem_readRegion _ _ q).mp hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have hj := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
  have hy := readDepth_le_last p e.level
  rw [readDepth_eq p hj.1 hj.2] at hy
  have hr : prefixRank (if side = .upper then .north else .south) q = pageDepth p side q := by
    cases side <;> simp [prefixRank, pageDepth]
  rw [hr] at hdepth
  exact hdepth.trans_le (by omega)

private def flankBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  sideClearSchedule l p target ++
    [trimRound l p .lower, trimRound l p .upper,
      .clear .west (Finset.range (p.H + 1) \ firstRowKeep l p),
      mainRound l p .upper, mainRound l p .lower,
      .clear .west (Finset.range (p.H + 1) \ secondRowKeep l p), privateRound l p]

private theorem flank_target_kept (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p)
    (hrow : q.2.val ∈ ({p.D - 2, p.D + 2} : Finset ℕ)) :
    q ∈ (emit (flankBefore l p target) (targetHoles l p target)).remaining := by
  have hD := PortLayout.last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hy1 := readDepth_le_last p 1
  rw [readDepth_eq p (by omega) p.levels_pos] at hy1
  have hrow' : q.2.val = p.D - 2 ∨ q.2.val = p.D + 2 := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hrow
  have hkeep : q.2.val ∈ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [flankBefore, emit_remaining_append]
  apply emit_preserves _ _ (side_target_marker l p hl haxes target hq)
  intro stage hstage hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := trim_depth_bound l p hl hM .lower hcontains
    simp only [pageDepth, reduceCtorEq, ite_false] at h
    omega
  · have h := trim_depth_bound l p hl hM .upper hcontains
    simp only [pageDepth, ite_true] at h
    omega
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcontains).2).2 (by simp only [firstRowKeep, keepRows, Finset.mem_union]; tauto)
  · have h := main_depth_bound l p hl hM .upper hcontains
    simp only [pageDepth, ite_true] at h
    omega
  · have h := main_depth_bound l p hl hM .lower hcontains
    simp only [pageDepth, reduceCtorEq, ite_false] at h
    omega
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcontains).2).2 (marker_row_keep_narrow l p hkeep)
  · have h := (private_region l p q).mp hcontains
    omega

/-- The literal D−2 and D+2 reads force all their actual central markers to remain final holes. -/
theorem flank_markers_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (l.centralMarkers p).filter (fun q => q.2.val ∈ ({p.D - 2, p.D + 2} : Finset ℕ)) ⊆ PushS.holes t := by
  have hsplit : ∃ right, schedule l p (targetHoles l p target \ Boundary.frame).card =
      flankBefore l p target ++ readRows p .east {p.D - 2, p.D + 2} :: right := by
    unfold schedule preparation flankBefore sideClearSchedule
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns,
      firstRowKeep, secondRowKeep, reduceCtorEq, ite_true, ite_false, List.append_assoc,
      List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨right, hsplit⟩ := hsplit
  refine central_stage_saturation l p hl hM haxes initial target hr hp hs ha
    (flankBefore l p target) right .east _ (Or.inr rfl) ?_ hsplit ⟨_, rfl⟩ ?_
  · intro y hy
    have hD := p.outer_distance
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    omega
  · intro q hq hrow
    exact flank_target_kept l p hl hM haxes target hq hrow

end PushPuzzle.Push.AcceptanceSoundness
