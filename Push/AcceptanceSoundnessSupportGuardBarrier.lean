/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportResidual
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceSoundnessCentralFlanks
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramStock
import all PushS.PortCentralStrip
import all PushS.PortEndpointLocality
import all PushS.PortSegments

/-! Every actual guard-column north read is bounded by its retained literal D−4 marker. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

private theorem central_not_street_row (p : Scales.Parameters) {y : ℕ}
    (hy : p.D ≤ y + 4) (hy' : y ≤ p.D + 4) : y ∉ streetRows (coordinates p) := by
  have hD := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  intro hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    change y = 0 ∨ y = p.H at hr
    omega
  · obtain ⟨j, _, hr⟩ := List.mem_flatMap.mp hr
    have hY := readDepth_le_last p (j + 1)
    change y ∈ [readDepth p (j + 1), readDepth p (j + 1) + 2,
      p.H - readDepth p (j + 1), p.H - (readDepth p (j + 1) + 2)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega

private theorem actual_guard_marker_fixed (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ AcceptanceProgram.guards l p) : point x (p.D - 4) ∈ l.fixedSegments p := by
  let c := coordinates p
  let base := interiorFixed l c
  let oldGuards := guardColumns l c (PortLayout.frame c ++ base)
  let shifted := if oldGuards.any (fun x => oldGuards.contains (x + 1)) then base.map (shiftPoint oldGuards (streetRows c)) else base
  let aux := (streetColumns l c).filter fun x => decide (x ≠ 0 ∧ x ≠ c.W) && !((axisColumns l c).contains x)
  let marked := shifted ++ aux.flatMap fun x => [point x (c.D - 2), point x (c.D + 2)]
  have hfixed : l.fixedSegments p = PortLayout.frame c ++
      (marked ++ (guardColumns l c (PortLayout.frame c ++ marked)).map (fun x => point x (c.D - 4)) ++
        (centers l).flatMap fun i => [point (c.x i + 2) (c.D + 4), point (c.x i + 10) (c.D + 4)]) := rfl
  have hg : x ∈ guardColumns l c (l.fixedSegments p) := List.mem_toFinset.mp hx
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hg
  unfold guardColumns at hg
  split at he
  next hcond =>
    have hsx : s.start.1 = x := Option.some.inj he
    have hrow : s.start.2 ∈ streetRows c := List.contains_iff_mem.mp hcond.2.2.1
    have hsource : s ∈ PortLayout.frame c ++ marked := by
      rw [hfixed] at hs
      rcases List.mem_append.mp hs with hf | hs
      · exact List.mem_append_left _ hf
      rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_append.mp hs with hm | hg
        · exact List.mem_append_right _ hm
        · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hg
          have hy : (point z (c.D - 4)).start.2 = p.D - 4 := by simp [point, PortLayout.segment, c, coordinates]
          have hD := p.outer_distance
          exact (central_not_street_row p (y := p.D - 4) (by omega) (by omega) (hy ▸ hrow)).elim
      · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        all_goals
          simp only [point, PortLayout.segment, Nat.min_self] at hrow
          change p.D + 4 ∈ streetRows (coordinates p) at hrow
          exact (central_not_street_row p (y := p.D + 4) (by omega) (by omega) hrow).elim
    have hraw : x ∈ guardColumns l c (PortLayout.frame c ++ marked) := by
      apply List.mem_filterMap.mpr
      exact ⟨s, hsource, by rw [ite_eq_left hcond]; exact congrArg some hsx⟩
    rw [hfixed]
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨x, hraw, rfl⟩
  next hcond => cases he

/-- Every column actually selected by the guard read has its actual central guard marker. -/
theorem actual_guard_marker (l : PortLayout) (p : Scales.Parameters) (x : Fin (p.W + 1))
    (hx : x.val ∈ guards l p) :
    ∃ g : Cell (p.W + 1) (p.H + 1), g.1 = x ∧ g.2.val = p.D - 4 ∧ g ∈ l.centralMarkers p := by
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let g : Cell (p.W + 1) (p.H + 1) := (x, ⟨p.D - 4, by omega⟩)
  have hnot : x.val ∉ streetColumns l (coordinates p) := by
    intro hs
    exact guard_not_street l p (l.fixedSegments p) hs (List.mem_toFinset.mp hx)
  have hx0 : x.val ≠ 0 := by intro he; exact hnot (by simp [streetColumns, he])
  have hxW : x.val ≠ p.W := by intro he; exact hnot (by simp [streetColumns, he, coordinates])
  refine ⟨g, rfl, rfl, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩⟩
  · exact (SegmentRecipe.mem_holes _ g).mpr ⟨point x.val (p.D - 4), actual_guard_marker_fixed l p hx,
      by simp [point, PortLayout.segment, Segment.Contains, g]⟩
  · intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame g).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, g] at hd <;> omega
  · change p.D ≤ p.D - 4 + 4 ∧ p.D - 4 ≤ p.D + 4
    omega

/-- The actual twelfth-round residual still contains every literal D−4 guard marker. -/
theorem guard_markers_residual (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.centralMarkers p) (hy : g.2.val = p.D - 4) :
    g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 12 := by
  have hsplit : ∃ right, schedule l p (targetHoles l p target \ Boundary.frame).card =
      guardBefore l p target ++ readRows p .west {p.D - 4} :: right := by
    unfold schedule preparation guardBefore flankBefore sideClearSchedule
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns,
      firstRowKeep, secondRowKeep, reduceCtorEq, ite_true, ite_false, List.append_assoc,
      List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨right, hsplit⟩ := hsplit
  obtain ⟨F, hF, hmarkers⟩ := central_stage_saturation_trace l p hl hM haxes initial target hr hp hs ha
    (guardBefore l p target) right .west {p.D - 4} (Or.inl rfl) (by
      intro y hy
      have he := Finset.mem_singleton.mp hy
      have hD := p.outer_distance
      omega) hsplit (by unfold guardBefore flankBefore; exact ⟨_, by rw [List.append_assoc]⟩)
    (by intro q hq hrow; exact guard_target_kept l p hl hM haxes target hq (Finset.mem_singleton.mp hrow))
  have htake : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 12 = guardBefore l p target := by
    simp only [schedule, preparation, frameSchedule, guardBefore, flankBefore, sideClearSchedule,
      mainRound, mainTop, mainBottom, privateRound, privateColumns, firstRowKeep, secondRowKeep,
      reduceCtorEq, ite_true, ite_false, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  unfold roundResidual
  rw [htake, hF]
  exact hmarkers (Finset.mem_filter.mpr ⟨hg, Finset.mem_singleton.mpr hy⟩)

end PushPuzzle.Push.AcceptanceSoundness
