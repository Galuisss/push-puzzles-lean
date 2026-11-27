/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceSoundnessCentralGeometry
import all Push.AcceptanceSoundnessCentralFlanks
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramColumns
import all PushS.PortGatePageWindow
import all PushS.PortFixedSeparation
import all PushS.PortTwoPageStreets
import all PushS.PortWalkBudget
import all PushS.PortSegments

/-! The literal D+4 sample row survives every earlier trim and saturates its actual quota. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem sample_off_axis (p : Scales.Parameters) (i k : ℕ) {offset : ℕ}
    (hoff : 0 < offset ∧ offset ≤ 10) : p.x i + offset ≠ p.x k := by
  have hD := p.outer_distance
  intro he
  rcases lt_trichotomy i k with h | h | h
  · have := axis_spacing p h
    omega
  · subst k
    omega
  · have := axis_spacing p h
    omega

private theorem cores_subset_axes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) : cores l p ⊆ axes l p := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, List.mem_range.mpr (gate_center_lt l hl hi), rfl⟩)

private theorem sample_not_axes (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) :
    q.1.val ∉ axes l p := by
  obtain ⟨i, _, hx⟩ := sample_marker_source l p hq hy
  intro ha
  obtain ⟨k, _, he⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  rcases hx with hx | hx
  · exact sample_off_axis p i k (by omega) (hx.symm.trans he.symm)
  · exact sample_off_axis p i k (by omega) (hx.symm.trans he.symm)

private theorem acceptance_column_page (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {a : PageColumn} (ha : a ∈ AcceptanceProgram.pageColumns l p side) :
    a.column ∈ l.pageColumnCoordinates p side := by
  change a.column ∈ PortLayout.pageColumns l (coordinates p) side
  rcases PortLayout.acceptance_column_data l p side ha with ⟨e, he, hside, _, hx⟩ | ⟨hside, _, i, hi, hx⟩
  · have h := endpoint_columns_mem l p e he (x := a.column) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto)
    simpa only [hside] using h
  · subst side
    exact gateSpecialColumn_mem_page l p hi hx

private theorem sample_not_lower_column (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (haxes : l.portCount ≤ p.axes) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) {a : PageColumn}
    (ha : a ∈ AcceptanceProgram.pageColumns l p .lower) : q.1.val ≠ a.column := by
  obtain ⟨i, hi, hx⟩ := sample_marker_source l p hq hy
  intro he
  have hcol := acceptance_column_page l p .lower ha
  rw [← he] at hcol
  have hnear : Nat.dist q.1.val (p.x i) ≤ p.L p.levels + 12 := by
    rcases hx with hx | hx <;> rw [hx] <;> simp only [Nat.dist] <;> omega
  have hown := l.gatePageColumns_near p hl haxes hi hcol hnear
  simp only [gateSpecialColumns, specialColumns, show (coordinates p).x i = p.x i from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hown
  rcases hx with hx | hx <;> omega

private theorem sample_not_guards (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) :
    q.1.val ∉ guards l p := by
  obtain ⟨i, hi, hx⟩ := sample_marker_source l p hq hy
  intro hg
  have hfar := guard_axis_far l p (l.fixedSegments p) (List.mem_toFinset.mp hg) (gate_center_lt l hl hi)
  rcases hx with hx | hx <;> rw [hx] at hfar <;> simp only [Nat.dist] at hfar <;> omega

private theorem sample_not_probe (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.D + 4) :
    q.2.val ∉ probeRows l p := by
  intro hprobe
  obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hprobe)
  have hj := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
  have hb := readDepth_le_last p e.level
  rw [readDepth_eq p hj.1 hj.2] at hb
  have hD := last_depth_margin p
  omega

private theorem sample_flank_kept (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) :
    q ∈ (emit (flankBefore l p target) (targetHoles l p target)).remaining := by
  have hD := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hy1 := readDepth_le_last p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hy1
  have hkeep : q.2.val ∈ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by simp [hy]
  rw [flankBefore, emit_remaining_append]
  apply emit_preserves _ _ (side_target_marker l p hl haxes target hq)
  intro stage hstage hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha, _, hx, _⟩ := (mem_trim_region l p .lower q).mp hcontains
    exact sample_not_lower_column l p hl haxes hq hy ha hx
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
  · have hx := (private_region l p q).mp hcontains
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx.1)
    exact sample_not_lower_column l p hl haxes hq hy (List.mem_filter.mp ha).1 he.symm

private theorem sample_guard_kept (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) :
    q ∈ (emit (guardBefore l p target) (targetHoles l p target)).remaining := by
  have hD := p.outer_distance
  rw [guardBefore, emit_remaining_append]
  apply emit_preserves _ _ (sample_flank_kept l p hl hM haxes target hq hy)
  intro stage hstage hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with rfl | rfl
  · have h := (readRows_region p .east _ (Or.inr rfl) q).mp hcontains
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega
  · change q ∈ readRegion .north _ at hcontains
    obtain ⟨a, ha, _, hspan⟩ := (mem_readRegion _ _ q).mp hcontains
    obtain ⟨_, hspan'⟩ := (mem_prefixRequests _ _ _ _).mp ha
    simp only [prefixRank] at hspan
    omega

private def sampleBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  guardBefore l p target ++ [readRows p .west {p.D - 4}, readRows p .west (probeRows l p),
    .clear .east (probeRows l p), axisReadRound l p, .clear .north (axes l p \ cores l p),
    .clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p),
    .read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1),
    readColumns p .south (guards l p), .clear .north (guards l p),
    .read .south (prefixRequests (samples l p) fun _ => p.D - 4)]

private theorem sample_target_kept (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) :
    q ∈ (emit (sampleBefore l p target) (targetHoles l p target)).remaining := by
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  have haxis := sample_not_axes l p hq hy
  have hguard := sample_not_guards l p hl hq hy
  have hprobe := sample_not_probe l p hl hM hy
  rw [sampleBefore, emit_remaining_append]
  apply emit_preserves _ _ (sample_guard_kept l p hl hM haxes target hq hy)
  intro stage hstage hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := (readRows_region p .west _ (Or.inl rfl) q).mp hcontains
    simp only [Finset.mem_singleton] at h
    omega
  · exact hprobe ((readRows_region p .west _ (Or.inl rfl) q).mp hcontains)
  · exact hprobe (Finset.mem_filter.mp hcontains).2
  · change q ∈ readRegion .north _ at hcontains
    obtain ⟨a, ha, hx, _⟩ := (mem_readRegion _ _ q).mp hcontains
    change q.1.val = a.1 at hx
    rcases List.mem_append.mp ha with ha | ha
    · exact haxis (hx.symm ▸ (Finset.mem_sdiff.mp ((mem_prefixRequests _ _ _ _).mp ha).1).1)
    · exact haxis (hx.symm ▸ cores_subset_axes l p hl ((mem_prefixRequests _ _ _ _).mp ha).1)
  · exact haxis (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcontains).2).1
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcontains).2).2 (by
      apply Finset.mem_union_right
      exact Finset.mem_singleton.mpr hy)
  · change q ∈ readRegion .north _ at hcontains
    obtain ⟨a, ha, hx, _⟩ := (mem_readRegion _ _ q).mp hcontains
    change q.1.val = a.1 at hx
    exact haxis (hx.symm ▸ cores_subset_axes l p hl ((mem_prefixRequests _ _ _ _).mp ha).1)
  · exact hguard ((readColumns_region p .south _ (Or.inr rfl) q).mp hcontains)
  · exact hguard (Finset.mem_filter.mp hcontains).2
  · change q ∈ readRegion .south _ at hcontains
    obtain ⟨a, ha, _, hspan⟩ := (mem_readRegion _ _ q).mp hcontains
    have hspan' := ((mem_prefixRequests _ _ _ _).mp ha).2
    simp only [prefixRank, Nat.add_sub_cancel] at hspan
    omega

/-- The actual D+4 read forces both independent short-train sample markers to remain final holes. -/
theorem sample_markers_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (l.centralMarkers p).filter (fun q => q.2.val = p.D + 4) ⊆ PushS.holes t := by
  have hsplit : ∃ right, schedule l p (targetHoles l p target \ Boundary.frame).card =
      sampleBefore l p target ++ readRows p .east {p.D + 4} :: right := by
    unfold schedule preparation sampleBefore guardBefore flankBefore sideClearSchedule
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns, axisReadRound,
      thirdRowKeep, firstRowKeep, secondRowKeep, reduceCtorEq, ite_true, ite_false, List.append_assoc,
      List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨right, hsplit⟩ := hsplit
  have h := central_stage_saturation l p hl hM haxes initial target hr hp hs ha
    (sampleBefore l p target) right .east {p.D + 4} (Or.inr rfl) (by
      intro y hy
      have he := Finset.mem_singleton.mp hy
      omega) hsplit (by unfold sampleBefore guardBefore flankBefore; exact ⟨_, by simp only [List.append_assoc]; rfl⟩)
    (by intro q hq hy; exact sample_target_kept l p hl hM haxes target hq (Finset.mem_singleton.mp hy))
  simpa only [Finset.mem_singleton] using h

end PushPuzzle.Push.AcceptanceSoundness
