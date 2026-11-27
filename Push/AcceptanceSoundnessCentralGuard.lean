/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentralGeometry
import all Push.AcceptanceSoundnessCentralGeometry
import all Push.AcceptanceSoundnessCentralFlanks
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramColumns
import all PushS.PortFixedSeparation
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! The actual D−4 guard-row read protects all far horizontal separator markers. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem acceptance_column_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (side : Side) {a : PageColumn}
    (ha : a ∈ AcceptanceProgram.pageColumns l p side) : a.column ∈ streetColumns l (coordinates p) := by
  have haux := l.acceptancePageColumn_aux p hl hM haxes side ha
  exact List.mem_toFinset.mp (Finset.mem_sdiff.mp haux).1

private theorem main_column_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ (mainRound l p side).region) :
    q.1.val ∈ streetColumns l (coordinates p) := by
  change q ∈ readRegion _ _ at hq
  obtain ⟨request, hm, hx, _⟩ := (mem_readRegion _ _ q).mp hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have he := (List.mem_filter.mp he).1
  have haxis := axis_in_streetColumns l p (l.endpoints_port_lt hl he)
  have hx' : q.1.val = p.x e.port := by cases side <;> exact hx
  exact hx'.symm ▸ haxis

private theorem private_column_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (privateRound l p).region) : q.1.val ∈ streetColumns l (coordinates p) := by
  have hx := (private_region l p q).mp hq
  obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx.1)
  have hstreet := acceptance_column_street l p hl hM haxes .lower (List.mem_filter.mp ha).1
  exact he ▸ hstreet

private theorem guard_flank_kept (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D - 4) :
    q ∈ (emit (flankBefore l p target) (targetHoles l p target)).remaining := by
  have hoff := guard_marker_off_street l p hq hy
  have hkeep : q.2.val ∈ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by simp [hy]
  rw [flankBefore, emit_remaining_append]
  apply emit_preserves _ _ (side_target_marker l p hl haxes target hq)
  intro stage hstage hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha, _, hx, _⟩ := (mem_trim_region l p .lower q).mp hcontains
    exact hoff (hx.symm ▸ acceptance_column_street l p hl hM haxes .lower ha)
  · obtain ⟨a, ha, _, hx, _⟩ := (mem_trim_region l p .upper q).mp hcontains
    exact hoff (hx.symm ▸ acceptance_column_street l p hl hM haxes .upper ha)
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcontains).2).2 (by simp only [firstRowKeep, keepRows, Finset.mem_union]; tauto)
  · exact hoff (main_column_street l p hl .upper hcontains)
  · exact hoff (main_column_street l p hl .lower hcontains)
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcontains).2).2 (marker_row_keep_narrow l p hkeep)
  · exact hoff (private_column_street l p hl hM haxes hcontains)

private def guardBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  flankBefore l p target ++ [readRows p .east {p.D - 2, p.D + 2},
    .read .north (prefixRequests (guards l p) fun _ => p.D - 4)]

private theorem guard_target_kept (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D - 4) :
    q ∈ (emit (guardBefore l p target) (targetHoles l p target)).remaining := by
  have hD := p.outer_distance
  rw [guardBefore, emit_remaining_append]
  apply emit_preserves _ _ (guard_flank_kept l p hl hM haxes target hq hy)
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

/-- The literal D−4 horizontal read forces every guard marker to remain a final hole. -/
theorem guard_markers_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (l.centralMarkers p).filter (fun q => q.2.val = p.D - 4) ⊆ PushS.holes t := by
  have hsplit : ∃ right, schedule l p (targetHoles l p target \ Boundary.frame).card =
      guardBefore l p target ++ readRows p .west {p.D - 4} :: right := by
    unfold schedule preparation guardBefore flankBefore sideClearSchedule
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns,
      firstRowKeep, secondRowKeep, reduceCtorEq, ite_true, ite_false, List.append_assoc,
      List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨right, hsplit⟩ := hsplit
  have h := central_stage_saturation l p hl hM haxes initial target hr hp hs ha
    (guardBefore l p target) right .west {p.D - 4} (Or.inl rfl) (by
      intro y hy
      have he := Finset.mem_singleton.mp hy
      have hD := p.outer_distance
      omega) hsplit (by unfold guardBefore flankBefore; exact ⟨_, by rw [List.append_assoc]⟩)
    (by intro q hq hy; exact guard_target_kept l p hl hM haxes target hq (Finset.mem_singleton.mp hy))
  simpa only [Finset.mem_singleton] using h

end PushPuzzle.Push.AcceptanceSoundness
