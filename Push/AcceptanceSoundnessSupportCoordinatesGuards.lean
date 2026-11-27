/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCoordinatesIsolation
import all PushS.PortSegments
import all PushS.PortHoleBudget
import all PushS.PortEndpointLocality
import all PushS.PortFixedSeparation
import all PushS.PortCoreCrossing
import all PushS.PortWalkBudget
import all Push.AcceptanceProgramLayout

/-! The actual conditional rounding makes the emitted guard columns separated. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private def GuardPoint (l : PortLayout) (c : Coordinates) (s : Segment) : Prop :=
  s.start = s.finish ∧ !((streetColumns l c).contains s.start.1) ∧
    (streetRows c).contains s.start.2 ∧
    (streetColumns l c).all (fun x => decide (14 < Nat.dist s.start.1 x))

private theorem guard_mem_iff (l : PortLayout) (c : Coordinates) (ss : List Segment) (x : ℕ) :
    x ∈ guardColumns l c ss ↔ ∃ s ∈ ss, GuardPoint l c s ∧ s.start.1 = x := by
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := List.mem_filterMap.mp hx
    split at hx
    next hpred => exact ⟨s, hs, hpred, Option.some.inj hx⟩
    next hpred => cases hx
  · rintro ⟨s, hs, hpred, hx⟩
    apply List.mem_filterMap.mpr
    refine ⟨s, hs, ?_⟩
    unfold GuardPoint at hpred
    rw [ite_eq_left hpred, hx]

private theorem central_not_street_row (p : Scales.Parameters) {row : ℕ}
    (hlo : p.D ≤ row + 4) (hhi : row ≤ p.D + 4) : row ∉ streetRows (coordinates p) := by
  intro hr
  have hD := readDepth_add_lt_D p 0
  have hH : p.H = 2 * p.D := rfl
  change row ∈ [0, p.H] ++ _ at hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  · obtain ⟨j, _, hr⟩ := List.mem_flatMap.mp hr
    have hwork := readDepth_add_lt_D p (j + 1)
    change row ∈ [readDepth p (j + 1), readDepth p (j + 1) + 2,
      p.H - readDepth p (j + 1), p.H - (readDepth p (j + 1) + 2)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega

private theorem central_not_guard (l : PortLayout) (p : Scales.Parameters) (x row : ℕ)
    (hlo : p.D ≤ row + 4) (hhi : row ≤ p.D + 4) : ¬ GuardPoint l (coordinates p) (point x row) := by
  intro hg
  have hrow := List.contains_iff_mem.mp hg.2.2.1
  apply central_not_street_row p hlo hhi
  simpa only [point, segment, min_self] using hrow

private theorem actual_guard_origin (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ guards l p) :
    ∃ s ∈ interiorFixed l (coordinates p), GuardPoint l (coordinates p) (roundedPiece l p s) ∧
      (roundedPiece l p s).start.1 = x := by
  have hDc : (coordinates p).D = p.D := rfl
  have hD : 0 < p.D := by have := readDepth_add_lt_D p 0; omega
  have hW : 0 < (coordinates p).W := by change 0 < p.W; unfold Scales.Parameters.W; positivity
  have hH : 0 < (coordinates p).H := by change 0 < p.H; unfold Scales.Parameters.H; omega
  have hx : x ∈ guardColumns l (coordinates p) (l.fixedSegments p) := List.mem_toFinset.mp hx
  rw [fixedSegments, guardColumns_frame_append l (coordinates p) _ hW hH] at hx
  obtain ⟨s, hs, hpred, he⟩ := (guard_mem_iff _ _ _ x).mp hx
  unfold markedInterior at hs
  extract_lets base guardList shifted aux marked at hs
  change s ∈ ((shifted ++ _) ++ _) ++ _ at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs
  · change s ∈ (let c := coordinates p
      let gs := guardColumns l c (frame c ++ interiorFixed l c)
      if gs.any (fun x => gs.contains (x + 1)) then
        (interiorFixed l c).map (shiftPoint gs (streetRows c)) else interiorFixed l c) at hs
    rw [roundedInterior_eq] at hs
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
    exact ⟨old, hold, hpred, he⟩
  · obtain ⟨col, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals
      exact False.elim (central_not_guard l p _ _ (by have := p.outer_distance; omega) (by omega) hpred)
  · obtain ⟨col, _, rfl⟩ := List.mem_map.mp hs
    exact False.elim (central_not_guard l p _ _ (by have := p.outer_distance; omega) (by omega) hpred)
  · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals exact False.elim (central_not_guard l p _ _ (by omega) (by omega) hpred)

private def rawGuards (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  guardColumns l (coordinates p) (frame (coordinates p) ++ interiorFixed l (coordinates p))

private theorem rounded_guard_even (l : PortLayout) (p : Scales.Parameters)
    (hround : (rawGuards l p).any (fun x => (rawGuards l p).contains (x + 1)) = true)
    {s : Segment} (hs : s ∈ interiorFixed l (coordinates p))
    (hg : GuardPoint l (coordinates p) (roundedPiece l p s)) : (roundedPiece l p s).start.1 % 2 = 0 := by
  dsimp only [rawGuards] at hround
  unfold roundedPiece at hg ⊢
  rw [ite_eq_left hround] at hg ⊢
  unfold shiftPoint at hg ⊢
  split_ifs at hg ⊢ with hshift
  · simp only [point, segment, min_self]
    have := Nat.mod_lt s.start.1 (by decide : 0 < 2)
    omega
  · have horiginal : s.start.1 ∈ guardColumns l (coordinates p)
        (frame (coordinates p) ++ interiorFixed l (coordinates p)) :=
      (guard_mem_iff _ _ _ _).mpr ⟨s, List.mem_append_right _ hs, hg, rfl⟩
    exact False.elim (hshift ⟨hg.1, List.contains_iff_mem.mpr horiginal, hg.2.2.1⟩)

/-- The actual marked emitter's guard columns contain no consecutive coordinates. -/
theorem acceptanceGuards_separated (l : PortLayout) (p : Scales.Parameters) {x y : ℕ}
    (hx : x ∈ guards l p) (hy : y ∈ guards l p) : x + 1 ≠ y := by
  obtain ⟨s, hs, hsg, hsx⟩ := actual_guard_origin l p hx
  obtain ⟨t, ht, htg, hty⟩ := actual_guard_origin l p hy
  let raw := rawGuards l p
  by_cases hround : raw.any (fun x => raw.contains (x + 1)) = true
  · have hxEven := rounded_guard_even l p hround hs hsg
    have hyEven := rounded_guard_even l p hround ht htg
    omega
  · dsimp only [raw, rawGuards] at hround
    unfold roundedPiece at hsg hsx htg hty
    rw [ite_eq_right hround] at hsg hsx htg hty
    have hrawX : x ∈ raw := (guard_mem_iff _ _ _ _).mpr ⟨s, List.mem_append_right _ hs, hsg, hsx⟩
    have hrawY : y ∈ raw := (guard_mem_iff _ _ _ _).mpr ⟨t, List.mem_append_right _ ht, htg, hty⟩
    intro he
    apply hround
    exact List.any_eq_true.mpr ⟨x, hrawX, List.contains_iff_mem.mpr (he ▸ hrawY)⟩

/-- Every actual guard column is farther than fourteen cells from every original street column. -/
theorem acceptanceGuard_street_far (l : PortLayout) (p : Scales.Parameters) {x y : ℕ}
    (hx : x ∈ guards l p) (hy : y ∈ l.streetColumnCoordinates p) : 14 < Nat.dist x y := by
  have hx : x ∈ guardColumns l (coordinates p) (l.fixedSegments p) := List.mem_toFinset.mp hx
  obtain ⟨s, _, hg, he⟩ := (guard_mem_iff _ _ _ _).mp hx
  have hh := List.all_eq_true.mp hg.2.2.2 y hy
  exact he ▸ of_decide_eq_true hh

/-- Guard columns remain farther than four cells from each actual +2/+10 gate sample column. -/
theorem acceptanceGuard_sample_far (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) {g x : ℕ}
    (hg : g ∈ guards l p) (hx : x ∈ samples l p) : 4 < Nat.dist g x := by
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hx)
  obtain ⟨kind, first, hgate, he⟩ := center_gate_mem l hi
  have hi' : i < l.portCount := by rw [he]; exact gate_middle_lt l hl hgate
  have haxis := axis_in_streetColumns l p hi'
  have hfar := l.acceptanceGuard_street_far p hg haxis
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [Nat.dist] at hfar ⊢
  rcases hx with hx | hx <;> omega

end PushPuzzle.PushS.PortLayout
