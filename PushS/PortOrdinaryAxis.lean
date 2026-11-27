/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisMacro
import all PushS.PortAxisMacro
import all PushS.PortEndpointCounts
import all PushS.PortSegmentInventory
import all PushS.PortSegments

/-! The actual open ordinary main axis has five canonical holes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The original vertical axis with its two frame cells removed. -/
@[expose] def ordinaryAxis (p : Scales.Parameters) (port : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1.val = p.x port ∧ 0 < q.2.val ∧ q.2.val < p.H

/-- Both actual axis-near signal traces, one from each page. -/
def ordinaryAxisSegments (p : Scales.Parameters) (state : SignalState) (upper lower : Endpoint) : List Segment :=
  (endpointSegments (coordinates p) state upper).take 1 ++
    (endpointSegments (coordinates p) state lower).take 1

private theorem horizontal_near_off_axis (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles ((endpointSegments (coordinates p) state e).drop 1)) : q.1 ≠ p.x e.port := by
  have hx : readLength p 0 + 64 < (coordinates p).x e.port := readLength_add_lt_x p e.port 0
  have hb := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
    else !(state.internal.getD e.internal false))
  dsimp only [endpointSegments] at hq
  simp only [List.drop_succ_cons, List.drop_zero, horizontal_mem] at hq
  change q.1 ≠ (coordinates p).x e.port
  cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false, inward] at hq hb <;> omega

private theorem axis_near_inside (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointSegments (coordinates p) state e).take 1)) : q ∈ ordinaryAxis p e.port := by
  have hm := (axis_mem p state e _).mp ((finite_mem p _ q).mp hq)
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hH := readDepth_add_lt_H p e.level
  have hb := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false else !(state.axes.getD e.port false))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hm.1, ?_⟩
  cases hs : e.side <;>
    simp only [hs, reduceCtorEq, ite_true, ite_false, onSide, show (coordinates p).H = p.H from rfl] at hm hb <;> omega

/-- The complete marked board contributes precisely the two axis-near traces to an ordinary axis. -/
theorem encodedSegments_ordinaryAxis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ ordinaryAxis p upper.port =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (ordinaryAxisSegments p state upper lower) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hh, hr⟩ := Finset.mem_inter.mp hq
    have hr := (Finset.mem_filter.mp hr).2
    rw [full_split l p hl state hu hlow hsu hsl hport] at hh
    rcases Finset.mem_union.mp hh with hrest | hpair
    · rw [← hport] at hrest
      exact False.elim (rest_axis_clear l p hl hM ha state hlow hsl ((finite_mem p _ q).mp hrest)
        (by simpa only [hport] using hr.1) hr.2.1 hr.2.2)
    · obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hpair
      apply (SegmentRecipe.mem_holes _ q).mpr
      rcases List.mem_append.mp hs with hs | hs
      · rw [← List.take_append_drop 1 (endpointSegments (coordinates p) state upper)] at hs
        rcases List.mem_append.mp hs with hs | hs
        · exact ⟨s, List.mem_append_left _ hs, hc⟩
        · exact False.elim (horizontal_near_off_axis p state upper ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hr.1)
      · rw [← List.take_append_drop 1 (endpointSegments (coordinates p) state lower)] at hs
        rcases List.mem_append.mp hs with hs | hs
        · exact ⟨s, List.mem_append_right _ hs, hc⟩
        · exact False.elim (horizontal_near_off_axis p state lower ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
            (by simpa only [hport] using hr.1))
  · intro hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    have hpair : s ∈ endpointSegments (coordinates p) state upper ++ endpointSegments (coordinates p) state lower := by
      rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_append_left _ (List.mem_of_mem_take hs)
      · exact List.mem_append_right _ (List.mem_of_mem_take hs)
    have haxis : q ∈ ordinaryAxis p upper.port := by
      rcases List.mem_append.mp hs with hs | hs
      · exact axis_near_inside l p hl hM state upper hu ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)
      · rw [← hport]
        exact axis_near_inside l p hl hM state lower hlow ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)
    refine Finset.mem_inter.mpr ⟨?_, haxis⟩
    rw [full_split l p hl state hu hlow hsu hsl hport]
    exact Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hpair, hc⟩)

/-- Every canonical assignment has five holes on an actual ordinary shared axis. -/
theorem encodedSegments_ordinaryAxis_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ ordinaryAxis p upper.port).card = 5 := by
  rw [l.encodedSegments_ordinaryAxis p hl hM ha state hu hlow hsu hsl hport, SegmentRecipe.holes_card_of_bounds]
  · exact endpointAxes_card p state upper lower hsu hsl hport.symm
      (l.endpoints_level_bounds p hl hM hu) (l.endpoints_level_bounds p hl hM hlow)
  · intro q hq
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    have hs' : s ∈ l.signalSegments p state := by
      apply List.mem_append_left
      rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_flatMap.mpr ⟨upper, hu, List.mem_of_mem_take hs⟩
      · exact List.mem_flatMap.mpr ⟨lower, hlow, List.mem_of_mem_take hs⟩
    have hb := l.signalSegments_contains_bounds p hl ha state hs' hc
    omega

end PushPuzzle.PushS.PortLayout
