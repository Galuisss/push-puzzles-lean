/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateWalks
public import Push.AcceptanceSoundnessTrimBarrier
import all Push.AcceptanceProgramTrimStock
import all Push.AcceptanceProgramLayout
import all PushS.PortGatePrivateWalk
import all PushS.PortGatePublicWalk
import all PushS.PortGateBottomWall
import all PushS.PortGatePageWindow
import all PushS.PortGateTails
import all PushS.PortCentralFreeze
import all PushS.PortOrdinaryFailure
import all PushS.PortSegments

/-! Frozen public gate-column tails confine their actual trim payments to the outer corridor and work cell. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Every public gate column occurs as an actual lower-page nonprivate trim request at level one. -/
theorem gate_public_column_mem (l : PortLayout) (p : Scales.Parameters) {middle x : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) (hx : x ∈ gatePublicColumns p middle) :
    (⟨x, 1, false⟩ : PageColumn) ∈ pageColumns l p .lower := by
  simp only [AcceptanceProgram.pageColumns, List.mem_append, ite_true]
  right
  apply List.mem_flatMap.mpr
  refine ⟨middle, hi, ?_⟩
  simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hi

private theorem public_deep_guard {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ gatePublicColumns p middle) (near : readDepth p 1 < p.H - q.2.val)
    (far : p.H - q.2.val < trimDepth p 1) (central : q ∉ l.centralMarkers p) :
    q ∈ l.gatePrivateBlockers p hl hM haxes hi ∧ q ∈ (I).initial.boxes := by
  have Y := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have margin := readDepth_add_lt_D p 1
  have H : p.H = 2 * p.D := rfl
  have read : readDepth p 1 = p.Y 1 := readDepth_eq p (by omega) p.levels_pos
  have bound := trimDepth_lt_D p (show 1 ≤ 1 by omega) p.levels_pos
  have special := gatePublicColumn_mem_special p hx
  have px := readLength_add_lt_x p middle 0
  by_cases short : p.H - q.2.val ≤ readDepth p 1 + 2
  · have rows : q.2.val = p.H - (readDepth p 1 + 1) ∨ q.2.val = p.H - (readDepth p 1 + 2) := by omega
    have guard : q ∈ l.gatePublicBlockers p hl hM haxes hi := by
      rcases rows with first | second
      · exact gate_public_cap l p hl hM haxes hi hx first
      · let left := gateLeftSeparator l p hl hM haxes hi
        let right := gateRightSeparator l p hl hM haxes hi
        have row := public_bottom_row l p middle left right hx
        have same : bottomCell p q.1 2 = q := Prod.ext rfl (Fin.ext (by simpa only [bottomCell] using second.symm))
        rw [same] at row
        rcases bottom_point l p hl middle left right (fun _ h => h) (Or.inr row) with wall | page
        · exact Finset.mem_union_right _ wall
        · exact gate_public_page l p hl hM haxes hi page
    refine ⟨Finset.mem_union_left _ (Finset.mem_union_left _ guard), ?_⟩
    by_contra empty
    have hole := (mem_holes q).mpr empty
    have initialHoles : (holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) =
        SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
      l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
    rw [initialHoles] at hole
    have window : q ∈ gatePageWindow p middle := by
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [Nat.dist]
      omega
    have position : BottomPosition p middle (q.1.val, q.2.val) := by
      rcases rows with first | second
      · exact Or.inl ⟨hx, first⟩
      · refine Or.inr ⟨second, ?_⟩
        simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega
    exact bottom_source_clear l p (l.canonical initial) position
      (l.encodedSegments_gatePageWindow p hl hM haxes (l.canonical initial) hi window hole)
  · by_cases levels : 1 < p.levels
    · have tail : q ∈ l.gateTails p := by
        classical
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, levels, middle, hi, special, p.H - q.2.val, by omega, ?_, ?_⟩
        · simp only [trimDepth, ite_eq_left levels, gateMarkerDepth] at far ⊢
          rw [read, readDepth_eq p (by omega) (by omega)]
          simpa only [Nat.reduceAdd] using far
        · have qb := q.2.isLt
          omega
      refine ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ tail))), ?_⟩
      exact l.gateTails_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) tail
    · have last : p.levels = 1 := by have := p.levels_pos; omega
      have depth : readDepth p 1 = p.Y p.levels := by rw [last, read]
      have column : q.1 ∈ l.streetColumnSet p := by
        change q.1.val ∈ streetColumns l (coordinates p)
        exact pageColumn_mem_street l p hl .lower (l.gateSpecialColumn_mem_page p hi special)
      have main := l.gateSpecialColumn_not_main p hl haxes hi special
      have box : q ∈ l.centralAuxiliaryBoxes p :=
        (mem_centralAuxiliaryBoxes l p q).mpr ⟨column, main, by omega, by omega, central⟩
      refine ⟨private_page l p hl hM haxes hi ?_, ?_⟩
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ box))
      · exact l.centralAuxiliaryBoxes_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) box

include hi in
/-- Every deeper pre-marker cell on an actual public gate column stays occupied throughout an accepted trace. -/
theorem canonical_gate_public_trim_deep_occupied (hgate : l.gateCenterCoordinates ≠ [])
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ gatePublicColumns p middle)
    (near : readDepth p 1 < p.H - q.2.val) (far : p.H - q.2.val < trimDepth p 1)
    (central : q ∉ l.centralMarkers p) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : q ∈ u.boxes := by
  obtain ⟨guard, occupied⟩ := public_deep_guard l p hl hM haxes initial target hi hx near far central
  exact avoiding_box (canonical_gate_private_avoiding_prefix l p hl hM haxes initial target hgate hi hsu hut accepted)
    guard occupied

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
