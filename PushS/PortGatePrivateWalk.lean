/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateHalfRods
import all PushS.PortGateHalfRods
import all PushS.EndpointMacros
import all PushS.PortGatePageWindow
import all PushS.PortGatePublicWalk
import all PushS.PortGateBottomWall
import all PushS.PortEndpointRWall
import all PushS.PortPageBackground
import all PushS.PortStreetSeparation
import all PushS.PortBackground
import all PushS.PortSegments

/-! The actual five-cell private gate walk is protected by its half rod and bottom walls. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def PrivatePosition (p : Scales.Parameters) (middle : ℕ) (q : ℕ × ℕ) : Prop :=
  (q.1 = p.x middle + 4 ∧ q.2 = p.H - (readDepth p 1 + 1)) ∨
    (q.2 = p.H - (readDepth p 1 + 2) ∧ p.x middle + 1 ≤ q.1 ∧ q.1 ≤ p.x middle + 4)

/-- The frame and the five literal fixed private gate holes. -/
noncomputable def gatePrivateWalk (p : Scales.Parameters) (middle : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Boundary.frame ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
    (((gateFixedSegments (coordinates p) middle).drop 4).take 2)

private theorem private_segments (p : Scales.Parameters) (middle : ℕ) :
    ((gateFixedSegments (coordinates p) middle).drop 4).take 2 =
      [point (p.x middle + 4) (p.H - (readDepth p 1 + 1)),
        segment (p.x middle + 1) (p.H - (readDepth p 1 + 2))
          (p.x middle + 4) (p.H - (readDepth p 1 + 2))] := rfl

private theorem mem_gatePrivateWalk (p : Scales.Parameters) (middle : ℕ)
    {q : Cell (p.W + 1) (p.H + 1)} : q ∈ gatePrivateWalk p middle ↔
      q ∈ Boundary.frame ∨ PrivatePosition p middle (q.1.val, q.2.val) := by
  rw [gatePrivateWalk, Finset.mem_union, private_segments]
  apply or_congr_right
  constructor
  · intro hq
    obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inl (point_coordinates hq)
    · have hp := horizontal_coordinates hq
      exact Or.inr ⟨hp.1, by omega, by omega⟩
  · intro hq
    apply (SegmentRecipe.mem_holes _ q).mpr
    rcases hq with hcap | hbranch
    · refine ⟨_, List.mem_cons_self, ?_⟩
      apply Or.inl
      simp only [point, segment, Nat.min_self, Nat.max_self, true_and]
      exact ⟨hcap.1, by have := hcap.2; omega, by have := hcap.2; omega⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      apply (horizontal_contains _ _ _ _).mpr
      exact ⟨hbranch.1, by omega, by omega⟩

/-- The complete encoding contains the frame and every literal private gate hole. -/
theorem gatePrivateWalk_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) :
    gatePrivateWalk p middle ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hp
  · exact l.encodedSegments_frame_subset p state hf
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hp
  apply (SegmentRecipe.mem_holes _ q).mpr
  exact ⟨s, List.mem_append_left _ (l.gateFixedSegments_mem_fixed p hi
    (List.mem_of_mem_drop (List.mem_of_mem_take hs))), hq⟩

private theorem private_page (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) : l.pageFrozenBlockers p hl ⊆ l.gatePrivateBlockers p hl hM ha hi :=
  fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (gate_public_page l p hl hM ha hi h))

private theorem private_bottom (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle - 1 ∨ q.1.val = p.x middle + 5)
    (hy : q.2.val = p.H - (readDepth p 1 + 2)) : q ∈ l.gatePrivateBlockers p hl hM ha hi := by
  let left := gateLeftSeparator l p hl hM ha hi
  let right := gateRightSeparator l p hl hM ha hi
  have hleft := left.outside
  have hright := right.outside
  have hx0 := readLength_add_lt_x p middle 0
  simp only [Bool.false_eq_true, ite_false, ite_true] at hleft hright
  have hrow : BottomRow l p middle left right q := by
    refine ⟨hy, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  rcases bottom_point l p hl middle left right (G := l.pageFrozenBlockers p hl)
      (fun _ h => h) (Or.inr hrow) with hw | hp
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hw))
  · exact private_page l p hl hM ha hi hp

private theorem private_deep (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 4) (hy : q.2.val = p.H - (readDepth p 1 + 3)) :
    q ∈ l.gatePrivateBlockers p hl hM ha hi := by
  have hc : (coordinates p).x = p.x := rfl
  have hs : q.1.val ∈ gateSpecialColumns p middle := by simp [gateSpecialColumns, specialColumns, hc, hx]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (l.gateTails_deep_mem p hl ha hi hs hy)))

private theorem private_near_background (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : p.x middle < q.1.val ∧ q.1.val < p.x middle + 6) (hfour : q.1.val ≠ p.x middle + 4)
    {k : ℕ} (hk : k = 1 ∨ k = 3) (hy : q.2.val = p.H - (readDepth p 1 + k)) :
    q ∈ l.gatePrivateBlockers p hl hM ha hi := by
  have hcol : q.1 ∉ l.pageColumnSet p .lower := by
    intro hc
    have hnear : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12 := by simp only [Nat.dist]; omega
    have hs := l.gatePageColumns_near p hl ha hi hc hnear
    have hc : (coordinates p).x = p.x := rfl
    simp only [gateSpecialColumns, specialColumns, hc, List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have he := readDepth_even p 1
  have hHe := H_even p
  apply private_page l p hl hM ha hi
  apply off_page_blocker l p hl
  intro hp
  rcases (l.page_support_iff_side p hl .lower q (by simp only [reduceCtorEq, ite_false]; omega)).mp hp with hr | hc
  · have hqe := l.workingRowSet_even p hr
    omega
  · exact hcol hc

/-- Half-depth back rods, actual bottom bars, and the private column tail guard all five private holes. -/
theorem gatePrivateWalk_emptyBoundary (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) :
    Freeze.EmptyBoundary (gatePrivateWalk p middle) Boundary.frame (l.gatePrivateBlockers p hl hM ha hi) := by
  constructor
  intro d q a b hq hf hadj han hab
  have hpos := ((mem_gatePrivateWalk p middle).mp hq).resolve_left hf
  have ha_out : ¬PrivatePosition p middle (a.1.val, a.2.val) :=
    fun h => han ((mem_gatePrivateWalk p middle).mpr (Or.inr h))
  have hY := readDepth_add_lt_H p 1
  have hx0 := readLength_add_lt_x p middle 0
  rcases hpos with hcap | hbranch
  · cases d with
    | north =>
      simp only [Adjacent] at hadj hab
      right
      apply Finset.mem_union_right
      apply l.gateHalfRods_back_mem p hi (Or.inr ?_) (by omega)
      exact (congrArg Fin.val (hadj.1.trans hab.1)).symm.trans hcap.1
    | south =>
      simp only [Adjacent] at hadj hab
      exact False.elim (ha_out (Or.inr ⟨by omega, by omega, by omega⟩))
    | east =>
      simp only [Adjacent] at hadj hab
      left
      exact private_near_background l p hl hM ha hi ⟨by omega, by omega⟩ (by omega) (Or.inl rfl)
        ((congrArg Fin.val hadj.2).symm.trans hcap.2)
    | west =>
      simp only [Adjacent] at hadj hab
      left
      exact private_near_background l p hl hM ha hi ⟨by omega, by omega⟩ (by omega) (Or.inl rfl)
        ((congrArg Fin.val hadj.2).symm.trans hcap.2)
  · cases d with
    | north =>
      simp only [Adjacent] at hadj hab
      have hax := congrArg Fin.val hadj.1
      by_cases hfour : a.1.val = p.x middle + 4
      · exact False.elim (ha_out (Or.inl ⟨hfour, by omega⟩))
      · left
        exact private_near_background l p hl hM ha hi ⟨by omega, by omega⟩ hfour (Or.inl rfl) (by omega)
    | south =>
      simp only [Adjacent] at hadj hab
      have hax := congrArg Fin.val hadj.1
      left
      by_cases hfour : a.1.val = p.x middle + 4
      · exact private_deep l p hl hM ha hi hfour (by omega)
      · exact private_near_background l p hl hM ha hi ⟨by omega, by omega⟩ hfour (Or.inr rfl) (by omega)
    | east =>
      simp only [Adjacent] at hadj hab
      have hay := congrArg Fin.val hadj.2
      have hby := congrArg Fin.val hab.2
      right
      apply private_bottom l p hl hM ha hi (Or.inl ?_) (by omega)
      have hout : ¬(p.x middle + 1 ≤ a.1.val ∧ a.1.val ≤ p.x middle + 4) :=
        fun h => ha_out (Or.inr ⟨hay.symm.trans hbranch.1, h⟩)
      omega
    | west =>
      simp only [Adjacent] at hadj hab
      have hay := congrArg Fin.val hadj.2
      left
      apply private_bottom l p hl hM ha hi (Or.inr ?_) (hay.symm.trans hbranch.1)
      have hout : ¬(p.x middle + 1 ≤ a.1.val ∧ a.1.val ≤ p.x middle + 4) :=
        fun h => ha_out (Or.inr ⟨hay.symm.trans hbranch.1, h⟩)
      omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every successful actual play leaves the five-cell private gate walk empty at every prefix. -/
theorem physicalInstance_gate_privateWalk_empty {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : gatePrivateWalk p middle ⊆ holes u := by
  have hr := l.physicalInstance_gate_private_avoiding_prefix p hl hM ha initial target hi hsu hut ht
  apply (l.gatePrivateWalk_emptyBoundary p hl hM ha hi).reachable_holes
    (gate_frame_preserving l p hl hM ha initial target hr hut ht)
  change gatePrivateWalk p middle ⊆
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ
  rw [compl_compl]
  exact l.gatePrivateWalk_subset_encoded p initial hi

end Solution
end PushPuzzle.PushS.PortLayout
