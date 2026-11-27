/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteToolMacros
public import PushS.FiniteWireFrame
import Mathlib.Tactic.FinCases

/-! Parity propagation with the shared right interface already high. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

/-- Actual floor used by the parity macro and its fixed real neighboring boxes. -/
def parityActive (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.filter fun p => radius w-2 ≤ p.1.val ∧ p.1.val ≤ radius w+paritySpan w+5 ∧
    radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ radius w ∧ p ∉ parityWalls w

def parityMacroBoard (w : ℕ) : Board (side w) (side w) :=
  FiniteWireFrame.board (parityActive w) ∅

private theorem parityCell_active (w : ℕ) (q : Bool) (l : ParityLabel) :
    parityCell w q l ∈ parityActive w := by
  have hq := Bool.toNat_le q
  have hm := paritySpan_bounds w
  simp only [parityActive, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, parityCell_not_wall w q l⟩
  all_goals cases l <;> dsimp [parityCell, parityPoint, radius] <;> omega

private theorem parityMixed_active (w : ℕ) (a b : Bool) :
    Disjoint (parityMixedBoxes w a b) (parityMacroBoard w).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  apply (FiniteWireFrame.floor_iff _ _ _).mpr
  cases l <;> exact parityCell_active w _ _

private theorem parityRoute_active (w : ℕ) (i : Fin 6) : parityRoute w i ∈ parityActive w := by
  have hm := paritySpan_bounds w
  simp only [parityActive, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, parityRoute_not_wall w i⟩
  all_goals fin_cases i <;> simp [parityRoute, radius] <;> omega

private theorem parityBackwardRoute_active (w : ℕ) (i : Fin 6) :
    parityBackwardRoute w i ∈ parityActive w := by
  have hm := paritySpan_bounds w
  simp only [parityActive, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, parityBackwardRoute_not_wall w i⟩
  all_goals fin_cases i <;> simp [parityBackwardRoute, radius] <;> omega

private theorem parity_support_empty (w : ℕ) (q : Bool) :
    (if q then parityBackwardRoute w 0 else parityRoute w 4) ∉ parityMixedBoxes w q true := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hm := paritySpan_bounds w
  cases q <;> cases l <;>
    simp [parityMixedCell, parityCell, parityPoint, parityRoute, parityBackwardRoute, radius] at hx <;> omega

private theorem parity_destination_empty (w : ℕ) (q : Bool) :
    parityCell w (!q) .left ∉ parityMixedBoxes w q true := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hm := paritySpan_bounds w
  cases q <;> cases l <;>
    simp [parityMixedCell, parityCell, parityPoint, radius] at hx <;> omega

/-- Move exactly D, retaining the already-high E and both exterior boxes. -/
private theorem parity_owned_push (w : ℕ) (q : Bool) :
    Move (parityMacroBoard w) (some 1) (if q then .west else .east)
      ⟨if q then parityBackwardRoute w 0 else parityRoute w 4, parityMixedBoxes w q true⟩
      ⟨parityCell w q .left, parityMixedBoxes w (!q) true⟩ := by
  apply FiniteWireFrame.push_named (parityMixedCell w q true) (parityMixedCell w (!q) true)
    (parityMixedCell_injective w q true) .left
  · intro l hl
    cases l <;> first | rfl | exact False.elim (hl rfl)
  · refine ⟨?_, parityMixed_active w q true, parity_support_empty w q⟩
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    cases q
    · exact parityRoute_active w 4
    · exact parityBackwardRoute_active w 0
  · cases q <;> simp [Adjacent, parityMixedCell, parityRoute, parityBackwardRoute, parityCell, parityPoint,
      Nat.add_assoc, radius]
  · cases q <;> simp [Adjacent, parityMixedCell, parityCell, parityPoint]
  · exact (FiniteWireFrame.floor_iff _ _ _).mpr (parityCell_active w (!q) .left)
  · exact parity_destination_empty w q

private theorem parity_active_walk_free (w : ℕ) (p : Cell (side w) (side w))
    (hx : radius w-1 ≤ p.1.val) (hx' : p.1.val ≤ radius w+paritySpan w+4)
    (hy : radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ radius w)
    (hside : p.1.val = radius w+paritySpan w+2 ∨ p.1.val = radius w-1 ∨
      p.2.val < radius w-w ∨ p.1.val = radius w+1 ∨
      p.1.val = radius w+paritySpan w+4) :
    Free (parityMacroBoard w) (parityMixedBoxes w false true) p := by
  have hf := parity_roof_walk_free w p hy' hside
  refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, hf.2⟩
  simp only [parityActive, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by omega, by omega, hy, hy', hf.1⟩

/-- The shared E has already moved; the parity atom walks around the roof and updates only D. -/
private theorem parity_forward_owned (w : ℕ) :
    Reachable (parityMacroBoard w) (some 1)
      ⟨parityRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityRoute w 5, parityBoxes w true⟩ := by
  have hr : w+1 < radius w := by unfold radius; omega
  have hd := parityMixed_active w false true
  have h12 : Reachable (parityMacroBoard w) (some 1)
      ⟨parityRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityRoute w 2, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_active_walk_free w
    all_goals simp at hy hy' ⊢
    all_goals omega
  have h23 : Reachable (parityMacroBoard w) (some 1)
      ⟨parityRoute w 2, parityMixedBoxes w false true⟩
      ⟨parityRoute w 3, parityMixedBoxes w false true⟩ := by
    apply walk_horizontal hd
    intro x hx hx'
    apply parity_active_walk_free w
    all_goals simp at hx hx' ⊢
    all_goals omega
  have h34 : Reachable (parityMacroBoard w) (some 1)
      ⟨parityRoute w 3, parityMixedBoxes w false true⟩
      ⟨parityRoute w 4, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_active_walk_free w
    all_goals simp at hy hy' ⊢
    all_goals omega
  exact (h12.trans (h23.trans h34)).tail ⟨.east, parity_owned_push w false⟩

private theorem parity_backward_owned (w : ℕ) :
    Reachable (parityMacroBoard w) (some 1)
      ⟨parityBackwardRoute w 0, parityBoxes w true⟩
      ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩ :=
  .single ⟨.west, parity_owned_push w true⟩

theorem parity_forward_owned_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (parityActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨parityRoute w 1, parityMixedBoxes w false true⟩)
      (e.extend fixed ⟨parityRoute w 5, parityBoxes w true⟩) :=
  frame.replay (parity_forward_owned w)

theorem parity_backward_owned_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (parityActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨parityBackwardRoute w 0, parityBoxes w true⟩)
      (e.extend fixed ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩) :=
  frame.replay (parity_backward_owned w)

private theorem parity_right_support_empty (w : ℕ) (q : Bool) :
    (if q then parityBackwardRoute w 4 else parityRoute w 0) ∉ parityMixedBoxes w false q := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hm := paritySpan_bounds w
  cases q <;> cases l <;>
    simp [parityMixedCell, parityCell, parityPoint, parityRoute, parityBackwardRoute, radius] at hx <;> omega

private theorem parity_right_destination_empty_active (w : ℕ) (q : Bool) :
    parityCell w (!q) .right ∉ parityMixedBoxes w false q := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hm := paritySpan_bounds w
  cases q <;> cases l <;> simp [parityMixedCell, parityCell, parityPoint, radius] at hx <;> omega

/-- The right interface moves from its actual tunnel support, with the left box low. -/
private theorem parity_right_active_push (w : ℕ) (q : Bool) :
    Move (parityMacroBoard w) (some 1) (if q then .west else .east)
      ⟨if q then parityBackwardRoute w 4 else parityRoute w 0, parityMixedBoxes w false q⟩
      ⟨parityCell w q .right, parityMixedBoxes w false (!q)⟩ := by
  apply FiniteWireFrame.push_named (parityMixedCell w false q) (parityMixedCell w false (!q))
    (parityMixedCell_injective w false q) .right
  · intro l hl
    cases l <;> first | rfl | exact False.elim (hl rfl)
  · refine ⟨?_, parityMixed_active w false q, parity_right_support_empty w q⟩
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    cases q
    · exact parityRoute_active w 0
    · exact parityBackwardRoute_active w 4
  · cases q <;> simp [Adjacent, parityMixedCell, parityRoute, parityBackwardRoute, parityCell, parityPoint,
      Nat.add_assoc]
  · cases q <;> simp [Adjacent, parityMixedCell, parityCell, parityPoint, Nat.add_assoc]
  · exact (FiniteWireFrame.floor_iff _ _ _).mpr (parityCell_active w (!q) .right)
  · exact parity_right_destination_empty_active w q

theorem parity_forward_active (w : ℕ) :
    Reachable (parityMacroBoard w) (some 1)
      ⟨parityRoute w 0, parityBoxes w false⟩ ⟨parityRoute w 5, parityBoxes w true⟩ :=
  (Relation.ReflTransGen.single ⟨.east, parity_right_active_push w false⟩).trans
    (parity_forward_owned w)

private theorem parity_backward_active_walk (w : ℕ) :
    Reachable (parityMacroBoard w) (some 1)
      ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 4, parityMixedBoxes w false true⟩ := by
  have hr : w+1 < radius w := by unfold radius; omega
  have hd := parityMixed_active w false true
  have h12 : Reachable (parityMacroBoard w) (some 1)
      ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 2, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_active_walk_free w
    all_goals simp at hy hy' ⊢
    all_goals omega
  have h23 : Reachable (parityMacroBoard w) (some 1)
      ⟨parityBackwardRoute w 2, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 3, parityMixedBoxes w false true⟩ := by
    apply walk_horizontal hd
    intro x hx hx'
    apply parity_active_walk_free w
    all_goals simp at hx hx' ⊢
    all_goals omega
  have h34 : Reachable (parityMacroBoard w) (some 1)
      ⟨parityBackwardRoute w 3, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 4, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_active_walk_free w
    all_goals simp at hy hy' ⊢
    all_goals omega
  exact h12.trans (h23.trans h34)

theorem parity_backward_active (w : ℕ) :
    Reachable (parityMacroBoard w) (some 1)
      ⟨parityBackwardRoute w 0, parityBoxes w true⟩
      ⟨parityBackwardRoute w 5, parityBoxes w false⟩ :=
  (parity_backward_owned w).trans ((parity_backward_active_walk w).tail
    ⟨.west, parity_right_active_push w true⟩)

theorem parity_forward_active_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (parityActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨parityRoute w 0, parityBoxes w false⟩)
      (e.extend fixed ⟨parityRoute w 5, parityBoxes w true⟩) :=
  frame.replay (parity_forward_active w)

theorem parity_backward_active_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (parityActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨parityBackwardRoute w 0, parityBoxes w true⟩)
      (e.extend fixed ⟨parityBackwardRoute w 5, parityBoxes w false⟩) :=
  frame.replay (parity_backward_active w)

end PushPuzzle.PushS.FiniteTools
