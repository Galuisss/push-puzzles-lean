/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCavityStockFrames

/-! Every literal cavity footprint of the temporary A double push and the two short OR approaches. -/

public section
namespace PushPuzzle.PushS.FiniteGateTemporaryAtomFrames

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateState FiniteGateTools
open FiniteGateVertical FiniteGateInputs FiniteGateBTriggers FiniteGateBForward FiniteGateBTemporary
open FiniteGateAtomLocalFrames FiniteGateNormalAtomFrames FiniteGateCavityStockFrames
open scoped Classical

attribute [local irreducible] FiniteGeometry.side

theorem and_B_closed_approach_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 2) (point w 2 0))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅) (andBBoxes w false false true) := by
  refine ⟨?_,?_,andBBoxes_floor w hw false false ∅⟩
  all_goals intro p hp
  all_goals have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
  · exact (approach_free w hw ∅ p (by dsimp [point] at hs; omega) (by dsimp [point] at hs; omega)).1
  · exact (approach_free w hw ∅ p (by dsimp [point] at hs; omega) (by dsimp [point] at hs; omega)).2

theorem and_B_closed_A_push_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅)
      ((andBBoxes w false false true).erase (point w 3 0)) := by
  apply image_erase_frame (andBCell w false false true) (point w 3 0)
    (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0)) (andBoard w ∅)
    (andBBoxes_floor w hw false false ∅)
  · intro p hp
    simp only [FiniteAtomFrames.pushActive,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    all_goals apply and_core_floor w hw
    all_goals dsimp [point]; omega
  · intro l hl
    simp only [FiniteAtomFrames.pushActive,Finset.mem_insert,Finset.mem_singleton,point,Prod.ext_iff,Fin.ext_iff] at hl ⊢
    cases l <;> simp [andBCell,andCell,andPoint,origin] at hl ⊢ <;> omega

theorem and_B_temporary_raise_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅)
      ((temporaryBoxes w).erase (point w 3 2)) := by
  rw [←andMixedBoxes_temporary w hw]
  apply image_erase_frame (andMixedCell w (andTemporaryPhases w)) (point w 3 2)
    (FiniteGateBAmbient.raiseActive w 3 (by omega)) (andBoard w ∅)
    (by change Disjoint (andMixedBoxes w (andTemporaryPhases w)) (andBoard w ∅).walls
        rw [andMixedBoxes_temporary w hw]
        exact temporary_floor w hw ∅)
  · intro p hp
    have hs := b_raise_shape w 3 (by omega) p hp
    apply and_core_floor w hw p
    all_goals dsimp [BRaiseShape] at hs; omega
  · intro l hl
    have hs := b_raise_shape w 3 (by omega) _ hl
    apply Prod.ext <;> apply Fin.ext
    all_goals cases l <;> dsimp [BRaiseShape,andMixedCell,andTemporaryPhases,andNormalPhases,andCell,andPoint,point,origin] at hs ⊢ <;> omega

theorem and_B_temporary_exit_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅) (temporaryBoxes w) := by
  have hf (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateBAmbient.exitActive w 3 (by omega)) :
      Free (andBoard w ∅) (temporaryBoxes w) p := by
    have hs := b_exit_shape w 3 (by omega) p hp
    apply free_relocated_of_ne
    · apply and_near_B_free w hw false false ∅ p
      all_goals dsimp [BExitShape] at hs; omega
    · intro he
      have hy := congrArg (fun z => z.2.val) he
      dsimp [BExitShape,point] at hs hy
      unfold origin at *
      omega
  exact ⟨fun p hp => (hf p hp).1,fun p hp => (hf p hp).2,temporary_floor w hw ∅⟩

theorem and_B_restore_A_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 3 0).1
      (point w 0 1).2 (point w 0 0).2) (GridIsometry.refl (side w) (side w)).embedding
      (andBoard w ∅) ((andBoxes w false true false).erase (point w 3 0)) := by
  apply image_erase_frame (andCell w false true false) (point w 3 0) _ (andBoard w ∅)
    (andBoxes_disjoint_walls w hw false true false)
  · intro p hp
    simp only [FiniteMouthFrames.mem_leftActive,point,Prod.ext_iff,Fin.ext_iff] at hp
    apply and_core_floor w hw p
    all_goals unfold origin at *; omega
  · intro l hl
    simp only [FiniteMouthFrames.mem_leftActive,point,Prod.ext_iff,Fin.ext_iff] at hl ⊢
    cases l <;> simp [andCell,andPoint,origin] at hl ⊢ <;> omega

theorem or_A_open_walk_frame (w : ℕ) (hw : 2 ≤ w) (c : Bool) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 1 1) (point w 4 1))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅) (orInputBoxes w true c true) := by
  have hf (p : Cell (side w) (side w)) (hp : p ∈ FiniteAtomFrames.walkActive (point w 1 1) (point w 4 1)) :
      Free (orBoard w ∅) (orInputBoxes w true c true) p := by
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
    constructor
    · apply or_core_floor w hw p
      all_goals dsimp [point] at hs; unfold origin at *; omega
    · intro hm
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hx := congrArg (fun z => z.1.val) he
      have hy := congrArg (fun z => z.2.val) he
      have hc := Bool.toNat_le c
      cases l <;> dsimp [orInputCell,orCell,orPoint,point,origin] at hx hy hs <;> omega
  refine ⟨fun p hp => (hf p hp).1,fun p hp => (hf p hp).2,?_⟩
  rw [←orMixedBoxes_input]
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  cases l <;> exact orCell_not_wall w hw _ _ _ _

theorem or_B_open_walk_frame (w : ℕ) (hw : 2 ≤ w) (c : Bool) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 3 2) (point w 3 1))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅) (orBBoxes w true c true) := by
  have hf (p : Cell (side w) (side w)) (hp : p ∈ FiniteAtomFrames.walkActive (point w 3 2) (point w 3 1)) :
      Free (orBoard w ∅) (orBBoxes w true c true) p := by
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
    apply orBBoxes_free w hw true c ∅
    · constructor
      · apply or_core_floor w hw p
        all_goals dsimp [point] at hs; unfold origin at *; omega
      · intro hm
        obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
        have hx := congrArg (fun z => z.1.val) he
        have hc := Bool.toNat_le c
        cases l <;> dsimp [orCell,orPoint,point,origin] at hx hs <;> omega
    · intro he
      have hx := congrArg (fun z => z.1.val) he
      dsimp [point] at hx hs
      omega
  exact ⟨fun p hp => (hf p hp).1,fun p hp => (hf p hp).2,orBBoxes_floor w hw true c ∅⟩

end PushPuzzle.PushS.FiniteGateTemporaryAtomFrames
