/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAtomLocalFrames

/-! Literal normal-stock frames for the B and C triggers and the OR A trigger. -/

public section
namespace PushPuzzle.PushS.FiniteGateNormalAtomFrames

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateState
open FiniteGateActiveRegion FiniteGateAtomLocalFrames
open scoped Classical

attribute [local irreducible] FiniteGeometry.side
-- The trigger checks normalize the nested finite-coordinate casts.
set_option maxRecDepth 8192

/-- The B release occupies its three column cells and the adjacent two-cell left lane. -/
@[expose] def BBackwardShape (w col : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.1.val = origin w+col ∧ p.2.val+1 ≤ origin w ∧ origin w ≤ p.2.val+3) ∨
    (p.1.val+1 = origin w+col ∧ p.2.val+2 ≤ origin w ∧ origin w ≤ p.2.val+3)

theorem b_backward_shape (w col : ℕ) (hc : 3 ≤ col ∧ col ≤ 4)
    (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateBAmbient.backwardActive w col hc) :
    BBackwardShape w col p := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  simp only [FiniteGateBAmbient.downLocalActive,parallel_active_iff,point,Prod.ext_iff,Fin.ext_iff] at hq
  dsimp [BBackwardShape,GridIsometry.transpose,GridIsometry.embedding] at *
  unfold origin at *
  omega

theorem and_B_backward_frame (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 3 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅)
      ((andBoxes w a true c).erase (point w 3 2)) := by
  apply image_erase_frame (andCell w a true c) (point w 3 2)
    (FiniteGateBAmbient.backwardActive w 3 (by omega)) (andBoard w ∅)
    (andBoxes_disjoint_walls w hw a true c)
  · intro p hp
    have hs := b_backward_shape w 3 (by omega) p hp
    apply and_core_floor w hw p
    all_goals dsimp [BBackwardShape] at hs; omega
  · intro l hl
    have hs := b_backward_shape w 3 (by omega) _ hl
    have ha := Bool.toNat_le a
    have hc := Bool.toNat_le c
    cases l <;> simp [BBackwardShape,andCell,andPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

theorem or_B_backward_frame (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 4 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅)
      ((orBoxes w a true c).erase (point w 4 2)) := by
  apply image_erase_frame (orCell w a true c) (point w 4 2)
    (FiniteGateBAmbient.backwardActive w 4 (by omega)) (orBoard w ∅)
    (orBoxes_disjoint_walls w hw a true c)
  · intro p hp
    have hs := b_backward_shape w 4 (by omega) p hp
    apply or_core_floor w hw p
    all_goals dsimp [BBackwardShape] at hs; omega
  · intro l hl
    have hs := b_backward_shape w 4 (by omega) _ hl
    have ha := Bool.toNat_le a
    have hc := Bool.toNat_le c
    cases l <;> simp [BBackwardShape,orCell,orPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢
    omega

/-- The B lift occupies only the three cells of its column. -/
@[expose] def BRaiseShape (w col : ℕ) (p : Cell (side w) (side w)) : Prop :=
  p.1.val = origin w+col ∧ p.2.val ≤ origin w ∧ origin w ≤ p.2.val+2

theorem b_raise_shape (w col : ℕ) (hc : col ≤ 4) (p : Cell (side w) (side w))
    (hp : p ∈ FiniteGateBAmbient.raiseActive w col hc) : BRaiseShape w col p := by
  simp only [FiniteGateBAmbient.raiseActive,FiniteAtomFrames.pushActive,Finset.mem_insert,Finset.mem_singleton,point,Prod.ext_iff,Fin.ext_iff] at hp
  dsimp [BRaiseShape]
  unfold origin at *
  omega

theorem and_B_raise_frame (w : ℕ) (hw : 2 ≤ w) (c : Bool) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅)
      ((andBoxes w true true c).erase (point w 3 2)) := by
  apply image_erase_frame (andCell w true true c) (point w 3 2)
    (FiniteGateBAmbient.raiseActive w 3 (by omega)) (andBoard w ∅)
    (andBoxes_disjoint_walls w hw true true c)
  · intro p hp
    have hs := b_raise_shape w 3 (by omega) p hp
    apply and_core_floor w hw p
    all_goals dsimp [BRaiseShape] at hs; omega
  · intro l hl
    have hs := b_raise_shape w 3 (by omega) _ hl
    have hc := Bool.toNat_le c
    cases l <;> simp [BRaiseShape,andCell,andPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

theorem or_B_raise_frame (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 4 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅)
      ((orBoxes w a true c).erase (point w 4 2)) := by
  apply image_erase_frame (orCell w a true c) (point w 4 2)
    (FiniteGateBAmbient.raiseActive w 4 (by omega)) (orBoard w ∅)
    (orBoxes_disjoint_walls w hw a true c)
  · intro p hp
    have hs := b_raise_shape w 4 (by omega) p hp
    apply or_core_floor w hw p
    all_goals dsimp [BRaiseShape] at hs; omega
  · intro l hl
    have hs := b_raise_shape w 4 (by omega) _ hl
    have ha := Bool.toNat_le a
    have hc := Bool.toNat_le c
    cases l <;> simp [BRaiseShape,orCell,orPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

/-- The C trigger uses its three row cells and its two-cell upper lane. -/
@[expose] def CForwardShape (w shift : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.2.val = origin w ∧ origin w+w+shift-2 ≤ p.1.val ∧ p.1.val ≤ origin w+w+shift) ∨
    (p.2.val+1 = origin w ∧ origin w+w+shift-1 ≤ p.1.val ∧ p.1.val ≤ origin w+w+shift)

theorem c_forward_shape (w shift : ℕ) (hs : 6 ≤ shift ∧ shift ≤ 7)
    (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateCAmbient.forwardActive w shift hs) :
    CForwardShape w shift p := by
  simp only [FiniteGateCAmbient.forwardActive,parallel_active_iff,point,Prod.ext_iff,Fin.ext_iff] at hp
  dsimp [CForwardShape]
  unfold origin at *
  omega

theorem and_C_forward_frame (w : ℕ) (hw : 2 ≤ w) (a b : Bool) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 6 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅)
      ((andBoxes w a b false).erase (point w (w+5) 0)) := by
  apply image_erase_frame (andCell w a b false) (point w (w+5) 0)
    (FiniteGateCAmbient.forwardActive w 6 (by omega)) (andBoard w ∅)
    (andBoxes_disjoint_walls w hw a b false)
  · intro p hp
    have hs := c_forward_shape w 6 (by omega) p hp
    apply and_core_floor w hw p
    all_goals dsimp [CForwardShape] at hs; unfold origin at *; omega
  · intro l hl
    have hs := c_forward_shape w 6 (by omega) _ hl
    have ha := Bool.toNat_le a
    have hb := Bool.toNat_le b
    cases l <;> simp [CForwardShape,andCell,andPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

theorem or_C_forward_frame (w : ℕ) (hw : 2 ≤ w) (a b : Bool) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 7 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅)
      ((orBoxes w a b false).erase (point w (w+6) 0)) := by
  apply image_erase_frame (orCell w a b false) (point w (w+6) 0)
    (FiniteGateCAmbient.forwardActive w 7 (by omega)) (orBoard w ∅)
    (orBoxes_disjoint_walls w hw a b false)
  · intro p hp
    have hs := c_forward_shape w 7 (by omega) p hp
    apply or_core_floor w hw p
    all_goals dsimp [CForwardShape] at hs; unfold origin at *; omega
  · intro l hl
    have hs := c_forward_shape w 7 (by omega) _ hl
    have ha := Bool.toNat_le a
    have hb := Bool.toNat_le b
    cases l <;> simp [CForwardShape,orCell,orPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

/-- The released C trigger's row interval and its single upper mouth cell. -/
@[expose] def CBackwardShape (w mouth shift : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.2.val = origin w ∧ origin w+mouth ≤ p.1.val ∧ p.1.val ≤ origin w+w+shift-1) ∨
    (p.2.val+1 = origin w ∧ p.1.val = origin w+mouth)

theorem c_backward_shape (w mouth shift : ℕ) (hm : mouth ≤ 4) (hs : 6 ≤ shift ∧ shift ≤ 7)
    (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateCAmbient.backwardActive w mouth shift hm hs) :
    CBackwardShape w mouth shift p := by
  simp only [FiniteGateCAmbient.backwardActive,FiniteMouthFrames.mem_rightActive,point,Prod.ext_iff,Fin.ext_iff] at hp
  dsimp [CBackwardShape]
  unfold origin at *
  omega

theorem and_C_backward_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 3 6 (by omega) (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅)
      ((andBoxes w true true false).erase (point w (w+5) 0)) := by
  apply image_erase_frame (andCell w true true false) (point w (w+5) 0)
    (FiniteGateCAmbient.backwardActive w 3 6 (by omega) (by omega)) (andBoard w ∅)
    (andBoxes_disjoint_walls w hw true true false)
  · intro p hp
    have hs := c_backward_shape w 3 6 (by omega) (by omega) p hp
    apply and_core_floor w hw p
    all_goals dsimp [CBackwardShape] at hs; unfold origin at *; omega
  · intro l hl
    have hs := c_backward_shape w 3 6 (by omega) (by omega) _ hl
    apply Prod.ext <;> apply Fin.ext
    all_goals cases l <;> dsimp [CBackwardShape,andCell,andPoint,point,origin] at hs ⊢ <;> omega

theorem or_C_backward_frame (w : ℕ) (hw : 2 ≤ w) (a b : Bool) (mouth : ℕ)
    (hm : mouth ≤ 4) (hA : 3 < mouth+a.toNat) (hB : mouth ≠ 4 ∨ b = true) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w mouth 7 hm (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅)
      ((orBoxes w a b false).erase (point w (w+6) 0)) := by
  apply image_erase_frame (orCell w a b false) (point w (w+6) 0)
    (FiniteGateCAmbient.backwardActive w mouth 7 hm (by omega)) (orBoard w ∅)
    (orBoxes_disjoint_walls w hw a b false)
  · intro p hp
    have hs := c_backward_shape w mouth 7 hm (by omega) p hp
    apply or_core_floor w hw p
    all_goals dsimp [CBackwardShape] at hs; unfold origin at *; omega
  · intro l hl
    have hs := c_backward_shape w mouth 7 hm (by omega) _ hl
    have ha := Bool.toNat_le a
    have hb := Bool.toNat_le b
    have hB' : mouth ≠ 4 ∨ b.toNat = 1 := hB.imp id (fun h => by simp [h])
    apply Prod.ext <;> apply Fin.ext
    all_goals cases l <;> dsimp [CBackwardShape,orCell,orPoint,point,origin] at hs ⊢ <;> omega

theorem or_A_backward_frame (w : ℕ) (hw : 2 ≤ w) (b c : Bool) :
    FiniteWireFrame.Frame (FiniteGateOrAAmbient.backwardActive w)
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅)
      ((orBoxes w true b c).erase (point w 2 0)) := by
  apply image_erase_frame (orCell w true b c) (point w 2 0)
    (FiniteGateOrAAmbient.backwardActive w) (orBoard w ∅)
    (orBoxes_disjoint_walls w hw true b c)
  · intro p hp
    have hs := a_backward_shape w p hp
    apply or_core_floor w hw p
    all_goals dsimp [ABackwardShape] at hs; omega
  · intro l hl
    have hs := a_backward_shape w _ hl
    have hb := Bool.toNat_le b
    have hc := Bool.toNat_le c
    cases l <;> simp [ABackwardShape,orCell,orPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

/-- The A contraction's row interval and its chosen upper mouth cell. -/
@[expose] def AForwardMouthShape (w mouth : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.2.val = origin w ∧ origin w+2 ≤ p.1.val ∧ p.1.val ≤ origin w+mouth) ∨
    (p.2.val+1 = origin w ∧ p.1.val = origin w+mouth)

theorem or_a_forward_shape (w mouth : ℕ) (hm : mouth ≤ w+8)
    (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateOrAAmbient.forwardActive w mouth hm) :
    AForwardMouthShape w mouth p := by
  simp only [FiniteGateOrAAmbient.forwardActive,FiniteMouthFrames.mem_leftActive,point,Prod.ext_iff,Fin.ext_iff] at hp
  dsimp [AForwardMouthShape]
  unfold origin at *
  omega

theorem or_A_forward_frame (w : ℕ) (hw : 2 ≤ w) (b c : Bool) (mouth : ℕ)
    (hm : mouth ≤ w+8) (hgap : 4 ≤ mouth) (hopen : mouth ≤ 4 ∨ w+5 ≤ mouth)
    (hB : mouth ≠ 4 ∨ b = true) (hC : mouth+c.toNat < w+6) :
    FiniteWireFrame.Frame (FiniteGateOrAAmbient.forwardActive w mouth hm)
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅)
      ((orBoxes w true b c).erase (point w 2 0)) := by
  apply image_erase_frame (orCell w true b c) (point w 2 0)
    (FiniteGateOrAAmbient.forwardActive w mouth hm) (orBoard w ∅)
    (orBoxes_disjoint_walls w hw true b c)
  · intro p hp
    have hs := or_a_forward_shape w mouth hm p hp
    apply or_core_floor w hw p
    all_goals dsimp [AForwardMouthShape] at hs; unfold origin at *; omega
  · intro l hl
    have hs := or_a_forward_shape w mouth hm _ hl
    have hb := Bool.toNat_le b
    have hc := Bool.toNat_le c
    have hB' : mouth ≠ 4 ∨ b.toNat = 1 := hB.imp id (fun h => by simp [h])
    cases l <;> simp [AForwardMouthShape,orCell,orPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

end PushPuzzle.PushS.FiniteGateNormalAtomFrames
