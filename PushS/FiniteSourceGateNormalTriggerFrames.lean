/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateTriggerFrames
public import PushS.FiniteGateNormalAtomFrames
public import PushS.FiniteGateCavityStockFrames

/-! The remaining normal trigger and prepared entry frames on the complete real board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateNormalAtomFrames FiniteGateCavityStockFrames
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- The literal and_B_backward_trigger_frame frame retains every actual globally remaining identity. -/
theorem and_B_backward_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 3 (by omega)) c.embedding B
      (((andBoxes w a true d).erase (point w 3 2)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_backward_frame w hw a d)
  · intro q hq
    have hs := b_backward_shape w 3 (by omega) q hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BBackwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw a true d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal and_B_raise_trigger_frame frame retains every actual globally remaining identity. -/
theorem and_B_raise_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega)) c.embedding B
      (((andBoxes w true true d).erase (point w 3 2)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_raise_frame w hw d)
  · intro q hq
    have hs := b_raise_shape w 3 (by omega) q hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BRaiseShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw true true d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal and_C_forward_trigger_frame frame retains every actual globally remaining identity. -/
theorem and_C_forward_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 2)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 2).target = !(armSpec w c.gate 2).initial)
    (a b : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 6 (by omega)) c.embedding B
      (((andBoxes w a b false).erase (point w (w+5) 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 2 p (tilePhases phase))) := by
  apply c.and_region_frame hg 2 p hloc ha phase fresh hb _ _ _ (and_C_forward_frame w hw a b)
  · intro q hq
    have hs := c_forward_shape w 6 (by omega) q hq
    change Region w true 2 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [CForwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw a b false _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal and_B_exit_trigger_frame frame retains every actual globally remaining identity. -/
theorem and_B_exit_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega)) c.embedding B
      ((andBoxes w a true d).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_exit_frame w hw a d)
  · intro q hq
    have hs := b_exit_shape w 3 (by omega) q hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BExitShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw a true d _ q (hq)
  · exact hB

/-- The literal or_B_backward_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_B_backward_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 4 (by omega)) c.embedding B
      (((orBoxes w a true d).erase (point w 4 2)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.or_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (or_B_backward_frame w hw a d)
  · intro q hq
    have hs := b_backward_shape w 4 (by omega) q hq
    change Region w false 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BBackwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw a true d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal or_B_raise_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_B_raise_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 4 (by omega)) c.embedding B
      (((orBoxes w a true d).erase (point w 4 2)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.or_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (or_B_raise_frame w hw a d)
  · intro q hq
    have hs := b_raise_shape w 4 (by omega) q hq
    change Region w false 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BRaiseShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw a true d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal or_C_forward_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_C_forward_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 2)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 2).target = !(armSpec w c.gate 2).initial)
    (a b : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 7 (by omega)) c.embedding B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 2 p (tilePhases phase))) := by
  apply c.or_region_frame hg 2 p hloc ha phase fresh hb _ _ _ (or_C_forward_frame w hw a b)
  · intro q hq
    have hs := c_forward_shape w 7 (by omega) q hq
    change Region w false 2 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [CForwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw a b false _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal or_B_exit_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_B_exit_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 4 (by omega)) c.embedding B
      ((orBoxes w a true d).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.or_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (or_B_exit_frame w hw a d)
  · intro q hq
    have hs := b_exit_shape w 4 (by omega) q hq
    change Region w false 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BExitShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw a true d _ q (hq)
  · exact hB

/-- The literal and_C_backward_trigger_frame frame retains every actual globally remaining identity. -/
theorem and_C_backward_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 2)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 2).target = !(armSpec w c.gate 2).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 3 6 (by omega) (by omega)) c.embedding B
      (((andBoxes w true true false).erase (point w (w+5) 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 2 p (tilePhases phase))) := by
  apply c.and_region_frame hg 2 p hloc ha phase fresh hb _ _ _ (and_C_backward_frame w hw )
  · intro q hq
    have hs := c_backward_shape w 3 6 (by omega) (by omega) q hq
    change Region w true 2 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [CBackwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw true true false _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal or_C_backward_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_C_backward_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 2)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 2).target = !(armSpec w c.gate 2).initial)
    (a b : Bool) (mouth : ℕ) (hm : mouth ≤ 4) (hA : 3 < mouth+a.toNat) (hG : mouth ≠ 4 ∨ b = true) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w mouth 7 hm (by omega)) c.embedding B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 2 p (tilePhases phase))) := by
  apply c.or_region_frame hg 2 p hloc ha phase fresh hb _ _ _ (or_C_backward_frame w hw a b mouth hm hA hG)
  · intro q hq
    have hs := c_backward_shape w mouth 7 hm (by omega) q hq
    change Region w false 2 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [CBackwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw a b false _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal or_A_backward_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_A_backward_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (b d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateOrAAmbient.backwardActive w) c.embedding B
      (((orBoxes w true b d).erase (point w 2 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  apply c.or_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (or_A_backward_frame w hw b d)
  · intro q hq
    have hs := FiniteGateAtomLocalFrames.a_backward_shape w q hq
    change Region w false 0 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [FiniteGateAtomLocalFrames.ABackwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw true b d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The literal or_A_forward_trigger_frame frame retains every actual globally remaining identity. -/
theorem or_A_forward_trigger_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (b d : Bool) (mouth : ℕ) (hm : mouth ≤ w+8) (hgap : 4 ≤ mouth) (hopen : mouth ≤ 4 ∨ w+5 ≤ mouth) (hG : mouth ≠ 4 ∨ b = true) (hC : mouth+d.toNat < w+6) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateOrAAmbient.forwardActive w mouth hm) c.embedding B
      (((orBoxes w true b d).erase (point w 2 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  apply c.or_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (or_A_forward_frame w hw b d mouth hm hgap hopen hG hC)
  · intro q hq
    have hs := or_a_forward_shape w mouth hm q hq
    change Region w false 0 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [AForwardMouthShape] at hs; unfold origin at *; omega
  · intro q hq
    exact or_normal_image_envelope w hw true b d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
