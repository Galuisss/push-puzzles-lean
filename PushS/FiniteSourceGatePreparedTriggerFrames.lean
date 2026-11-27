/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateNormalTriggerFrames
public import PushS.FiniteGateTemporaryAtomFrames
public import PushS.FiniteSourceCoreCorridors

/-! Literal global cavity frames of all prepared and temporary branch stocks. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateNormalAtomFrames FiniteGateCavityStockFrames
open FiniteGateTemporaryAtomFrames FiniteGateVertical FiniteGateBTemporary FiniteGateInputs
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- The real and_B_entry_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem and_B_entry_actual_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w (w+4) 3 (by omega) (by omega)) c.embedding B
      ((andBBoxes w true false true).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_entry_frame w hw )
  · intro q hq
    have hs := b_entry_shape w (w+4) 3 (by omega) (by omega) q hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BEntryShape] at hs; unfold origin at *; omega
  · intro q hq
    rw [←andMixedBoxes_B] at hq
    exact and_mixed_image_envelope w hw _ _ q hq
  · exact hB

/-- The real or_B_entry_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem or_B_entry_actual_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (mouth : ℕ) (hm : mouth ≤ w+8) (hleft : 3 < min mouth 4+a.toNat) (hright : max mouth 4+d.toNat < w+6) (hopen : mouth ≤ 4 ∨ w+5 ≤ mouth) (hne : mouth ≠ 4) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w mouth 4 hm (by omega)) c.embedding B
      ((orBBoxes w a d true).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.or_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (or_B_entry_frame w hw a d mouth hm hleft hright hopen hne)
  · intro q hq
    have hs := b_entry_shape w mouth 4 hm (by omega) q hq
    change Region w false 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BEntryShape] at hs; unfold origin at *; omega
  · intro q hq
    rw [←orMixedBoxes_B] at hq
    exact or_mixed_image_envelope w hw _ _ q hq
  · exact hB

/-- The real and_B_closed_approach_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem and_B_closed_approach_actual_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 2) (point w 2 0)) c.embedding B
      ((andBBoxes w false false true).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_closed_approach_frame w hw )
  · intro q hq
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [point] at hs; unfold origin at *; omega
  · intro q hq
    rw [←andMixedBoxes_B] at hq
    exact and_mixed_image_envelope w hw _ _ q hq
  · exact hB

/-- The real and_B_closed_A_push_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem and_B_closed_A_push_actual_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0)) c.embedding B
      (((andBBoxes w false false true).erase (point w 3 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_closed_A_push_frame w hw )
  · intro q hq
    have hs := hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals simp [FiniteAtomFrames.pushActive,point,Prod.ext_iff,Fin.ext_iff] at hs; unfold origin at *; omega
  · intro q hq
    have hq' := Finset.mem_of_mem_erase hq
    rw [←andMixedBoxes_B] at hq'
    exact and_mixed_image_envelope w hw _ _ q hq'
  · exact hB

/-- The real and_B_temporary_raise_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem and_B_temporary_raise_actual_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega)) c.embedding B
      (((temporaryBoxes w).erase (point w 3 2)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_temporary_raise_frame w hw )
  · intro q hq
    have hs := b_raise_shape w 3 (by omega) q hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BRaiseShape] at hs; unfold origin at *; omega
  · intro q hq
    have hq' := Finset.mem_of_mem_erase hq
    rw [←andMixedBoxes_temporary w hw] at hq'
    exact and_mixed_image_envelope w hw _ _ q hq'
  · exact hB

/-- The real and_B_temporary_exit_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem and_B_temporary_exit_actual_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega)) c.embedding B
      ((temporaryBoxes w).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_temporary_exit_frame w hw )
  · intro q hq
    have hs := b_exit_shape w 3 (by omega) q hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [BExitShape] at hs; unfold origin at *; omega
  · intro q hq
    rw [←andMixedBoxes_temporary w hw] at hq
    exact and_mixed_image_envelope w hw _ _ q hq
  · exact hB

/-- The real and_B_restore_A_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem and_B_restore_A_actual_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
     (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 3 0).1 (point w 0 1).2 (point w 0 0).2) c.embedding B
      (((andBoxes w false true false).erase (point w 3 0)).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (and_B_restore_A_frame w hw )
  · intro q hq
    have hs := hq
    change Region w true 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals simp [FiniteMouthFrames.leftActive,point,Prod.ext_iff,Fin.ext_iff] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw false true false _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The real or_A_open_walk_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem or_A_open_walk_actual_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 1 1) (point w 4 1)) c.embedding B
      ((orInputBoxes w true d true).map c.embedding.cells ∪ c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  apply c.or_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (or_A_open_walk_frame w hw d)
  · intro q hq
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    change Region w false 0 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [point] at hs; unfold origin at *; omega
  · intro q hq
    rw [←orMixedBoxes_input] at hq
    exact or_mixed_image_envelope w hw _ _ q hq
  · exact hB

/-- The real or_B_open_walk_actual_frame uses exactly its prepared local stock and the complete actual remaining inventory. -/
theorem or_B_open_walk_actual_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 3 2) (point w 3 1)) c.embedding B
      ((orBBoxes w true d true).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  apply c.or_region_frame hg 1 p hloc ha phase fresh hb _ _ _ (or_B_open_walk_frame w hw d)
  · intro q hq
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    change Region w false 1 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [point] at hs; unfold origin at *; omega
  · intro q hq
    rw [←orMixedBoxes_B] at hq
    exact or_mixed_image_envelope w hw _ _ q hq
  · exact hB

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
