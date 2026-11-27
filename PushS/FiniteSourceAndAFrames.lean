/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateSweepFrames

/-! The entire protected AND A branch has literal frames on the actual global source board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateAStraight FiniteSquareLine FiniteLineMacros FiniteGateMacros FiniteGateActiveRegion
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side FiniteTools.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

private theorem detour_local_frame (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (k : FiniteGateAApproaches.Detour) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (k.start w) (k.finish w))
      (GridIsometry.refl (FiniteGeometry.side w) (FiniteGeometry.side w)).embedding
      (FiniteGateCore.andBoard w ∅) (andMixedBoxes w X) := by
  apply FiniteWireFrame.Frame.of_free
  · apply Finset.disjoint_left.mpr
    intro p hp hm
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
    exact andMixedCell_floor w hw X l hm
  · intro p hp
    obtain ⟨hx,hx',hy,hy'⟩ := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
    exact k.free w hw X ∅ p hx hx' hy hy'

/-- Four complete straight sweeps, all three shared tools and all four island detours retain every real global box. -/
theorem and_A_frames (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (b d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteGateAAmbient.Frames w b d c.embedding B (c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  constructor
  · intro k
    refine c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (k.frame w hw b d ∅).toWireFrame ?_ ?_ B hB
    · intro q hq
      exact region_of_safeBounds w true 0 q (and_sweep_safe w hw k q hq)
    · intro q hq
      exact and_mixed_image_envelope w hw (stage w b d k.before) _ q hq
  · refine c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (upper_frame w hw (stage w b d 1) ∅) ?_ ?_ B hB
    · intro q hq
      exact region_of_safeBounds w true 0 _ (upper_safe w hw 0 q hq)
    · intro q hq
      exact and_mixed_image_envelope w hw (stage w b d 1) _ q hq
  · refine c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (flip_frame w hw (stage w b d 3) ∅) ?_ ?_ B hB
    · intro q hq
      exact region_of_safeBounds w true 0 _ (flip_safe w hw 0 q hq)
    · intro q hq
      exact and_mixed_image_envelope w hw (stage w b d 3) _ q hq
  · refine c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (protection_frame w hw (stage w b d 5) ∅) ?_ ?_ B hB
    · intro q hq
      exact region_of_safeBounds w true 0 _ (protection_safe w hw 0 q hq)
    · intro q hq
      exact and_mixed_image_envelope w hw (stage w b d 5) _ q hq
  · intro k
    let X := stage w b d (match k with
      | .upperAcross | .upperDown => 3 | .lowerAcross | .lowerUp => 4)
    refine c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (detour_local_frame w hw X k) ?_ ?_ B hB
    · intro q hq
      exact region_of_safeBounds w true 0 q (detour_safe w hw 0 k q hq)
    · intro q hq
      exact and_mixed_image_envelope w hw X _ q hq

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
