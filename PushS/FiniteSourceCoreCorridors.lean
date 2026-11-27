/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateSweepFrames
public import PushS.FiniteGatePreparedPhases

public import PushS.FiniteGeometrySimp

/-! The real core's exposed corridors remain free for every prepared local stock. -/

public section
namespace PushPuzzle.PushS.FiniteGateActiveRegion

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools FiniteGateCore
open FiniteGateMacros FiniteGateFaceGeometry FiniteGateOuterAccess

attribute [local irreducible] FiniteGeometry.side

attribute [local finite_gate_access_coords]
  SafeBounds Envelope minX maxX minY coordinates node nodePoint Corridor.start Corridor.finish leftX rightX column upperDepth origin

/-- Both actual core-side corridors lie strictly within the common selected-core region. -/
private theorem strip_safe (w : ℕ) (hw : 2 ≤ w) (kind side : Bool) (selected : Fin 3)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (hp : p ∈ if side then leftStrip w kind else rightStrip w kind) :
    SafeBounds w kind selected (coordinates p) := by
  cases side <;> cases kind <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,mem_leftStrip,mem_rightStrip] at hp
  all_goals dsimp [SafeBounds,Envelope,minX,maxX,minY,coordinates,leftX,rightX,column,upperDepth,origin] at *; omega

/-- All four literal exterior rectangles remain strictly inside the actual core active region. -/
private theorem corridor_safe (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (selected : Fin 3) (k : Corridor)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ k.active w kind) :
    SafeBounds w kind selected (coordinates p) := by
  obtain ⟨hx,hx',hy,hy'⟩ := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
  cases kind <;> cases k <;>
    dsimp [finite_gate_access_coords] at * <;> omega

end PushPuzzle.PushS.FiniteGateActiveRegion

namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateFaceGeometry FiniteGateOuterAccess
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

private theorem and_mixed_floor (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) :
    Disjoint (andMixedBoxes w X) (andWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact andMixedCell_floor w hw X l

private theorem or_mixed_floor (w : ℕ) (hw : 2 ≤ w) (X : OrPhases w) :
    Disjoint (orMixedBoxes w X) (orWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  cases l <;> exact orCell_not_wall w hw _ _ _ _

/-- Any clear literal core footprint carries its complete mixed inventory onto the real board. -/
theorem and_mixed_frame (hg : c.gate.core.isAND = true) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : AndPhases w) (active : Finset (Cell (FiniteGeometry.side w) (FiniteGeometry.side w)))
    (hr : ∀ q ∈ active,SafeBounds w true selected (coordinates q))
    (hf : ∀ q ∈ active,Free (andBoard w ∅) (andMixedBoxes w X) q)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame active c.embedding B ((andMixedBoxes w X).map c.embedding.cells ∪
      c.remaining (c.corePhase selected p (tilePhases phase))) := by
  have F : FiniteWireFrame.Frame active (GridIsometry.refl (FiniteGeometry.side w) (FiniteGeometry.side w)).embedding
      (andBoard w ∅) (andMixedBoxes w X) := ⟨fun q hq => (hf q hq).1,fun q hq => (hf q hq).2,and_mixed_floor w hw X⟩
  apply c.and_region_frame hg selected p hloc ha phase fresh hb _ _ _ F
  · intro q hq
    exact region_of_safeBounds w true selected q (hr q hq)
  · intro q hq
    exact and_mixed_image_envelope w hw X _ q hq
  · exact hB

/-- The same actual mixed-stock placement for an OR core. -/
theorem or_mixed_frame (hg : c.gate.core.isAND = false) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : OrPhases w) (active : Finset (Cell (FiniteGeometry.side w) (FiniteGeometry.side w)))
    (hr : ∀ q ∈ active,SafeBounds w false selected (coordinates q))
    (hf : ∀ q ∈ active,Free (orBoard w ∅) (orMixedBoxes w X) q)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame active c.embedding B ((orMixedBoxes w X).map c.embedding.cells ∪
      c.remaining (c.corePhase selected p (tilePhases phase))) := by
  have F : FiniteWireFrame.Frame active (GridIsometry.refl (FiniteGeometry.side w) (FiniteGeometry.side w)).embedding
      (orBoard w ∅) (orMixedBoxes w X) := ⟨fun q hq => (hf q hq).1,fun q hq => (hf q hq).2,or_mixed_floor w hw X⟩
  apply c.or_region_frame hg selected p hloc ha phase fresh hb _ _ _ F
  · intro q hq
    exact region_of_safeBounds w false selected q (hr q hq)
  · intro q hq
    exact or_mixed_image_envelope w hw X _ q hq
  · exact hB

/-- Every actual AND mixed phase has both full corridor frames. -/
theorem and_strip_frame (hg : c.gate.core.isAND = true) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : AndPhases w) (side : Bool) (B : Board (width w v) (height w v))
    (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (if side then leftStrip w true else rightStrip w true) c.embedding B
      ((andMixedBoxes w X).map c.embedding.cells ∪ c.remaining (c.corePhase selected p (tilePhases phase))) := by
  apply c.and_mixed_frame hg selected p hloc ha phase fresh hb X _ (strip_safe w hw true side selected) _ B hB
  intro q hq
  cases side
  · exact and_right_free w hw X ∅ q hq
  · exact and_left_free w hw X ∅ q hq

/-- Every actual OR mixed phase has both full corridor frames. -/
theorem or_strip_frame (hg : c.gate.core.isAND = false) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : OrPhases w) (side : Bool) (B : Board (width w v) (height w v))
    (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (if side then leftStrip w false else rightStrip w false) c.embedding B
      ((orMixedBoxes w X).map c.embedding.cells ∪ c.remaining (c.corePhase selected p (tilePhases phase))) := by
  apply c.or_mixed_frame hg selected p hloc ha phase fresh hb X _ (strip_safe w hw false side selected) _ B hB
  intro q hq
  cases side
  · exact or_right_free w hw X ∅ q hq
  · exact or_left_free w hw X ∅ q hq

/-- Every prepared AND phase preserves all four real exterior corridors. -/
theorem and_corridor_frame (hg : c.gate.core.isAND = true) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : AndPhases w) (k : Corridor) (B : Board (width w v) (height w v))
    (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (k.active w true) c.embedding B
      ((andMixedBoxes w X).map c.embedding.cells ∪ c.remaining (c.corePhase selected p (tilePhases phase))) := by
  exact c.and_mixed_frame hg selected p hloc ha phase fresh hb X _ (corridor_safe w hw true selected k)
    (Corridor.and_free w hw X k ∅) B hB

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
