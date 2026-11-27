/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreFrames
public import PushS.FiniteGateRegionBounds
public import PushS.FiniteSweepLocalFrames

/-! All actual B/C branches and the OR A branch have complete global straight-sweep frames. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteSquareLine FiniteLineMacros FiniteGateActiveRegion FiniteGateCore
open FiniteGateVertical FiniteGateOutputs FiniteGateInputs FiniteGateBranchSweeps
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- The common dependent contract for placing one gate kind's local frame on its actual board. -/
@[expose] def FramePlacement {n m : ℕ} (kind : Bool) : Prop :=
    ∀ (selected : Fin 3) (p : PathSite w hw v (armSpec w c.gate selected))
    (_hloc : p.location = ((codes w v).get c.index).1) (_ha : (inventory w hw v).Admissible)
    (phase : GridRouting.Point → Bool) (_fresh : phase p.location = false)
    (_hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (active : Finset (Cell n m)) (a : GridEmbedding n m (FiniteGeometry.side w) (FiniteGeometry.side w))
    (fixed : Finset (Cell (FiniteGeometry.side w) (FiniteGeometry.side w)))
    (_F : FiniteWireFrame.Frame active a (if kind then andBoard w ∅ else orBoard w ∅) fixed)
    (_hr : ∀ q ∈ active,Region w kind selected (a.cells q))
    (_hf : ∀ q ∈ fixed,Envelope w kind (coordinates q))
    (B : Board (width w v) (height w v)) (_hB : B.walls = (inventory w hw v).walls),
    FiniteWireFrame.Frame active (a.trans c.embedding) B
      (fixed.map c.embedding.cells ∪ c.remaining (c.corePhase selected p (tilePhases phase)))

private theorem kind_region_frame {n m : ℕ} (kind : Bool) (hg : c.gate.core.isAND = kind) :
    c.FramePlacement (n:=n) (m:=m) kind := by
  intro selected p hloc ha phase fresh hb active a fixed F hr hf B hB
  apply c.region_frame selected p hloc ha phase fresh hb active a _ fixed (by rw [hg]; cases kind <;> rfl) F
  · simpa only [hg] using hr
  · simpa only [hg] using hf
  · exact hB

/-- Place a literal AND frame in the selected actual core region. -/
theorem and_region_frame {n m : ℕ} (hg : c.gate.core.isAND = true) :
    c.FramePlacement (n:=n) (m:=m) true := c.kind_region_frame true hg

/-- Place a literal OR frame in the selected actual core region. -/
theorem or_region_frame {n m : ℕ} (hg : c.gate.core.isAND = false) :
    c.FramePlacement (n:=n) (m:=m) false := c.kind_region_frame false hg

/-- The complete actual branch stock sweep has its literal global frame. -/
theorem and_B_sweep_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (andBSweep w).active c.embedding B
      ((andBFixed w a d).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  have L := andBFrame w hw a d ∅
  have F : (andBSweep w).Frame (andBoard w ∅) (andBFixed w a d) :=
    ⟨L.fixed_floor,L.track_free,L.lane_free⟩
  apply c.and_region_frame hg 1 p hloc ha phase fresh hb _ _ _ F.toWireFrame
  · intro q hq
    exact region_of_safeBounds w true 1 q (and_b_sweep_safe w hw q hq)
  · intro q hq
    exact and_normal_image_envelope w hw a false d _ q hq
  · exact hB

/-- The complete actual branch stock sweep has its literal global frame. -/
theorem or_B_sweep_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 1)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 1).target = !(armSpec w c.gate 1).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (orBSweep w).active c.embedding B
      ((orBFixed w a d).map c.embedding.cells ∪ c.remaining (c.corePhase 1 p (tilePhases phase))) := by
  have L := orBFrame w hw a d ∅
  have F : (orBSweep w).Frame (orBoard w ∅) (orBFixed w a d) :=
    ⟨L.fixed_floor,L.track_free,L.lane_free⟩
  apply c.or_region_frame hg 1 p hloc ha phase fresh hb _ _ _ F.toWireFrame
  · intro q hq
    exact region_of_safeBounds w false 1 q (or_b_sweep_safe w hw q hq)
  · intro q hq
    exact or_normal_image_envelope w hw a false d _ q hq
  · exact hB

/-- The complete actual branch stock sweep has its literal global frame. -/
theorem and_C_sweep_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 2)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 2).target = !(armSpec w c.gate 2).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (andOutputSweep w).active c.embedding B
      ((andOutputFixed w a d).map c.embedding.cells ∪ c.remaining (c.corePhase 2 p (tilePhases phase))) := by
  have L := andOutputFrame w hw a d ∅
  have F : (andOutputSweep w).Frame (andBoard w ∅) (andOutputFixed w a d) :=
    ⟨L.fixed_floor,L.track_free,L.lane_free⟩
  apply c.and_region_frame hg 2 p hloc ha phase fresh hb _ _ _ F.toWireFrame
  · intro q hq
    exact region_of_safeBounds w true 2 q (and_c_sweep_safe w hw q hq)
  · intro q hq
    exact and_normal_image_envelope w hw a d true _ q hq
  · exact hB

/-- The complete actual branch stock sweep has its literal global frame. -/
theorem or_C_sweep_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 2)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 2).target = !(armSpec w c.gate 2).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (orOutputSweep w).active c.embedding B
      ((orOutputFixed w a d).map c.embedding.cells ∪ c.remaining (c.corePhase 2 p (tilePhases phase))) := by
  have L := orOutputFrame w hw a d ∅
  have F : (orOutputSweep w).Frame (orBoard w ∅) (orOutputFixed w a d) :=
    ⟨L.fixed_floor,L.track_free,L.lane_free⟩
  apply c.or_region_frame hg 2 p hloc ha phase fresh hb _ _ _ F.toWireFrame
  · intro q hq
    exact region_of_safeBounds w false 2 q (or_c_sweep_safe w hw q hq)
  · intro q hq
    exact or_normal_image_envelope w hw a d true _ q hq
  · exact hB

/-- The complete actual branch stock sweep has its literal global frame. -/
theorem or_A_sweep_frame (hg : c.gate.core.isAND = false)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (a d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (orInputSweep w).active c.embedding B
      ((orInputFixed w a d).map c.embedding.cells ∪ c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  have L := orInputFrame w hw a d ∅
  have F : (orInputSweep w).Frame (orBoard w ∅) (orInputFixed w a d) :=
    ⟨L.fixed_floor,L.track_free,L.lane_free⟩
  apply c.or_region_frame hg 0 p hloc ha phase fresh hb _ _ _ F.toWireFrame
  · intro q hq
    exact region_of_safeBounds w false 0 q (or_a_sweep_safe w hw q hq)
  · intro q hq
    exact or_normal_image_envelope w hw false a d _ q hq
  · exact hB

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
