/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceFixedHoles
public import PushS.PortGateAxis
public import PushS.PortGateRail
public import PushS.PortWireRail

/-! The actual finite family of principal axes and placement rails. -/

public section
namespace PushPuzzle.Push.AcceptanceSignalRegions

open PushFS PushS PushS.PortLayout

/-- One principal axis or one distinct actual placement. -/
@[expose] noncomputable def RegionIndex (l : PortLayout) : Type := by
  classical
  exact Fin l.portCount ⊕ ↥((placements l).toFinset)

noncomputable instance (l : PortLayout) : Fintype (RegionIndex l) := inferInstanceAs (Fintype (_ ⊕ _))
noncomputable instance (l : PortLayout) : DecidableEq (RegionIndex l) := Classical.decEq _

/-- The open vertical segment belonging to an actual numbered axis. -/
@[expose] def axisRegion (l : PortLayout) (p : Scales.Parameters) (i : Fin l.portCount) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  if i.val ∈ l.gateCenterCoordinates then gateAxis p i.val else ordinaryAxis p i.val

/-- The open horizontal segment belonging to an actual placement. -/
@[expose] def railRegion (p : Scales.Parameters) (g : Placement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  match g.gate with
  | none => wireOpenRail p g
  | some _ => gateOpenRail p g

/-- The literal physical region indexed by the actual source layout. -/
@[expose] def region (l : PortLayout) (p : Scales.Parameters) :
    RegionIndex l → Finset (Cell (p.W + 1) (p.H + 1))
  | .inl i => axisRegion l p i
  | .inr g => railRegion p g.val

/-- All literal fixed holes of the same physical layout. -/
@[expose] def fixedHoles (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p)

/-- The fixed stock and the actual holes in each signal region. -/
@[expose] def family (l : PortLayout) (p : Scales.Parameters)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) :
    Option (RegionIndex l) → Finset (Cell (p.W + 1) (p.H + 1))
  | none => fixedHoles l p
  | some i => E ∩ region l p i

end PushPuzzle.Push.AcceptanceSignalRegions
