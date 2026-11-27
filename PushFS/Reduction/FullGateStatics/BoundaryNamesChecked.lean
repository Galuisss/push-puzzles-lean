/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Shape

/-! Exact active names at the four outer edges of every complete physical gate. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def OnEdge (p : ℕ×ℕ) : Prop := p.1=0 ∨p.1=200006 ∨p.2=0 ∨p.2=198067
instance (p : ℕ×ℕ) : Decidable (OnEdge p) := by unfold OnEdge; infer_instance

def edgeName (g : GateTileState) (p : ℕ×ℕ) : AxisTrack :=
  if p.2=99034 ∧(p.1=0 ∧FullGateBoundary.Used g .west ∨p.1=200006 ∧FullGateBoundary.Used g .east)
    then .horizontal 99034
  else if p.1=100003 ∧(p.2=0 ∧FullGateBoundary.Used g .north ∨p.2=198067 ∧FullGateBoundary.Used g .south)
    then .vertical 100003
  else .outside

def edgeNamesTest (g : GateTileState) : Bool :=
  (chartIndices g).all fun c=>
    let s:=shape (chart g c)
    s.boundary.all fun u=>
      if s.name u≠.outside ∧OnEdge (s.global u) then
        decide (AxisTrack.shift s.dx s.dy (s.name u)=edgeName g (s.global u))
      else true

private theorem edgeNames_checked : ∀k : Geometry,edgeNamesTest (ofGeometry k)=true := by
  rintro ⟨kind,pattern,rotation,incoming⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals
    rcases incoming with ⟨left, upper, right⟩
    cases left <;> cases upper <;> cases right <;> decide +kernel

theorem edgeNames_all (g : GateTileState) : edgeNamesTest g=true := edgeNames_checked (geometry g)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
