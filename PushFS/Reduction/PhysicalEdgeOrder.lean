/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.UnitPathOrder
public import PushFS.Reduction.ProfileSweep
public import Mathlib.Data.Fin.Rev
public import PushFS.Reduction.PhysicalWallPhases
public import PushFS.Reduction.PhysicalWireSignals
public import PushFS.Reduction.PhysicalGatePlacement
public import PushFS.Reduction.SourceEdgeMetadata

/-! The exact finite order of all real physical tiles along one original source edge. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] Raster.width Raster.height

theorem trace_index (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (e : ℕ) (p : GridRouting.Point) (hp : HasPoint (Route.edgeSegments (refinedProgram v.1,e)) p) :
    ∃i : Index v,position i=p := by
  have htrace:=(Route.edgeSegments_trace _ _ _).mp hp
  cases hv : Raster.vertexAt (v.1,p) with
  | some g=>
    obtain ⟨hg,he⟩:=Raster.vertexAt_sound hv
    exact ⟨gateIndex v g hg,he⟩
  | none=>
    have he:=Raster.owner_unique hP hT ((Raster.vertexAt_none_iff v.1 p).mp hv) htrace
    obtain ⟨k,hk⟩:=CellPlan.cell_wire v hP hT p hv he
    have hb:=Raster.trace_bounds v.1 htrace
    let c : Raster.Cell v.1:=(⟨p.1,by omega⟩,⟨p.2,by omega⟩)
    refine ⟨⟨(c,.inr (k,!(v.2.1.getD e false),!(v.2.2.getD e false))),?_⟩,rfl⟩
    change PhysicalTiles.key (CellPlan.cell (v,p))=_
    rw [hk]
    rfl

structure EdgeOrder (v : CellPlan.Source) (e : ℕ) where
  source : GridRouting.Point
  target : GridRouting.Point
  connected : Connects (Route.edgeSegments (refinedProgram v.1,e)) source target
  flow : UnitFlow (Route.edgeSegments (refinedProgram v.1,e)) source target
  sequence : DirectedPath.Sequence (UnitStep (Route.edgeSegments (refinedProgram v.1,e))) source target

theorem edgeOrder_exists (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (e : Fin v.1.compile.edgeCount) : Nonempty (EdgeOrder v e.val) := by
  obtain ⟨p,q,_,_,hc,hf⟩:=complete_flow hP hT e
  have hc' : Connects (Route.edgeSegments (refinedProgram v.1,e.val)) (refinePoint p) (refinePoint q):=by
    rw [refinedProgram,Route.edgeSegments_refined]
    exact hc.refined
  have hf' : UnitFlow (Route.edgeSegments (refinedProgram v.1,e.val)) (refinePoint p) (refinePoint q):=by
    rw [refinedProgram,Route.edgeSegments_refined]
    exact hf.refined
  obtain ⟨s⟩:=DirectedPath.nonempty_of_reach hc'.unitReach
  exact ⟨⟨refinePoint p,refinePoint q,hc',hf',s⟩⟩

namespace EdgeOrder
variable {v : CellPlan.Source} {e : ℕ} (order : EdgeOrder v e)

theorem node_mem (i : Fin (order.sequence.length+1)) :
    HasPoint (Route.edgeSegments (refinedProgram v.1,e)) (order.sequence.node i) := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · exact order.sequence.last.symm ▸order.flow.target_mem
  · obtain ⟨d,ha,_⟩:=order.sequence.step j
    exact ((order.flow.outgoing_iff _).mp ⟨d,ha⟩).1

noncomputable def index (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) : Index v:=
  Classical.choose (trace_index v hP hT e (order.sequence.node i) (order.node_mem i))

theorem index_position (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) : position (order.index hP hT i)=order.sequence.node i:=
  Classical.choose_spec (trace_index v hP hT e (order.sequence.node i) (order.node_mem i))

private theorem index_injective (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    Function.Injective (order.index hP hT) := by
  intro i j he
  apply order.sequence.injective order.flow.step_left_unique order.flow.no_step_source
  exact (order.index_position hP hT i).symm.trans ((congrArg position he).trans (order.index_position hP hT j))

/-- Every real tile on the original edge occurs exactly once in this order. -/
theorem covers (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) (hp : HasPoint (Route.edgeSegments (refinedProgram v.1,e)) (position i)) :
    ∃j,order.index hP hT j=i := by
  obtain ⟨j,hj⟩:=order.sequence.covers order.flow.step_right_unique order.flow.no_step_target
    (order.connected.point_unitReach hp)
  refine ⟨j,position_injective ((order.index_position hP hT j).trans hj)⟩

private theorem adjacent (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Fin (order.sequence.length+1))
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e))
      (position (order.index hP hT i)) (position (order.index hP hT j))) : j.val=i.val+1 := by
  rw [order.index_position,order.index_position] at h
  exact order.sequence.step_index
    (order.sequence.injective order.flow.step_left_unique order.flow.no_step_source)
    order.flow.step_right_unique order.flow.no_step_target i j h

theorem predecessor (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) (j : Index v)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e))
      (position j) (position (order.index hP hT i))) :
    ∃k,order.index hP hT k=j ∧k.val+1=i.val := by
  obtain ⟨k,hk⟩:=order.covers hP hT j h.left_mem
  exact ⟨k,hk,(order.adjacent hP hT k i (hk.symm ▸h)).symm⟩

theorem successor (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) (j : Index v)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e))
      (position (order.index hP hT i)) (position j)) :
    ∃k,order.index hP hT k=j ∧k.val=i.val+1 := by
  obtain ⟨k,hk⟩:=order.covers hP hT j h.right_mem
  exact ⟨k,hk,order.adjacent hP hT i k (hk.symm ▸h)⟩

noncomputable def numberedNode (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) : Fin (Fintype.card (Index v)):=numbering v (order.index hP hT i)

private theorem numberedNode_injective (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    Function.Injective (order.numberedNode hP hT):=(numbering v).injective.comp (order.index_injective hP hT)

noncomputable def forwardMask (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (t : ℕ) :
    Fin (Fintype.card (Index v))→Bool:=ProfileSweep.stage (order.numberedNode hP hT) (fun _=>false) t

noncomputable def backwardMask (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (t : ℕ) :
    Fin (Fintype.card (Index v))→Bool:=ProfileSweep.stage (fun j=>order.numberedNode hP hT j.rev) (fun _=>false) t

theorem forward_current (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) : order.forwardMask hP hT i.val (order.numberedNode hP hT i)=false:=
  ProfileSweep.node_false _ (order.numberedNode_injective hP hT) _ (fun _=>rfl) _ _ (le_refl _)

theorem forward_before (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Fin (order.sequence.length+1)) (h : j.val < i.val) :
    order.forwardMask hP hT i.val (order.numberedNode hP hT j)=true:=ProfileSweep.node_true _ _ _ _ h

theorem forward_after (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Fin (order.sequence.length+1)) (h : i.val < j.val) :
    order.forwardMask hP hT i.val (order.numberedNode hP hT j)=false:=
  ProfileSweep.node_false _ (order.numberedNode_injective hP hT) _ (fun _=>rfl) _ _ (by omega)

theorem backward_current (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) : order.backwardMask hP hT i.val (order.numberedNode hP hT i.rev)=false:=
  ProfileSweep.node_false _ ((order.numberedNode_injective hP hT).comp Fin.rev_injective) _ (fun _=>rfl) _ _ (le_refl _)

theorem backward_before (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Fin (order.sequence.length+1)) (h : j.val < i.rev.val) :
    order.backwardMask hP hT i.val (order.numberedNode hP hT j)=false:=by
  have hj : i.val≤j.rev.val:=by
    have hh:=Fin.rev_lt_rev.mpr (show j < i.rev from h)
    simpa only [Fin.rev_rev,Fin.le_def] using le_of_lt hh
  have hh:=ProfileSweep.node_false (fun j=>order.numberedNode hP hT j.rev)
    ((order.numberedNode_injective hP hT).comp Fin.rev_injective) (fun _=>false) (fun _=>rfl) i.val j.rev hj
  simpa only [backwardMask,Fin.rev_rev] using hh

theorem backward_after (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Fin (order.sequence.length+1)) (h : i.rev.val < j.val) :
    order.backwardMask hP hT i.val (order.numberedNode hP hT j)=true:=by
  have hj : j.rev.val < i.val:=by
    have hh:=Fin.rev_lt_rev.mpr (show i.rev < j from h)
    simpa only [Fin.rev_rev,Fin.lt_def] using hh
  have hh:=ProfileSweep.node_true (fun j=>order.numberedNode hP hT j.rev) (fun _=>false) i.val j.rev hj
  simpa only [backwardMask,Fin.rev_rev] using hh

end EdgeOrder
end PushPuzzle.PushFS.Reduction.PhysicalInventory
