/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathCompletion

/-! Every actual ordinary wire selects its real preceding gate-arm or wire identity. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires Plan
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

/-- An actual nonempty cell record occurs literally in the source compiler's cell table. -/
theorem record_mem (p : GridRouting.Point) (c : CellPlan.Gate ⊕ CellPlan.Wire)
    (hc : CellPlan.cell (v,p) = some c) : (p,some c) ∈ CellPlan.cells v := by
  have hb := CellPlan.nonempty_bounds (show CellPlan.cell (v,p) ≠ none by rw [hc]; simp)
  simpa only [hc] using cell_entry_mem v p hb.1 hb.2

/-- The complete shared first identity is owned by the literal preceding source-grid neighbor. -/
structure WireInput {a : Catalog.Bitmap.Args} (t : PathSite w hw v (wireSpec w a)) where
  previous : GridRouting.Point
  neighbor : PushFS.Reduction.neighbor (Catalog.sourceDirection a.1).opposite t.location = some previous
  endpoints : t.Endpoints
  first_location : ((codes w v).get endpoints.first.1).1 = previous

/-- Every actual wire input has its genuine compiler-owned preceding identity, in both normal configurations. -/
noncomputable def actualWireInput (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    {a : Catalog.Bitmap.Args} (e : ℕ) (t : PathSite w hw v (wireSpec w a))
    (hc : CellPlan.cell (v,t.location) = some (.inr (e,a))) : WireInput t := by
  apply Classical.choice
  have hp : LocalPort (CellPlan.cell (v,t.location)) (Catalog.sourceDirection a.1).opposite true := by
    rw [hc]
    exact Or.inl ⟨rfl,rfl⟩
  have hu := local_port_used v _ _ true hp
  obtain ⟨p,hn,_⟩ := CellPlan.used_neighbor v hP hT _ _ hu
  have hh := local_port_reciprocal v hP hT _ _ _ hn true hp
  have hn' : PushFS.Reduction.neighbor (Catalog.sourceDirection a.1) p = some t.location := by
    simpa only [Direction.opposite_opposite] using neighbor_reverse hn
  cases hprev : CellPlan.cell (v,p) with
  | none => simp only [hprev,LocalPort] at hh
  | some prev =>
    cases prev with
    | inl g =>
      obtain ⟨role,hd,hin⟩ := (show LocalPort (some (.inl g)) (Catalog.sourceDirection a.1) false by
        simpa only [hprev,Direction.opposite_opposite,Bool.not_true] using hh)
      let s := PathSite.arm (hw := hw) p g role (record_mem p (.inl g) hprev)
      have hsLoc : s.location = p := rfl
      have hns : PushFS.Reduction.neighbor (PortAnnulus.outerDirection (g.2.pattern,g.2.rotation,role)) s.location = some t.location := by
        rw [hd,hsLoc]
        exact hn'
      refine ⟨⟨p,hn,actual_gate_wire_endpoints hP hT role hin g.1 e s t hns (by exact hprev) hc,?_⟩⟩
      change ((codes w v).get (ArmBoundary.outputIdentity s hin).1).1 = p
      exact ArmBoundary.output_owner_location s hin
    | inr b =>
      have hp' : LocalPort (some (.inr b)) (Catalog.sourceDirection a.1) false := by
        simpa only [hprev,Direction.opposite_opposite,Bool.not_true] using hh
      rcases hp' with ⟨h,_⟩ | ⟨_,hd⟩
      · cases h
      · let s := PathSite.wire (hw := hw) p b (record_mem p (.inr b) hprev)
        have hsLoc : s.location = p := rfl
        have hns : PushFS.Reduction.neighbor (Catalog.targetDirection b.2.1) s.location = some t.location := by
          rw [←hd,hsLoc]
          exact hn'
        refine ⟨⟨p,hn,actual_wire_wire_endpoints hP hT b.1 e s t hns (by exact hprev) hc,?_⟩⟩
        change ((codes w v).get (WireBoundary.outputIdentity s).1).1 = p
        exact WireBoundary.output_owner_location s

namespace WireInput

variable {a : Catalog.Bitmap.Args} {t : PathSite w hw v (wireSpec w a)} (I : WireInput t)

/-- A low prepared predecessor makes the concrete actual wire endpoints ready for its full path macro. -/
theorem ready (phase : GridRouting.Point → Bool) (hp : phase I.previous = a.2.1) :
    t.BoundaryReady I.endpoints (tilePhases phase) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro b he
    have hh := congrArg (fun i => ((codes w v).get i).1) he
    rw [b.owner_location,I.first_location] at hh
    exact neighbor_distinct I.neighbor hh
  · intro h
    change true = false at h
    cases h
  · unfold tilePhases
    rw [I.first_location]
    exact hp
  · intro h
    change true = false at h
    cases h

end WireInput
end PushPuzzle.PushS.FiniteSourceInventory
