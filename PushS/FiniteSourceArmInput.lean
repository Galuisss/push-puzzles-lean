/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceWireInput

/-! Every actual selected gate arm has its real core and neighboring ordinary endpoint identities. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires Plan
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

/-- The first arm identity is its core's box; every unowned last identity belongs to its actual reciprocal source neighbor. -/
structure ArmInput (c : CoreSite w hw v) (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role)) where
  endpoints : p.Endpoints
  first_core : endpoints.first = c.portLabel role
  final_neighbor : ∀ h,PushFS.Reduction.neighbor (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role))
    p.location = some ((codes w v).get (endpoints.final h).1).1

/-- Actual cell adjacency selects all endpoint identities of either a producing or consuming arm. -/
noncomputable def actualArmInput (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (c : CoreSite w hw v) (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1) (vertex : VertexData)
    (hc : CellPlan.cell (v,p.location) = some (.inl (vertex,c.gate))) : ArmInput c role p := by
  apply Classical.choice
  by_cases hin : c.gate.incoming.get role = false
  · refine ⟨⟨c.outgoingEndpoints role hin p hloc,rfl,?_⟩⟩
    intro h
    simp only [armSpec,hin,Bool.not_false] at h
    contradiction
  · have hin' : c.gate.incoming.get role = true := Bool.eq_true_of_ne_false hin
    have hp : LocalPort (CellPlan.cell (v,p.location))
        (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)) true := by
      rw [hc]
      exact ⟨role,rfl,hin'⟩
    obtain ⟨r,hn,_⟩ := CellPlan.used_neighbor v hP hT _ _ (local_port_used v _ _ true hp)
    have hh := local_port_reciprocal v hP hT _ _ _ hn true hp
    cases hprev : CellPlan.cell (v,r) with
    | none => simp only [hprev,LocalPort] at hh
    | some prev =>
      cases prev with
      | inl g => exact (neighboring_gates_impossible v _ _ _ hn vertex g.1 c.gate g.2 hc hprev).elim
      | inr a =>
        have hp' : LocalPort (some (.inr a))
            (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)).opposite false := by
          simpa only [hprev,Bool.not_true] using hh
        rcases hp' with ⟨h,_⟩ | ⟨_,hd⟩
        · cases h
        · let s := PathSite.wire (hw := hw) r a (record_mem r (.inr a) hprev)
          have hd' : PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role) =
              (Catalog.targetDirection a.2.1).opposite := by
            simpa only [Direction.opposite_opposite] using congrArg Direction.opposite hd
          have hns : neighbor (Catalog.targetDirection a.2.1) s.location = some p.location := by
            rw [←hd]
            exact neighbor_reverse hn
          refine ⟨⟨actual_wire_gate_endpoints hP hT c role hin' vertex a.1 s p hloc hns hd' hc hprev,rfl,?_⟩⟩
          intro h
          change neighbor (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)) p.location =
            some ((codes w v).get (WireBoundary.outputIdentity s).1).1
          rw [WireBoundary.output_owner_location]
          exact hn

namespace CoreSite

variable (c : CoreSite w hw v)

/-- The selected arm executes before a rising core claim and after a falling core claim. -/
noncomputable def preparedArmBase (role : Fin 3) (base : Fin (codes w v).length → Bool) :
    Fin (codes w v).length → Bool :=
  if (armSpec w c.gate role).initial then Function.update base c.index true else base

/-- The actual shared first core box is low before either physical direction of full arm propagation. -/
private theorem preparedArmBase_core (role : Fin 3) (base : Fin (codes w v).length → Bool)
    (fresh : base c.index = false) :
    c.preparedArmBase role base c.index = (armSpec w c.gate role).initial := by
  cases hp : (armSpec w c.gate role).initial <;> simp only [preparedArmBase,hp,Bool.false_eq_true,ite_false,ite_true,
    Function.update_self,fresh]

/-- Preparing the selected core owner preserves every external owner's actual phase. -/
theorem preparedArmBase_external (role : Fin 3) (base : Fin (codes w v).length → Bool)
    (i : Fin (codes w v).length) (hi : i ≠ c.index) : c.preparedArmBase role base i = base i := by
  unfold preparedArmBase
  split_ifs
  · exact Function.update_of_ne hi _ _
  · rfl

/-- All actual selected arm primitives are fresh after the possible preliminary core macro. -/
theorem preparedArmBase_fresh (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (phase : GridRouting.Point → Bool) (hp : phase p.location = false) :
    ∀ a : PathEvent (armSpec w c.gate role),c.preparedArmBase role (tilePhases phase) (a.owner p) = false := by
  intro a
  rw [c.preparedArmBase_external role _ _ (c.arm_event_ne_core role p a)]
  exact p.path_fresh phase hp a

end CoreSite

namespace ArmInput

variable {c : CoreSite w hw v} {role : Fin 3} {p : PathSite w hw v (armSpec w c.gate role)} (I : ArmInput c role p)

/-- The chosen core order and the actual prepared reciprocal neighbor give every arm exterior phase condition. -/
theorem ready (hloc : p.location = ((codes w v).get c.index).1)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (outside : ∀ h,phase ((codes w v).get (I.endpoints.final h).1).1 = !(armSpec w c.gate role).initial) :
    p.BoundaryReady I.endpoints (c.preparedArmBase role (tilePhases phase)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    rw [I.first_core,c.portLabel_owner]
    exact c.arm_event_ne_core role p a
  · intro h a he
    have hh := congrArg (fun i => ((codes w v).get i).1) he
    rw [a.owner_location] at hh
    exact neighbor_distinct (I.final_neighbor h) hh
  · rw [I.first_core,c.portLabel_owner]
    apply c.preparedArmBase_core
    unfold tilePhases
    rw [←hloc]
    exact fresh
  · intro h
    have hi : (I.endpoints.final h).1 ≠ c.index := by
      intro he
      have hh : ((codes w v).get (I.endpoints.final h).1).1 = p.location := he ▸ hloc.symm
      exact neighbor_distinct (I.final_neighbor h) hh.symm
    rw [c.preparedArmBase_external role _ _ hi]
    exact outside h

end ArmInput
end PushPuzzle.PushS.FiniteSourceInventory
