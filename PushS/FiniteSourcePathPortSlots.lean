/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceActualPathReadout
public import PushS.FiniteSourceCorePorts
public import PushS.FiniteRoutingPortExclusion

/-! Actual path ports keep their literal external owner and core-arm high-slot identity. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open PushFS.Gadgets.Wires.Soundness
open scoped Classical

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

namespace PathSite

variable {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w) (E : s.Endpoints)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

theorem actual_input_label (hne : 0 < P.segments.length) :
    ((s.actualReadout G E hP hT).line ⟨0,hne⟩).input.label = E.first := by
  apply (admissible w hw v hP hT).source_injective
  apply (show Function.Injective (@coordinates _ _) from Fin.val_injective.prodMap Fin.val_injective)
  have hleft := (s.actualReadout G E hP hT).line_source_input ⟨0,hne⟩
  have hright := congrArg (@coordinates (width w v) (height w v)) (E.source_first hne)
  rw [(s.line ⟨0,hne⟩).actual_first_coordinates,s.line_location] at hright
  exact hleft.trans hright.symm

theorem actual_output_label (hk : P.keepEndpoint = false) (i : Fin P.segments.length)
    (hi : i.val+1 = P.segments.length) :
    ((s.actualReadout G E hP hT).line i).output.label = E.final hk := by
  apply (admissible w hw v hP hT).source_injective
  apply (show Function.Injective (@coordinates _ _) from Fin.val_injective.prodMap Fin.val_injective)
  have hleft := (s.actualReadout G E hP hT).line_source_output i
  have hright := congrArg (@coordinates (width w v) (height w v)) (E.source_final hk i hi)
  rw [(s.line i).actual_last_coordinates,s.line_location] at hright
  exact hleft.trans hright.symm

end PathSite

namespace CoreSite

open FiniteGateReadout FiniteGeometry

variable (s : CoreSite w hw v) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

private theorem port_direction (role : Fin 3) : (s.port hP hT role).direction = PortAnnulus.innerDirection role := by
  unfold port
  split_ifs <;> rfl

private theorem port_slot_coordinates (role : Fin 3) :
    coordinates (s.port hP hT role).slot = macroShift w ((codes w v).get s.index).1
      (Line.along w (PortAnnulus.innerDirection role) (corePort w s.gate.core.isAND role) 1) := by
  have hb : portInflow true true false role = true := by fin_cases role <;> rfl
  unfold port
  split_ifs with hg
  · change coordinates ((GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells
      (andCell w true true false (andPortLabel w role))) = _
    rw [←s.embedding_translate,s.embedding_coordinates,andPort_world,hb,hg]
    rfl
  · change coordinates ((GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells
      (orCell w true true false (orPortLabel w role))) = _
    rw [←s.embedding_translate,s.embedding_coordinates,orPort_world,hb,Bool.eq_false_iff.mpr hg]
    rfl

private theorem arm_input_port (role : Fin 3) (p : PathSite w hw v (armSpec w s.gate role))
    (E : p.Endpoints) (hloc : p.location = ((codes w v).get s.index).1) (hfirst : E.first = s.portLabel role)
    (hne : 0 < (armSpec w s.gate role).segments.length) :
    ((p.actualReadout (armSpec_geometry w s.gate role) E hP hT).line ⟨0,hne⟩).input = s.port hP hT role := by
  apply PhysicalPort.ext_coordinates
  · exact (p.actual_input_label (armSpec_geometry w s.gate role) E hP hT hne).trans
      (hfirst.trans (s.port_label hP hT role).symm)
  · have hl := (p.actualReadout (armSpec_geometry w s.gate role) E hP hT).line_input_slot ⟨0,hne⟩ true
    have hr := s.port_slot_coordinates hP hT role
    change coordinates ((p.actualReadout (armSpec_geometry w s.gate role) E hP hT).line ⟨0,hne⟩).input.slot = _
    rw [hr]
    exact hl.trans (by
      change macroShift w p.location (((armSpec w s.gate role).line 0).firstWorld w hw true) = _
      rw [armSpec_first_slot,hloc]
      rfl)
  · exact (p.actualReadout (armSpec_geometry w s.gate role) E hP hT).line_direction ⟨0,hne⟩ |>.trans
      ((armSpec_first_direction w s.gate role).trans (s.port_direction hP hT role).symm)

/-- A real core's outer claim traverses its complete emitted arm, with every intermediate tool retained. -/
theorem arm_claim_signal (role : Fin 3) (p : PathSite w hw v (armSpec w s.gate role))
    (E : p.Endpoints) (hloc : p.location = ((codes w v).get s.index).1) (hfirst : E.first = s.portLabel role)
    (hne : 0 < (armSpec w s.gate role).segments.length)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final)
    (hclaim : portInflow (s.boundarySignals hP hT S).left (s.boundarySignals hP hT S).upper
      (s.boundarySignals hP hT S).right role = true) (i : Fin (armSpec w s.gate role).segments.length) :
    ((p.actualReadout (armSpec_geometry w s.gate role) E hP hT).line i).output.High S := by
  have hin : (s.port hP hT role).High S := of_decide_eq_true ((s.port_claim hP hT S role).trans hclaim)
  have hinput : ((p.actualReadout (armSpec_geometry w s.gate role) E hP hT).line ⟨0,hne⟩).input.High S :=
    (s.arm_input_port hP hT role p E hloc hfirst hne).symm ▸ hin
  exact p.actual_signal (armSpec_geometry w s.gate role) E hP hT hne h hinput i

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
