/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathForward
public import PushS.FiniteSourceCoreConnectivity
public import PushS.FiniteRoutingArmEndpoints

/-! Actual core-owned endpoint identities of every emitted gate arm. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory FiniteGeometry.side Line.width Line.height LineSite.atoms

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

namespace CoreSite

variable (s : CoreSite w hw v)

/-- The literal gate record selects its actual emitted core entry. -/
def of_gate (q : GridRouting.Point) (g : CellPlan.Gate)
    (hq : (q,some (Sum.inl g)) ∈ CellPlan.cells v) : CoreSite w hw v := by
  have hm : (q,PrimitiveCode.core g.2) ∈ codes w v :=
    PathSite.local_mem hq (by change PrimitiveCode.core g.2 ∈ gateCodes w g.2; exact List.mem_cons_self)
  let i : Fin (codes w v).length := ⟨(codes w v).idxOf (q,.core g.2),List.idxOf_lt_length_of_mem hm⟩
  exact ⟨i,g.2,congrArg Prod.snd (List.getElem_idxOf (List.idxOf_lt_length_of_mem hm))⟩

theorem of_gate_location (q : GridRouting.Point) (g : CellPlan.Gate)
    (hq : (q,some (Sum.inl g)) ∈ CellPlan.cells v) :
    ((codes w v).get (of_gate (hw := hw) q g hq).index).1 = q := by
  exact congrArg Prod.fst (List.getElem_idxOf (List.idxOf_lt_length_of_mem
    (PathSite.local_mem hq (by change PrimitiveCode.core g.2 ∈ gateCodes w g.2; exact List.mem_cons_self))))

/-- The core itself owns the exact first normal box of each one of its three arms. -/
def portLabel (role : Fin 3) : (inventory w hw v).PhysicalLabel :=
  if h : s.gate.core.isAND = true then s.andLabel h (andPortLabel w role)
  else s.orLabel (Bool.eq_false_iff.mpr h) (orPortLabel w role)

theorem portLabel_owner (role : Fin 3) : (s.portLabel role).1 = s.index := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind <;> simpa only [portLabel,Bool.false_eq_true,dite_false,dite_true,andLabel,orLabel] using
    (primitiveLabel_owner w hw v index (.core _) he _)

private theorem cell_ext {W H : ℕ} {p q : Cell W H} (h : coordinates p = coordinates q) : p = q :=
  Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

/-- The compiler-owned core identity is the literal first arm slot in the initial configuration. -/
theorem arm_source_first (role : Fin 3) (p : PathSite w hw v (armSpec w s.gate role))
    (hloc : p.location = ((codes w v).get s.index).1)
    (h : 0 < (armSpec w s.gate role).segments.length) :
    (inventory w hw v).source (s.portLabel role) = (p.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (p.line ⟨0,h⟩).atoms (armSpec w s.gate role).initial
        (Line.cutFirstLabel w (p.line ⟨0,h⟩).atoms)) := by
  apply cell_ext
  rw [(p.line ⟨0,h⟩).actual_first_coordinates,p.line_location,hloc]
  unfold portLabel
  split
  next hg =>
    rw [s.and_source_actual hg,s.embedding_coordinates]
    change _ = macroShift w _ (((armSpec w s.gate role).line 0).firstWorld w hw
      (portInflow s.gate.core.initial.left s.gate.core.initial.upper s.gate.core.initial.right role))
    rw [and_arm_first_shared w hw s.gate hg]
  next hg =>
    rw [s.or_source_actual (Bool.eq_false_iff.mpr hg),s.embedding_coordinates]
    change _ = macroShift w _ (((armSpec w s.gate role).line 0).firstWorld w hw
      (portInflow s.gate.core.initial.left s.gate.core.initial.upper s.gate.core.initial.right role))
    rw [or_arm_first_shared w hw s.gate (Bool.eq_false_iff.mpr hg)]

/-- The same actual core identity supplies the literal first arm target slot. -/
theorem arm_target_first (role : Fin 3) (p : PathSite w hw v (armSpec w s.gate role))
    (hloc : p.location = ((codes w v).get s.index).1)
    (h : 0 < (armSpec w s.gate role).segments.length) :
    (inventory w hw v).target (s.portLabel role) = (p.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (p.line ⟨0,h⟩).atoms (armSpec w s.gate role).target
        (Line.cutFirstLabel w (p.line ⟨0,h⟩).atoms)) := by
  apply cell_ext
  rw [(p.line ⟨0,h⟩).actual_first_coordinates,p.line_location,hloc]
  unfold portLabel
  split
  next hg =>
    rw [s.and_target_actual hg,s.embedding_coordinates]
    change _ = macroShift w _ (((armSpec w s.gate role).line 0).firstWorld w hw
      (portInflow s.gate.core.target.left s.gate.core.target.upper s.gate.core.target.right role))
    rw [and_arm_first_shared w hw s.gate hg]
  next hg =>
    rw [s.or_target_actual (Bool.eq_false_iff.mpr hg),s.embedding_coordinates]
    change _ = macroShift w _ (((armSpec w s.gate role).line 0).firstWorld w hw
      (portInflow s.gate.core.target.left s.gate.core.target.upper s.gate.core.target.right role))
    rw [or_arm_first_shared w hw s.gate (Bool.eq_false_iff.mpr hg)]

/-- Every actual arm event is owned by a line or turn, hence is external to its core's identity owner. -/
theorem arm_event_ne_core (role : Fin 3) (p : PathSite w hw v (armSpec w s.gate role))
    (a : PathEvent (armSpec w s.gate role)) : a.owner p ≠ s.index := by
  intro he
  have hh := congrArg Prod.snd (p.get_index a.code a.member)
  change ((codes w v).get (a.owner p)).2 = a.code at hh
  rw [he,s.code_eq] at hh
  cases a <;> cases hh

/-- A producing arm owns its final endpoint, so its core supplies the only external identity. -/
noncomputable def outgoingEndpoints (role : Fin 3) (hin : s.gate.incoming.get role = false)
    (p : PathSite w hw v (armSpec w s.gate role))
    (hloc : p.location = ((codes w v).get s.index).1) : p.Endpoints where
  first := s.portLabel role
  final h := by simp only [armSpec,hin,Bool.not_false] at h; contradiction
  source_first := s.arm_source_first role p hloc
  target_first := s.arm_target_first role p hloc
  source_final h := by simp only [armSpec,hin,Bool.not_false] at h; contradiction
  target_final h := by simp only [armSpec,hin,Bool.not_false] at h; contradiction

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
