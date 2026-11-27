/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnNormalBridges
public import PushS.FiniteSourceTurnForward
public import PushS.FiniteSourceTurnConnectivity

/-! The exact four actual turn identities occupy the literal normal P/F/G/Q slot pairs. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteTools

attribute [local irreducible] codes width height Line.width Line.height FiniteTools.side FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

private theorem phase_label_coordinates (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (goal : Bool) (l : c.Labels w) :
    coordinates (if goal then (inventory w hw v).target (primitiveLabel w hw v i c he l)
      else (inventory w hw v).source (primitiveLabel w hw v i c he l)) =
      macroShift w ((codes w v).get i).1 (c.actor w hw goal l) := by
  cases goal
  · exact source_primitiveLabel_coordinates w hw v i c he l
  · exact target_primitiveLabel_coordinates w hw v i c he l

namespace TurnStep

variable (s : TurnStep w hw v P)

private theorem normal_predecessor_coordinates (goal : Bool) :
    coordinates (if goal then (inventory w hw v).target (s.labels .predecessor) else (inventory w hw v).source (s.labels .predecessor)) =
      macroShift w s.path.location (s.site.code.actionWorld w hw
        (Turn.normalCell w (if goal then P.target else P.initial) .predecessor)) := by
  have h := phase_label_coordinates (hw:=hw) s.incoming.index (.line s.incoming.code) s.incoming.code_eq goal s.predecessorOwned
  change coordinates (if goal then (inventory w hw v).target (s.labels .predecessor)
    else (inventory w hw v).source (s.labels .predecessor)) = _ at h
  have he : (PrimitiveCode.line s.incoming.code).actor w hw goal s.predecessorOwned =
      s.incoming.code.penultimateWorld w hw (if goal then P.target else P.initial) := by cases goal <;> rfl
  rw [he,show ((codes w v).get s.incoming.index).1 = s.path.location from s.path.line_location s.index] at h
  exact h.trans (congrArg (macroShift w s.path.location)
    (s.contract.predecessor_normal w hw _ _ _ (if goal then P.target else P.initial)))

private theorem normal_successor_coordinates (goal : Bool) :
    coordinates (if goal then (inventory w hw v).target (s.labels .successor) else (inventory w hw v).source (s.labels .successor)) =
      macroShift w s.path.location (s.site.code.actionWorld w hw
        (Turn.normalCell w (if goal then P.target else P.initial) .successor)) := by
  have h := phase_label_coordinates (hw:=hw) s.outgoing.index (.line s.outgoing.code) s.outgoing.code_eq goal s.successorOwned
  change coordinates (if goal then (inventory w hw v).target (s.labels .successor)
    else (inventory w hw v).source (s.labels .successor)) = _ at h
  have he : (PrimitiveCode.line s.outgoing.code).actor w hw goal s.successorOwned =
      s.outgoing.code.secondWorld w hw (if goal then P.target else P.initial) := by cases goal <;> rfl
  rw [he,show ((codes w v).get s.outgoing.index).1 = s.path.location from s.path.line_location ⟨s.index.val+1,s.hasTurn.1⟩] at h
  exact h.trans (congrArg (macroShift w s.path.location)
    (s.contract.successor_normal w hw _ _ _ (if goal then P.target else P.initial)))

private theorem normal_owned_coordinates (goal : Bool) (i : Fin 2) :
    coordinates (if goal then (inventory w hw v).target (s.site.label i) else (inventory w hw v).source (s.site.label i)) =
      macroShift w s.path.location (s.site.code.actionWorld w hw
        (Turn.normalCell w (if goal then P.target else P.initial) (Turn.label i))) := by
  have h := phase_label_coordinates (hw:=hw) s.site.index (.turn s.site.code) s.site.code_eq goal i
  rw [show ((codes w v).get s.site.index).1 = s.path.location from s.path.turn_location s.geometry s.index s.hasTurn] at h
  have he : (PrimitiveCode.turn s.site.code).actor w hw goal i =
      s.site.code.actionWorld w hw (Turn.normalCell w (if goal then P.target else P.initial) (Turn.label i)) := by
    fin_cases i <;> cases goal <;> rfl
  exact h.trans (congrArg (macroShift w s.path.location) he)

private theorem normal_slot_coordinates (goal : Bool) (l : TurnLabel) :
    coordinates (if goal then (inventory w hw v).target (s.labels l) else (inventory w hw v).source (s.labels l)) =
      macroShift w s.path.location (s.site.code.actionWorld w hw
        (Turn.normalCell w (if goal then P.target else P.initial) l)) := by
  cases l with
  | predecessor => exact s.normal_predecessor_coordinates goal
  | successor => exact s.normal_successor_coordinates goal
  | horizontal => exact s.normal_owned_coordinates goal 0
  | vertical => exact s.normal_owned_coordinates goal 1

theorem normal_slot_source (l : TurnLabel) : (inventory w hw v).source (s.labels l) =
    s.site.actualEmbedding.cells (Turn.normalCell w P.initial l) := by
  apply (show Function.Injective (@coordinates _ _) from Fin.val_injective.prodMap Fin.val_injective)
  have h := s.normal_slot_coordinates false l
  have he := s.site.actual_cell_coordinates (Turn.normalCell w P.initial l)
  rw [show ((codes w v).get s.site.index).1 = s.path.location from s.path.turn_location s.geometry s.index s.hasTurn] at he
  exact h.trans he.symm

theorem normal_slot_target (l : TurnLabel) : (inventory w hw v).target (s.labels l) =
    s.site.actualEmbedding.cells (Turn.normalCell w P.target l) := by
  apply (show Function.Injective (@coordinates _ _) from Fin.val_injective.prodMap Fin.val_injective)
  have h := s.normal_slot_coordinates true l
  have he := s.site.actual_cell_coordinates (Turn.normalCell w P.target l)
  rw [show ((codes w v).get s.site.index).1 = s.path.location from s.path.turn_location s.geometry s.index s.hasTurn] at he
  exact h.trans he.symm

end TurnStep
end PushPuzzle.PushS.FiniteSourceInventory
