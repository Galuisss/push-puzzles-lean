/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathSites
public import PushS.FiniteRoutingLineNeighbors

/-! Actual global shared cells and their literal compiler-owned turn interfaces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

namespace LineSite

def finalOwned (s : LineSite w hw v) (hl : s.code.last = true) : (PrimitiveCode.line s.code).Labels w := by
  change Line.OwnedLabel w s.atoms s.code.first s.code.last
  refine ⟨Line.cutLastLabel w s.atoms,Or.inr ?_,Or.inl hl⟩
  have hn := Line.program_length_ge_six w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)
  change 0 < (Line.positions w false s.atoms).length-1
  exact Nat.sub_pos_of_lt (by exact lt_of_lt_of_le (by omega) hn)

def finalLabel (s : LineSite w hw v) (hl : s.code.last = true) : (inventory w hw v).PhysicalLabel :=
  s.label (s.finalOwned hl)

theorem source_finalLabel (s : LineSite w hw v) (hl : s.code.last = true) :
    (inventory w hw v).source (s.finalLabel hl) = s.actualEmbedding.cells
      (Line.cell w hw s.atoms s.code.initial (Line.cutLastLabel w s.atoms)) :=
  source_primitiveLabel w hw v s.index (.line s.code) s.code_eq (s.finalOwned hl)

theorem target_finalLabel (s : LineSite w hw v) (hl : s.code.last = true) :
    (inventory w hw v).target (s.finalLabel hl) = s.actualEmbedding.cells
      (Line.cell w hw s.atoms s.code.target (Line.cutLastLabel w s.atoms)) :=
  target_primitiveLabel w hw v s.index (.line s.code) s.code_eq (s.finalOwned hl)

end LineSite

namespace PathSite

variable (s : PathSite w hw v P) (G : P.Geometry w)

private theorem cell_ext {W H : ℕ} {p q : Cell W H} (h : coordinates p = coordinates q) : p = q :=
  Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

private theorem incoming_shared_cells (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (phase : Bool) :
    (s.line i).actualEmbedding.cells (Line.cell w hw (s.line i).atoms phase (Line.cutLastLabel w (s.line i).atoms)) =
      (s.turn G i hi).actualEmbedding.cells (Turn.cell w phase 0) := by
  apply cell_ext
  rw [(s.line i).actual_last_coordinates phase,(s.turn G i hi).actual_slot_coordinates phase 0,
    s.line_location i,s.turn_location G i hi]
  exact congrArg (shiftPoint (tileStride w*s.location.1) (tileStride w*s.location.2))
    ((P.junction_contract w G i.val hi).incoming_shared_phase w hw _ _ _ phase)

private theorem outgoing_shared_cells (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (phase : Bool) :
    (s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells
        (Line.cell w hw (s.line ⟨i.val+1,hi.1⟩).atoms phase (Line.cutFirstLabel w (s.line ⟨i.val+1,hi.1⟩).atoms)) =
      (s.turn G i hi).actualEmbedding.cells (Turn.cell w phase 1) := by
  apply cell_ext
  rw [(s.line ⟨i.val+1,hi.1⟩).actual_first_coordinates phase,(s.turn G i hi).actual_slot_coordinates phase 1,
    s.line_location ⟨i.val+1,hi.1⟩,s.turn_location G i hi]
  exact congrArg (shiftPoint (tileStride w*s.location.1) (tileStride w*s.location.2))
    ((P.junction_contract w G i.val hi).outgoing_shared_phase w hw _ _ _ phase)

include G in
private theorem collinear_shared_cells (i : Fin P.segments.length)
    (hi : i.val+1 < P.segments.length)
    (hn : ¬P.hasTurn i.val) (phase : Bool) :
    (s.line i).actualEmbedding.cells (Line.cell w hw (s.line i).atoms phase (Line.cutLastLabel w (s.line i).atoms)) =
      (s.line ⟨i.val+1,hi⟩).actualEmbedding.cells
        (Line.cell w hw (s.line ⟨i.val+1,hi⟩).atoms phase (Line.cutFirstLabel w (s.line ⟨i.val+1,hi⟩).atoms)) := by
  apply cell_ext
  rw [(s.line i).actual_last_coordinates phase,(s.line ⟨i.val+1,hi⟩).actual_first_coordinates phase,
    s.line_location i,s.line_location ⟨i.val+1,hi⟩]
  exact congrArg (shiftPoint (tileStride w*s.location.1) (tileStride w*s.location.2))
    ((P.collinear_contract w G i.val hi hn).shared w hw _ _ phase)

/-- The turn owns the incoming line's final interface in both canonical states. -/
theorem incoming_source_owner (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    (inventory w hw v).source ((s.turn G i hi).label 0) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms (s.line i).code.initial (Line.cutLastLabel w (s.line i).atoms)) := by
  rw [(s.turn G i hi).source_actual]
  exact (s.incoming_shared_cells G i hi P.initial).symm

theorem incoming_target_owner (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    (inventory w hw v).target ((s.turn G i hi).label 0) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms (s.line i).code.target (Line.cutLastLabel w (s.line i).atoms)) := by
  rw [(s.turn G i hi).target_actual]
  exact (s.incoming_shared_cells G i hi P.target).symm

/-- The turn owns the outgoing line's first interface in both canonical states. -/
theorem outgoing_source_owner (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    (inventory w hw v).source ((s.turn G i hi).label 1) = (s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨i.val+1,hi.1⟩).atoms (s.line ⟨i.val+1,hi.1⟩).code.initial
        (Line.cutFirstLabel w (s.line ⟨i.val+1,hi.1⟩).atoms)) := by
  rw [(s.turn G i hi).source_actual]
  exact (s.outgoing_shared_cells G i hi P.initial).symm

theorem outgoing_target_owner (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    (inventory w hw v).target ((s.turn G i hi).label 1) = (s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨i.val+1,hi.1⟩).atoms (s.line ⟨i.val+1,hi.1⟩).code.target
        (Line.cutFirstLabel w (s.line ⟨i.val+1,hi.1⟩).atoms)) := by
  rw [(s.turn G i hi).target_actual]
  exact (s.outgoing_shared_cells G i hi P.target).symm

omit G in
theorem collinear_last_owned (i : Fin P.segments.length) (hi : i.val+1 < P.segments.length)
    (hn : ¬P.hasTurn i.val) : (s.line i).code.last = true := by
  have he : segmentDirection (segmentAt P.segments i.val) = segmentDirection (segmentAt P.segments (i.val+1)) :=
    Classical.not_not.mp (fun h => hn ⟨hi,h⟩)
  simp only [line,PathSpec.line,lineCodeAt,ownsLast,show i.val+1 ≠ P.segments.length by omega,ite_false,he,decide_true]

include G in
theorem collinear_source_owner (i : Fin P.segments.length) (hi : i.val+1 < P.segments.length)
    (hn : ¬P.hasTurn i.val) :
    (inventory w hw v).source ((s.line i).finalLabel (s.collinear_last_owned i hi hn)) =
      (s.line ⟨i.val+1,hi⟩).actualEmbedding.cells
        (Line.cell w hw (s.line ⟨i.val+1,hi⟩).atoms (s.line ⟨i.val+1,hi⟩).code.initial
          (Line.cutFirstLabel w (s.line ⟨i.val+1,hi⟩).atoms)) := by
  rw [LineSite.source_finalLabel]
  exact s.collinear_shared_cells G i hi hn P.initial

include G in
theorem collinear_target_owner (i : Fin P.segments.length) (hi : i.val+1 < P.segments.length)
    (hn : ¬P.hasTurn i.val) :
    (inventory w hw v).target ((s.line i).finalLabel (s.collinear_last_owned i hi hn)) =
      (s.line ⟨i.val+1,hi⟩).actualEmbedding.cells
        (Line.cell w hw (s.line ⟨i.val+1,hi⟩).atoms (s.line ⟨i.val+1,hi⟩).code.target
          (Line.cutFirstLabel w (s.line ⟨i.val+1,hi⟩).atoms)) := by
  rw [LineSite.target_finalLabel]
  exact s.collinear_shared_cells G i hi hn P.target

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
