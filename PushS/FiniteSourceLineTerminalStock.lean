/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceVacantSlots
public import PushS.FiniteSourcePathEvents
public import PushS.FiniteSourceNeighborSlots
public import PushS.FiniteSourceTerminalStock

/-! Internal collinear successors and the real neighboring source tile prepare every terminal support. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

/-- The actual consumer tile, its face and its normal owner phases beyond a producer. -/
structure TerminalNeighbor (phase : Fin (codes w v).length → Bool) where
  face : Direction
  producer : LinePort w s.code face false
  consumerLow : ∀ i : Fin (codes w v).length,
    neighbor face ((codes w v).get s.index).1 = some ((codes w v).get i).1 →
      ConsumerLow (CellPlan.cell (v,((codes w v).get i).1)) face.opposite (phase i)

/-- The actual working-row support two cells beyond the final interface. -/
@[expose]
def terminalSupport : Cell (Line.width w s.atoms) (Line.height w) :=
  Line.Readout.rail w s.atoms (LineCode.capIndex w s.atoms false)

private theorem terminal_support_coordinates : coordinates (s.actualEmbedding.cells s.terminalSupport) =
    macroShift w ((codes w v).get s.index).1 (s.code.capWorld w hw false) :=
  s.actual_cell_coordinates _

theorem eq_terminal_support (p : Cell (Line.width w s.atoms) (Line.height w))
    (hx : p.1.val = FiniteTools.radius w+Line.span w s.atoms+2) (hy : p.2.val = FiniteTools.radius w) :
    p = s.terminalSupport := by
  apply Prod.ext <;> apply Fin.ext
  · dsimp [terminalSupport,Line.Readout.rail,LineCode.capIndex]
    unfold FiniteTools.radius at *
    omega
  · exact hy

theorem TerminalNeighbor.support_empty {phase : Fin (codes w v).length → Bool}
    (T : s.TerminalNeighbor phase) :
    s.actualEmbedding.cells s.terminalSupport ∉ PrimitiveProfile.boxes w hw v phase :=
  s.producer_cap_empty phase T.face T.producer T.consumerLow _ s.terminal_support_coordinates

end LineSite

namespace PathSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}
variable (s : PathSite w hw v P) (G : P.Geometry w)
include G

private theorem collinear_terminal_second (i : Fin P.segments.length) (hn : i.val+1 < P.segments.length)
    (ht : ¬P.hasTurn i.val) :
    (s.line i).actualEmbedding.cells (s.line i).terminalSupport =
      (s.line ⟨i.val+1,hn⟩).actualEmbedding.cells
        (Line.cell w hw (s.line ⟨i.val+1,hn⟩).atoms false
          (Line.secondLabel w (segmentLength (s.line ⟨i.val+1,hn⟩).code.segment)
            ((s.line ⟨i.val+1,hn⟩).code.above != (s.line ⟨i.val+1,hn⟩).code.desiredSide))) := by
  have H := P.collinear_contract w G i.val hn ht
  have hworld : (P.line i.val).capWorld w hw false = (P.line (i.val+1)).secondWorld w hw false := by
    rw [LineCode.capWorld_eq w hw _ H.first_good false,LineCode.secondWorld_eq w hw _ H.next_good false]
    simp only [Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero,H.directions,H.joined]
  apply (show Function.Injective (@coordinates _ _) from Fin.val_injective.prodMap Fin.val_injective)
  rw [(s.line i).terminal_support_coordinates,(s.line ⟨i.val+1,hn⟩).actual_second_coordinates false]
  rw [s.line_location,s.line_location]
  exact congrArg (macroShift w s.location) hworld

theorem internal_terminal_empty (hb : P.target = !P.initial)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length)
    (F : PathEvent.Frontier s phase (.line i)) (hn : i.val+1 < P.segments.length)
    (hlast : (s.line i).code.last = true) :
    (s.line i).actualEmbedding.cells (s.line i).terminalSupport ∉ PrimitiveProfile.boxes w hw v phase := by
  have ht : ¬P.hasTurn i.val := by
    intro ht
    have hh := (P.junction_contract w G i.val ht).incoming_last
    change (s.line i).code.last = false at hh
    rw [hlast] at hh
    cases hh
  rw [s.collinear_terminal_second G i hn ht]
  apply (s.line ⟨i.val+1,hn⟩).second_low_empty
  · rw [s.line_target,s.line_initial]
    exact hb
  · exact hP
  · exact hT
  · have hh := F.after (.line ⟨i.val+1,hn⟩) (by change 2*i.val < 2*(i.val+1); omega)
    change phase (s.line ⟨i.val+1,hn⟩).index = !P.initial at hh
    rw [s.line_initial]
    exact hh

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
