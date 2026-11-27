/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshNodes
public import PushS.FiniteSourcePorts
public import PushS.FiniteSourceLineConnectivity

/-! Every real producing source port selects its literal complete terminal line and actual global table index. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height

private theorem local_producer_line (w : ℕ) (code : CellPlan.Code) (face : Direction)
    (hp : LocalPort code face false) :
    ∃ c : LineCode, .line c ∈ localCodes w code ∧ LineGood w c.segment ∧
      segmentDirection c.segment = face ∧ c.segment.finish = boundaryPoint w face ∧ c.first = false ∧ c.last = true := by
  cases code with
  | none => exact hp.elim
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,hd,hi⟩ := hp
      have hn : (armRoute w g.2 role).length-1 < (armRoute w g.2 role).length := by rw [armRoute_length,route_length]; omega
      refine ⟨gatePortLine w g.2 role,arm_code_mem_gateCodes w g.2 role _ ((armSpec w g.2 role).line_mem_codes _ hn),
        gatePortLine_good w g.2 role,(armSpec_last_direction w g.2 role).trans hd,?_,rfl,?_⟩
      · change ((armSpec w g.2 role).line ((armRoute w g.2 role).length-1)).segment.finish = _
        rw [armSpec_last_finish,hi]
        simp only [Bool.toNat_false,advance_zero,hd]
      · rw [gatePortLine_last,hi]
        rfl
    | inr q =>
      rcases hp with h | ⟨_,hd⟩
      · cases h.1
      · let i := (wireRoute w q.2.1).length-1
        have hpos : 0 < (wireRoute w q.2.1).length := by rw [wireRoute_length]; split_ifs <;> decide
        have hi : i < (wireRoute w q.2.1).length := by dsimp [i]; omega
        have hil : i+1 = (wireRoute w q.2.1).length := by dsimp [i]; omega
        refine ⟨(wireSpec w q.2).line i,(wireSpec w q.2).line_mem_codes i hi,
          (wireSpec w q.2).line_good w (wireSpec_geometry w q.2) i hi,
          (wire_last_direction w q.2 i hil).trans hd.symm,?_,rfl,?_⟩
        · rw [wire_last_finish w q.2 i hil,hd]
        · simp only [wireSpec,PathSpec.line,lineCodeAt,ownsLast,hil,ite_true]

theorem producer_line_site (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (pos : GridRouting.Point)
    (face : Direction) (hp : LocalPort (CellPlan.cell (v,pos)) face false) :
    ∃ s : LineSite w hw v, ((codes w v).get s.index).1 = pos ∧
      segmentDirection s.code.segment = face ∧ s.code.segment.finish = boundaryPoint w face ∧ s.code.last = true := by
  obtain ⟨c,hc,_,hd,he,_,hl⟩ := local_producer_line w (CellPlan.cell (v,pos)) face hp
  have hm := code_mem_of_local w v pos (.line c) hc
  let i : Fin (codes w v).length := ⟨(codes w v).idxOf (pos,.line c),List.idxOf_lt_length_of_mem hm⟩
  have hi : (codes w v).get i = (pos,.line c) := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
  exact ⟨⟨i,c,congrArg Prod.snd hi⟩,congrArg Prod.fst hi,hd,he,hl⟩

end PushPuzzle.PushS.FiniteSourceInventory
