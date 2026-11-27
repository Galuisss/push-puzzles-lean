/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceReadoutHops
public import PushS.FiniteRoutingPathOwners
public import PushS.FiniteRoutingWireCollars

/-! An actual source-table path selects its literal global line and turn entries. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction PushFS.Gadgets.Wires FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height

/-- The actual table contains every instruction of this path at one source-grid location. -/
structure PathSite (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (P : PathSpec) where
  location : GridRouting.Point
  member : ∀ c ∈ P.codes, (location,c) ∈ codes w v

namespace PathSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

def index (s : PathSite w hw v P) (c : PrimitiveCode) (hc : c ∈ P.codes) : Fin (codes w v).length :=
  ⟨(codes w v).idxOf (s.location,c), List.idxOf_lt_length_of_mem (s.member c hc)⟩

theorem get_index (s : PathSite w hw v P) (c : PrimitiveCode) (hc : c ∈ P.codes) :
    (codes w v).get (s.index c hc) = (s.location,c) := by
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (s.member c hc))

def line (s : PathSite w hw v P) (i : Fin P.segments.length) : LineSite w hw v where
  index := s.index (.line (P.line i.val)) (P.line_mem_codes i.val i.isLt)
  code := P.line i.val
  code_eq := congrArg Prod.snd (s.get_index (.line (P.line i.val)) (P.line_mem_codes i.val i.isLt))

def turn (s : PathSite w hw v P) (G : P.Geometry w) (i : Fin P.segments.length)
    (hi : P.hasTurn i.val) : TurnSite w hw v where
  index := s.index (.turn (P.turn i.val)) (P.turn_mem_codes i.val hi)
  code := P.turn i.val
  code_eq := congrArg Prod.snd (s.get_index (.turn (P.turn i.val)) (P.turn_mem_codes i.val hi))
  perpendicular := P.turn_perpendicular w G i.val hi

theorem line_location (s : PathSite w hw v P) (i : Fin P.segments.length) :
    ((codes w v).get (s.line i).index).1 = s.location :=
  congrArg Prod.fst (s.get_index (.line (P.line i.val)) (P.line_mem_codes i.val i.isLt))

theorem turn_location (s : PathSite w hw v P) (G : P.Geometry w) (i : Fin P.segments.length)
    (hi : P.hasTurn i.val) : ((codes w v).get (s.turn G i hi).index).1 = s.location :=
  congrArg Prod.fst (s.get_index (.turn (P.turn i.val)) (P.turn_mem_codes i.val hi))

theorem local_mem {q : GridRouting.Point × CellPlan.Code} (hq : q ∈ CellPlan.cells v)
    {c : PrimitiveCode} (hc : c ∈ localCodes w q.2) : (q.1,c) ∈ codes w v := by
  unfold codes
  exact List.mem_flatMap.mpr ⟨q,hq,List.mem_map.mpr ⟨c,hc,rfl⟩⟩

/-- An ordinary source wire has the exact path used by the physical renderer. -/
def wire (q : GridRouting.Point) (a : CellPlan.Wire)
    (hq : (q,some (Sum.inr a)) ∈ CellPlan.cells v) : PathSite w hw v (wireSpec w a.2) where
  location := q
  member c hc := local_mem hq (by change c ∈ wireCodes w a.2; exact hc)

/-- Each source gate arm has the exact path used by the physical renderer. -/
def arm (q : GridRouting.Point) (g : CellPlan.Gate) (r : Fin 3)
    (hq : (q,some (Sum.inl g)) ∈ CellPlan.cells v) : PathSite w hw v (armSpec w g.2 r) where
  location := q
  member c hc := local_mem hq (by
    change c ∈ gateCodes w g.2
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨r,List.mem_finRange _,hc⟩)

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
