/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPrimitiveGeometry

/-! Erasing only normal inventory phases retains the exact emitted primitive geometry. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

def eraseGatePhases (g : GateTileState) : GateTileState :=
  {g with core := {g.core with initial := ⟨false,false,false⟩, target := ⟨false,false,false⟩}}

namespace PrimitiveCode

/-- Initial and target phases are the only changing fields of a fixed source primitive. -/
def erasePhases : PrimitiveCode → PrimitiveCode
  | .core g => .core (eraseGatePhases g)
  | .line c => .line {c with initial := false,target := false}
  | .turn c => .turn {c with initial := false,target := false}

def eraseInitial : PrimitiveCode → PrimitiveCode
  | .core g => .core {g with core := {g.core with initial := ⟨false,false,false⟩}}
  | .line c => .line {c with initial := false}
  | .turn c => .turn {c with initial := false}

/-- Literal placed wall coordinates of the actual semantic primitive. -/
def wallPoints (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) : Finset (ℕ × ℕ) :=
  (c.instanceOf w hw).board.walls.image (c.world w hw)

def targetPoints (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) : Finset (ℕ × ℕ) :=
  (c.instanceOf w hw).board.goals.image (c.world w hw)

theorem eraseInitial_targetPoints (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    c.eraseInitial.targetPoints w hw = c.targetPoints w hw := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind <;> rfl
  | line c => rfl
  | turn c => rfl

theorem erasePhases_wallPoints (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    c.erasePhases.wallPoints w hw = c.wallPoints w hw := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind <;> rfl
  | line c => rfl
  | turn c => rfl

end PrimitiveCode

private theorem pathCodes_erase_phases (segments : List Segment)
    (initialSide targetSide keepEndpoint a b a' b' : Bool) :
    (pathCodes segments initialSide targetSide keepEndpoint a b).map PrimitiveCode.erasePhases =
      (pathCodes segments initialSide targetSide keepEndpoint a' b').map PrimitiveCode.erasePhases := by
  simp only [pathCodes,List.map_flatMap,List.map_append]
  congr 1
  funext i
  split_ifs <;> rfl

theorem gateCodes_erase_phases (w : ℕ) (kind : Bool) (incoming : PushFS.Gadgets.Gates.Signals)
    (pattern rotation : Fin 3) (s t s' t' : PushFS.Gadgets.Gates.Signals) :
    (gateCodes w ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩).map PrimitiveCode.erasePhases =
      (gateCodes w ⟨⟨kind,s',t'⟩,incoming,pattern,rotation⟩).map PrimitiveCode.erasePhases := by
  simp only [gateCodes,List.map_cons,List.map_flatMap]
  congr 1
  congr 1
  funext role
  exact pathCodes_erase_phases _ _ _ _ _ _ _ _

theorem wireCodes_erase_phases (w : ℕ) (kind : Catalog.Kind) (a b a' b' : Bool) :
    (wireCodes w (kind,a,b)).map PrimitiveCode.erasePhases =
      (wireCodes w (kind,a',b')).map PrimitiveCode.erasePhases :=
  pathCodes_erase_phases _ _ _ _ _ _ _ _

private theorem pathCodes_erase_initial (segments : List Segment)
    (initialSide targetSide keepEndpoint a a' b : Bool) :
    (pathCodes segments initialSide targetSide keepEndpoint a b).map PrimitiveCode.eraseInitial =
      (pathCodes segments initialSide targetSide keepEndpoint a' b).map PrimitiveCode.eraseInitial := by
  simp only [pathCodes,List.map_flatMap,List.map_append]
  congr 1
  funext i
  split_ifs <;> rfl

theorem gateCodes_erase_initial (w : ℕ) (kind : Bool) (incoming : PushFS.Gadgets.Gates.Signals)
    (pattern rotation : Fin 3) (s s' t : PushFS.Gadgets.Gates.Signals) :
    (gateCodes w ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩).map PrimitiveCode.eraseInitial =
      (gateCodes w ⟨⟨kind,s',t⟩,incoming,pattern,rotation⟩).map PrimitiveCode.eraseInitial := by
  simp only [gateCodes,List.map_cons,List.map_flatMap]
  congr 1
  congr 1
  funext role
  exact pathCodes_erase_initial _ _ _ _ _ _ _

theorem wireCodes_erase_initial (w : ℕ) (kind : Catalog.Kind) (a a' b : Bool) :
    (wireCodes w (kind,a,b)).map PrimitiveCode.eraseInitial =
      (wireCodes w (kind,a',b)).map PrimitiveCode.eraseInitial :=
  pathCodes_erase_initial _ _ _ _ _ _ _

end PushPuzzle.PushS.FiniteRouting
