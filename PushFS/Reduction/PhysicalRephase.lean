/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSlots

/-! Canonical source-orientation assignments on the fixed actual physical tile identities. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Plan Gadgets.Wires
set_option maxRecDepth 65536

abbrev Payload := CellPlan.Gate ⊕ CellPlan.Wire

def payloadKey : Payload→Key
  | .inl g=>.inl g.2
  | .inr w=>.inr w.2

theorem key_some (c : Payload) : key (some c)=some (payloadKey c) := by cases c <;> rfl

/-- Reassign the original edge bits while retaining every geometric choice and every auxiliary identity. -/
def rephase (c : Payload) (a b : List Bool) : Key :=
  match c with
  | .inl (v,g)=>.inl {g with core:={g.core with initial:=gateSignals (v.ports,a),target:=gateSignals (v.ports,b)}}
  | .inr (e,(k,_,_))=>.inr (k,!(a.getD e false),!(b.getD e false))

def rephaseCode (c : CellPlan.Code) (a b : List Bool) : CellPlan.Code :=
  match c with
  | none=>none
  | some (.inl (v,g))=>some (.inl (v,{g with core:={g.core with initial:=gateSignals (v.ports,a),target:=gateSignals (v.ports,b)}}))
  | some (.inr (e,(k,_,_)))=>some (.inr (e,(k,!(a.getD e false),!(b.getD e false))))

theorem key_rephaseCode_some (c : Payload) (a b : List Bool) :
    key (rephaseCode (some c) a b)=some (rephase c a b) := by cases c <;> rfl

/-- The actual source compiler changes only canonical phases when its orientation lists change. -/
theorem rephase_cell (v : CellPlan.Source) (p : NCL.GridRouting.Point) (a b : List Bool) :
    rephaseCode (CellPlan.cell (v,p)) a b=CellPlan.cell ((v.1,(a,b)),p) := by
  cases hv : Raster.vertexAt (v.1,p) with
  | some g => simp only [CellPlan.cell,hv,Option.elim_some,gateTileState,rephaseCode]
  | none =>
    cases he : Raster.owner (v.1,p) with
    | none => simp only [CellPlan.cell,hv,CellPlan.ordinary,he,Option.elim_none,rephaseCode]
    | some e =>
      cases hk : Raster.wireAt (v.1,(e,p)) <;>
        simp only [CellPlan.cell,hv,CellPlan.ordinary,he,CellPlan.wireData,hk,
          Option.elim_none,Option.elim_some,Option.map_none,Option.map_some,rephaseCode]

theorem rephase_pad (c : Payload) (a b : List Bool) : pad (rephase c a b)=pad (payloadKey c) := by
  cases c <;> rfl

end PushPuzzle.PushFS.Reduction.PhysicalTiles
