/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalGateForeignGeometry
public import PushFS.Reduction.PhysicalProfileForeign
public import PushFS.Reduction.PhysicalGatePlacement

/-! Complete gate walking collars instantiated by the actual mixed foreign inventory on the whole board. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileOutside StorageAtlas.profileFixed

private theorem matching_marks {I : Instance} {L : Type} [Fintype L] (M : SlotMatching I L) (goal : Bool)
    (q : Cell I.width I.height) (hq : q∈(if goal then I.board.goals else I.initial.boxes)) :
    ∃l,(if goal then M.target l else M.source l)=q := by
  cases goal
  · change q∈I.initial.boxes at hq
    rw [←M.source_image] at hq
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hq
    exact ⟨l,he⟩
  · change q∈I.board.goals at hq
    rw [←M.target_image] at hq
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hq
    exact ⟨l,he⟩

noncomputable def gateProfileFixed (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1) : Finset GateTileRouting.C :=
  Finset.univ.filter fun p=>(gateEmbedding v g hg).cells p∈
    (atlas v hP hT).profileOutside f (numbering v (gateIndex v g hg))

theorem mem_gateProfileFixed (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1) (p : GateTileRouting.C) :
    p∈gateProfileFixed v hP hT f g hg ↔(gateEmbedding v g hg).cells p∈
      (atlas v hP hT).profileOutside f (numbering v (gateIndex v g hg)) := by
  simp only [gateProfileFixed,Finset.mem_filter,Finset.mem_univ,true_and]

attribute [local irreducible] gateProfileFixed

/-- Every actual foreign box visible in a complete gate belongs to its true external endpoint mask, for arbitrary independent source/target choices. -/
theorem gate_profile_fixed_mask (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1)
    (p : GateTileRouting.C)
    (hp : p∈gateProfileFixed v hP hT f g hg) :
    OuterMask (gateTileState (g,v.2)) p := by
  have hp':=(mem_gateProfileFixed v hP hT f g hg p).mp hp
  obtain ⟨j,hji,q,hq,he⟩:=profile_foreign v hP hT f (gateIndex v g hg) p hp'
  rcases j with ⟨⟨pos,h|a⟩,hj⟩
  · have hpos:=PhysicalTiles.gate_gate_overlap (key_eq (gateIndex v g hg)) hj p q he
    exact (hji (position_injective hpos.symm)).elim
  · obtain ⟨l,hl⟩:=matching_marks (PhysicalTiles.matching (.inr a)) (f (numbering v ⟨(pos,.inr a),hj⟩)) q hq
    have hslots : PhysicalTiles.slots (f (numbering v ⟨(pos,.inr a),hj⟩)) (.inr a) l=q:=by
      cases hb : f (numbering v ⟨(pos,.inr a),hj⟩) <;>
        simpa only [PhysicalTiles.slots,hb,Bool.false_eq_true,ite_false,ite_true] using hl
    rw [←hslots] at he
    exact PhysicalTiles.gate_foreign_wire_mask v hP hT (key_eq (gateIndex v g hg)) hj _ l p he

end PushPuzzle.PushFS.Reduction.PhysicalInventory
