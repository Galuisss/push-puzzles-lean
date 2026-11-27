/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSlotSeparation
public import PushFS.Reduction.PhysicalCanonicalEndpoints

/-! Complete one-cell separation of canonical source/goal slots across real source-grid contacts. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles.SeparatedContacts


open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap

theorem wire_east (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (i : Labels (.inr a)) (j : Labels (.inr b)) (hx : r.1=p.1+1) (hy : r.2=p.2) :
    ¬Nearby 1 (coordinates p (.inr a) (slots goal (.inr a) i)) (coordinates r (.inr b) (slots goal (.inr b) j)) := by
  intro he
  have hlocal : Nearby 1
      ((slots goal (.inr a) i).1.val,(slots goal (.inr a) i).2.val)
      (strideX+(slots goal (.inr b) j).1.val,(slots goal (.inr b) j).2.val) := by
    dsimp only [Nearby,coordinates,offset,pad] at he
    rw [hx,hy,Nat.mul_add,Nat.mul_one] at he
    dsimp only [Nearby]
    omega
  have hface : Catalog.InFace6 .east (slots goal (.inr a) i) := by
    change 199999≤(slots goal (.inr a) i).1.val
    dsimp only [Nearby,strideX] at hlocal
    omega
  have hu : Used (.inr a) .east := SlotSeparation.wire_six_face a.1 (wirePhase a goal) .east _ (wire_slots_bounds a goal i) hface
  obtain ⟨e,hca⟩ := wire_code ha
  obtain ⟨f,hcb⟩ := wire_code hb
  have hn : neighbor .east p=some r := by
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hx.symm,hy.symm⟩
  obtain ⟨hef,hflow⟩ := CellPlan.wire_adjacent v hP hT hn hca hcb ((used_key ha .east).mp hu)
  have hphase : wirePhase a goal=wirePhase b goal := by rw [wire_phase hca goal,wire_phase hcb goal,hef]
  have hsb := wire_slots_bounds b goal j
  rw [←hphase] at hsb
  exact SlotSeparation.wire_east a.1 b.1 (wirePhase a goal)
    ((slots goal (.inr a) i).1.val,(slots goal (.inr a) i).2.val)
    ((slots goal (.inr b) j).1.val,(slots goal (.inr b) j).2.val) (wire_slots_bounds a goal i) hsb hflow hlocal

theorem wire_south (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (i : Labels (.inr a)) (j : Labels (.inr b)) (hx : r.1=p.1) (hy : r.2=p.2+1) :
    ¬Nearby 1 (coordinates p (.inr a) (slots goal (.inr a) i)) (coordinates r (.inr b) (slots goal (.inr b) j)) := by
  intro he
  have hlocal : Nearby 1
      ((slots goal (.inr a) i).1.val,(slots goal (.inr a) i).2.val)
      ((slots goal (.inr b) j).1.val,strideY+(slots goal (.inr b) j).2.val) := by
    dsimp only [Nearby,coordinates,offset,pad] at he
    rw [hx,hy,Nat.mul_add,Nat.mul_one] at he
    dsimp only [Nearby]
    omega
  have hface : Catalog.InFace6 .south (slots goal (.inr a) i) := by
    change 198060≤(slots goal (.inr a) i).2.val
    dsimp only [Nearby,strideY] at hlocal
    omega
  have hu : Used (.inr a) .south := SlotSeparation.wire_six_face a.1 (wirePhase a goal) .south _ (wire_slots_bounds a goal i) hface
  obtain ⟨e,hca⟩ := wire_code ha
  obtain ⟨f,hcb⟩ := wire_code hb
  have hn : neighbor .south p=some r := by
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hx.symm,hy.symm⟩
  obtain ⟨hef,hflow⟩ := CellPlan.wire_adjacent v hP hT hn hca hcb ((used_key ha .south).mp hu)
  have hphase : wirePhase a goal=wirePhase b goal := by rw [wire_phase hca goal,wire_phase hcb goal,hef]
  have hsb := wire_slots_bounds b goal j
  rw [←hphase] at hsb
  exact SlotSeparation.wire_south a.1 b.1 (wirePhase a goal)
    ((slots goal (.inr a) i).1.val,(slots goal (.inr a) i).2.val)
    ((slots goal (.inr b) j).1.val,(slots goal (.inr b) j).2.val) (wire_slots_bounds a goal i) hsb hflow hlocal

theorem gate_wire (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r)
    {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (i : Labels (.inl g)) (j : Labels (.inr a)) :
    ¬Nearby 1 (coordinates p (.inl g) (slots goal (.inl g) i)) (coordinates r (.inr a) (slots goal (.inr a) j)) := by
  intro he
  have hf := gate_wire_near_frame p r g a d hn _ _ he
  obtain ⟨inc,prev,hpoint,hflow⟩ := gate_canonical_endpoint v hP hT goal hn hg ha i hf
  apply SlotSeparation.gate_wire d inc (wirePhase a goal) prev a.1 p r
    ((slots goal (.inr a) j).1.val,(slots goal (.inr a) j).2.val) hn (wire_slots_bounds a goal j) hflow
  have hpx := congrArg Prod.fst hpoint
  have hpy := congrArg Prod.snd hpoint
  dsimp only at hpx hpy
  change Nearby 1
    (strideX*p.1+(slots goal (.inl g) i).1.val,strideY*p.2+(slots goal (.inl g) i).2.val)
    (strideX*r.1+1+(slots goal (.inr a) j).1.val,strideY*r.2+1+(slots goal (.inr a) j).2.val) at he
  rw [hpx,hpy] at he
  exact he

end PushPuzzle.PushFS.Reduction.PhysicalTiles.SeparatedContacts
