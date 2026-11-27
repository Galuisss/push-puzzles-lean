/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSlots

/-! Complete source and target ownership at actual neighboring ordinary cells. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles.SlotContacts


open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap

theorem wire_east (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (i : Labels (.inr a)) (j : Labels (.inr b)) (hx : r.1=p.1+1) (hy : r.2=p.2) :
    coordinates p (.inr a) (slots goal (.inr a) i)≠coordinates r (.inr b) (slots goal (.inr b) j) := by
  intro he
  have hh := east_wire_overlap p r a b _ _ hx hy he
  have hu : Used (.inr a) .east := wire_slots_face a goal .east i hh.1
  obtain ⟨e,hca⟩ := wire_code ha
  obtain ⟨f,hcb⟩ := wire_code hb
  have hn : neighbor .east p=some r := by
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hx.symm,hy.symm⟩
  obtain ⟨hef,hflow⟩ := CellPlan.wire_adjacent v hP hT hn hca hcb ((used_key ha .east).mp hu)
  have hphase : wirePhase a goal=wirePhase b goal := by
    rw [wire_phase hca goal,wire_phase hcb goal,hef]
  have hsa := wire_slots_bounds a goal i
  have hsb := wire_slots_bounds b goal j
  rw [←hphase] at hsb
  apply SlotBounds.wire_east a.1 b.1 (wirePhase a goal)
    (((slots goal (.inr a) i).1.val),((slots goal (.inr a) i).2.val))
    (((slots goal (.inr b) j).1.val),((slots goal (.inr b) j).2.val)) hsa hsb hflow
  have hex := congrArg Prod.fst he
  have hey := congrArg Prod.snd he
  dsimp only [coordinates,offset,pad] at hex hey
  rw [hx,Nat.mul_add,Nat.mul_one] at hex
  rw [hy] at hey
  apply Prod.ext <;> dsimp only <;> omega

theorem wire_south (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (i : Labels (.inr a)) (j : Labels (.inr b)) (hx : r.1=p.1) (hy : r.2=p.2+1) :
    coordinates p (.inr a) (slots goal (.inr a) i)≠coordinates r (.inr b) (slots goal (.inr b) j) := by
  intro he
  have hh := south_wire_overlap p r a b _ _ hx hy he
  have hu : Used (.inr a) .south := wire_slots_face a goal .south i hh.1
  obtain ⟨e,hca⟩ := wire_code ha
  obtain ⟨f,hcb⟩ := wire_code hb
  have hn : neighbor .south p=some r := by
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hx.symm,hy.symm⟩
  obtain ⟨hef,hflow⟩ := CellPlan.wire_adjacent v hP hT hn hca hcb ((used_key ha .south).mp hu)
  have hphase : wirePhase a goal=wirePhase b goal := by
    rw [wire_phase hca goal,wire_phase hcb goal,hef]
  have hsa := wire_slots_bounds a goal i
  have hsb := wire_slots_bounds b goal j
  rw [←hphase] at hsb
  apply SlotBounds.wire_south a.1 b.1 (wirePhase a goal)
    (((slots goal (.inr a) i).1.val),((slots goal (.inr a) i).2.val))
    (((slots goal (.inr b) j).1.val),((slots goal (.inr b) j).2.val)) hsa hsb hflow
  have hex := congrArg Prod.fst he
  have hey := congrArg Prod.snd he
  dsimp only [coordinates,offset,pad] at hex hey
  rw [hy,Nat.mul_add,Nat.mul_one] at hey
  rw [hx] at hex
  apply Prod.ext <;> dsimp only <;> omega

theorem gate_wire (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r)
    {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (i : Labels (.inl g)) (j : Labels (.inr a))
    (hf : GateTileRouting.FullGateBoundary.InFrame d
      ((slots goal (.inl g) i).1.val,(slots goal (.inl g) i).2.val)) :
    coordinates p (.inl g) (slots goal (.inl g) i)≠coordinates r (.inr a) (slots goal (.inr a) j) := by
  obtain ⟨role,prev,hd,hpoint⟩ := gate_slots_frame g goal d i hf
  obtain ⟨b,hgc⟩ := gate_code hg
  obtain ⟨hgv,hgs⟩ := CellPlan.gate_sound hgc
  subst g
  obtain ⟨hmem,hbp⟩ := Raster.vertexAt_sound hgv
  obtain ⟨e,hac⟩ := wire_code ha
  have hd' : b.portDirection role=d := hd
  have hn' : neighbor (b.portDirection role) (refinePoint b.point)=some r := by
    rw [hd',hbp]
    exact hn
  obtain ⟨hedge,hflow⟩ := CellPlan.gate_adjacent v hP hT hmem role hn' hac
  have hphase : gatePhase (gateTileState (b,v.2)) goal role=
      if (gateTileState (b,v.2)).incoming.get role then !(wirePhase a goal) else wirePhase a goal := by
    rw [gateTileState_incoming,wire_phase hac goal,←hedge]
    exact gate_phase v b goal role
  have hflow' : if (gateTileState (b,v.2)).incoming.get role then Catalog.targetDirection a.1=d.opposite
      else Catalog.sourceDirection a.1=d := by
    rw [gateTileState_incoming,←hd']
    exact hflow
  rw [hphase] at hpoint
  have hgap := SlotBounds.gate_wire d ((gateTileState (b,v.2)).incoming.get role) (wirePhase a goal)
    prev a.1 p r ((slots goal (.inr a) j).1.val,(slots goal (.inr a) j).2.val) hn
    (wire_slots_bounds a goal j) hflow'
  intro he
  apply hgap
  have hpx := congrArg Prod.fst hpoint
  have hpy := congrArg Prod.snd hpoint
  dsimp only at hpx hpy
  change (strideX*p.1+(slots goal (.inl (gateTileState (b,v.2))) i).1.val,
    strideY*p.2+(slots goal (.inl (gateTileState (b,v.2))) i).2.val)=
      (strideX*r.1+1+(slots goal (.inr a) j).1.val,strideY*r.2+1+(slots goal (.inr a) j).2.val) at he
  rw [hpx,hpy] at he
  exact he

end PushPuzzle.PushFS.Reduction.PhysicalTiles.SlotContacts
