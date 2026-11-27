/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateExternalMaskCoordinates
public import PushFS.Reduction.PhysicalCanonicalEndpoints
public import PushFS.Reduction.PhysicalSlotSeparation

/-! Every actual foreign source or target wire box visible in a complete gate lies on its endpoint walking mask. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL Plan Gadgets.Wires PhysicalBitmap GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

private theorem neighbor_collar (d : Direction) (inc a : Bool) (k : Catalog.Kind)
    (p r q s : ℕ×ℕ) (hk : Catalog.Straight k) (hn : neighbor d p=some r)
    (hs : Catalog.SlotBounds k a s.1 s.2)
    (hflow : if inc then Catalog.targetDirection k=d.opposite else Catalog.sourceDirection k=d)
    (he : (strideX*p.1+q.1,strideY*p.2+q.2)=(strideX*r.1+1+s.1,strideY*r.2+1+s.2)) :
    NeighborCollar d inc q := by
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  rcases hk with rfl|rfl|rfl
  all_goals cases d <;> cases inc <;> cases a
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite,
    Bool.false_eq_true,ite_true,ite_false,reduceCtorEq] at hflow
  all_goals simp only [Catalog.SlotBounds,Bool.toNat_false,Bool.toNat_true] at hs
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [NeighborCollar,Bool.toNat_false,Bool.toNat_true,strideX,strideY] at hx hy ⊢
  all_goals omega

theorem gate_neighbor_flow (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args} {d : Direction}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (role : Fin 3) (hd : PortAnnulus.outerDirection (g.key role).2=d) (hn : neighbor d p=some r) :
    if g.incoming.get role then Catalog.targetDirection a.1=d.opposite else Catalog.sourceDirection a.1=d := by
  obtain ⟨b,hgc⟩:=gate_code hg
  obtain ⟨hgv,hgs⟩:=CellPlan.gate_sound hgc
  subst g
  obtain ⟨hmem,hbp⟩:=Raster.vertexAt_sound hgv
  obtain ⟨e,hac⟩:=wire_code ha
  have hd' : b.portDirection role=d:=hd
  have hn' : neighbor (b.portDirection role) (refinePoint b.point)=some r:=by rw [hd',hbp]; exact hn
  have hflow:=(CellPlan.gate_adjacent v hP hT hmem role hn' hac).2
  rw [gateTileState_incoming,←hd']
  exact hflow

private theorem neighbor_wire_mask (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args} {d : Direction}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (hn : neighbor d p=some r) (goal : Bool) (l : Labels (.inr a)) (q : GateTileRouting.C)
    (he : coordinates p (.inl g) q=coordinates r (.inr a) (slots goal (.inr a) l))
    (hf : Catalog.InFace6 (face d.opposite) (slots goal (.inr a) l)) : OuterMask g q := by
  have hu : Used (.inr a) d.opposite:=SlotSeparation.wire_six_face a.1 (wirePhase a goal) _ _ (wire_slots_bounds a goal l) hf
  obtain ⟨role,hd⟩:=(used_reciprocal v hP hT hn hg ha).mpr hu
  apply outer_mask_of_neighbor_collar g role q
  rw [hd]
  exact neighbor_collar d (g.incoming.get role) (wirePhase a goal) a.1 p r (q.1.val,q.2.val)
    ((slots goal (.inr a) l).1.val,(slots goal (.inr a) l).2.val) (gate_neighbor_straight v hP hT hn hg ha) hn (wire_slots_bounds a goal l)
    (gate_neighbor_flow v hP hT hg ha role hd hn) he

/-- A literal gate cell coinciding with any actual neighboring ordinary canonical slot belongs to the complete external endpoint mask. -/
theorem gate_foreign_wire_mask (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (goal : Bool) (l : Labels (.inr a)) (q : GateTileRouting.C)
    (he : coordinates p (.inl g) q=coordinates r (.inr a) (slots goal (.inr a) l)) : OuterMask g q := by
  have hne : p≠r:=by intro h; subst r; cases same_position_key hg ha
  have hn:=overlap_neighbors p r (.inl g) (.inr a) q (slots goal (.inr a) l) he
  rcases gate_wire_overlap_axis hg ha q (slots goal (.inr a) l) he with hx|hy
  · have hny : p.2≠r.2:=fun hy=>hne (Prod.ext hx.symm hy)
    rcases lt_or_gt_of_ne hny with hy|hy
    · have hcoords:=south_gate_wire_overlap p r g a q (slots goal (.inr a) l) hx (by omega) he
      have hn' : neighbor .south p=some r:=by simp only [neighbor,Option.some.injEq,Prod.ext_iff]; exact ⟨hx.symm,by omega⟩
      exact neighbor_wire_mask v hP hT hg ha hn' goal l q he hcoords.2.1
    · have hcoords:=south_wire_gate_overlap r p a g (slots goal (.inr a) l) q hx.symm (by omega) he.symm
      have hn' : neighbor .south r=some p:=by simp only [neighbor,Option.some.injEq,Prod.ext_iff]; exact ⟨hx,by omega⟩
      exact neighbor_wire_mask v hP hT hg ha (neighbor_reverse hn') goal l q he hcoords.1
  · have hnx : p.1≠r.1:=fun hx=>hne (Prod.ext hx hy.symm)
    rcases lt_or_gt_of_ne hnx with hx|hx
    · have hcoords:=east_gate_wire_overlap p r g a q (slots goal (.inr a) l) (by omega) hy he
      have hn' : neighbor .east p=some r:=by simp only [neighbor,Option.some.injEq,Prod.ext_iff]; exact ⟨by omega,hy.symm⟩
      exact neighbor_wire_mask v hP hT hg ha hn' goal l q he hcoords.2.1
    · have hcoords:=east_wire_gate_overlap r p a g (slots goal (.inr a) l) q (by omega) hy.symm he.symm
      have hn' : neighbor .east r=some p:=by simp only [neighbor,Option.some.injEq,Prod.ext_iff]; exact ⟨by omega,hy⟩
      exact neighbor_wire_mask v hP hT hg ha (neighbor_reverse hn') goal l q he hcoords.1

/-- A foreign ordinary cell meeting an annular line is the actual neighbor at that arm's external port. -/
theorem gate_line_foreign_neighbor (v : CellPlan.Source)
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (role : Fin 3) (j : Fin (curve (GateTileRouting.key g role)).length)
    (q : Cell (lineInput g role j).width (lineInput g role j).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (he : coordinates p (.inl g) ((lineEmbedding g role j).cells q)=coordinates r (.inr a) s) :
    neighbor (PortAnnulus.outerDirection (g.key role).2) p=some r := by
  have hne : p≠r:=by intro h; subst r; cases same_position_key hg ha
  let t:=(lineEmbedding g role j).cells q
  have hn:=overlap_neighbors p r (.inl g) (.inr a) t s he
  have owner (d : Direction) (hf : FullGateBoundary.InFrame d (t.1.val,t.2.val)) :
      PortAnnulus.outerDirection (g.key role).2=d:=by
    exact (FullGateBoundary.raw_owner g (lineIndex g role j) d
      ((lineRawIso (GateTileRouting.key g role) j.val j.isLt (Inventory.initialPhase g role) (Inventory.targetPhase g role)).cells q) hf).2
  rcases gate_wire_overlap_axis hg ha t s he with hx|hy
  · have hny : p.2≠r.2:=fun hy=>hne (Prod.ext hx.symm hy)
    rcases lt_or_gt_of_ne hny with hy|hy
    · have hh:=south_gate_wire_overlap p r g a t s hx (by omega) he
      rw [owner .south (by change 198061≤t.2.val; omega)]
      simp only [neighbor,Option.some.injEq,Prod.ext_iff]
      exact ⟨hx.symm,by omega⟩
    · have hh:=south_wire_gate_overlap r p a g s t hx.symm (by omega) he.symm
      rw [owner .north (by change t.2.val<7; omega)]
      apply neighbor_reverse (d:=.south)
      simp only [neighbor,Option.some.injEq,Prod.ext_iff]
      exact ⟨hx,by omega⟩
  · have hnx : p.1≠r.1:=fun hx=>hne (Prod.ext hx hy.symm)
    rcases lt_or_gt_of_ne hnx with hx|hx
    · have hh:=east_gate_wire_overlap p r g a t s (by omega) hy he
      rw [owner .east (by change 200000≤t.1.val; omega)]
      simp only [neighbor,Option.some.injEq,Prod.ext_iff]
      exact ⟨by omega,hy.symm⟩
    · have hh:=east_wire_gate_overlap r p a g s t (by omega) hy.symm he.symm
      rw [owner .west (by change t.1.val<7; omega)]
      apply neighbor_reverse (d:=.east)
      simp only [neighbor,Option.some.injEq,Prod.ext_iff]
      exact ⟨by omega,hy⟩

end PushPuzzle.PushFS.Reduction.PhysicalTiles
