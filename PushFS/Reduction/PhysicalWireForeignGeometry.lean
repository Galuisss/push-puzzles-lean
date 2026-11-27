/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGateForeignGeometry
public import PushFS.Reduction.PhysicalGatePreparedGeometry
public import PushFS.Gadgets.Wires.Catalog.ExteriorGeometry
public import PushFS.Gadgets.Wires.Catalog.PreparedMasks

/-! Foreign canonical slots at actual ordinary-cell seams occupy only the real native external collars. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

private theorem wire_neighbor_mask (d : Direction) (k l : Catalog.Kind) (a : Bool)
    (p r : GridRouting.Point) (q s : Catalog.Cell) (hn : neighbor d p=some r)
    (hs : Catalog.SlotRegion l a s) (hf : CellPlan.Consecutive k l d)
    (he : coordinates p (.inr (k,false,false)) q=coordinates r (.inr (l,false,false)) s) :
    Catalog.WalkingMask k q := by
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  have hqx:=q.1.isLt
  have hqy:=q.2.isLt
  cases k <;> cases l <;> cases d <;> cases a
  all_goals simp only [CellPlan.Consecutive,Catalog.sourceDirection,Catalog.targetDirection,
    Direction.opposite,reduceCtorEq,and_true,and_false,or_true,or_false] at hf
  all_goals simp only [Catalog.SlotRegion,Catalog.SlotBounds,Bool.toNat_false,Bool.toNat_true] at hs
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [coordinates,offset,pad,strideX,strideY,Catalog.WalkingMask,Catalog.width,Catalog.height] at hx hy hqx hqy ⊢
  all_goals omega

private theorem gate_neighbor_mask (d : Direction) (inc a prev : Bool) (k : Catalog.Kind)
    (p r : GridRouting.Point) (q : Catalog.Cell) (hk : Catalog.Straight k)
    (hn : neighbor d p=some r)
    (hf : if inc then Catalog.targetDirection k=d.opposite else Catalog.sourceDirection k=d)
    (he : (strideX*p.1+(FullGateBoundary.endpointPoint d inc a prev).1,
      strideY*p.2+(FullGateBoundary.endpointPoint d inc a prev).2)=
      (strideX*r.1+1+q.1.val,strideY*r.2+1+q.2.val)) :
    Catalog.WalkingMask k q ∧(a=false→Catalog.PreparedMask k q) := by
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  have hqx:=q.1.isLt
  have hqy:=q.2.isLt
  rcases hk with rfl|rfl|rfl
  all_goals cases d <;> cases inc <;> cases a <;> cases prev
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite,
    Bool.false_eq_true,ite_true,ite_false,reduceCtorEq] at hf
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals simp only [FullGateBoundary.endpointPoint,Bool.toNat_false,Bool.toNat_true,ite_true] at hx hy
  all_goals simp only [Catalog.WalkingMask,Catalog.PreparedMask,Catalog.sourceCollar,Catalog.targetCollar,
    Prod.ext_iff,Fin.ext_iff,Catalog.width,Catalog.height] at hqx hqy ⊢
  all_goals dsimp only [strideX,strideY] at hx hy
  all_goals norm_num [Catalog.width,Catalog.height] at *
  all_goals try simp only [Fin.ext_iff,Fin.val_zero] at *
  all_goals dsimp only [Catalog.width,Catalog.height] at *
  all_goals omega

private theorem slot_corner (a : Catalog.Bitmap.Args) (goal : Bool) (l : Labels (.inr a))
    (hx : (slots goal (.inr a) l).1.val<5 ∨200000≤(slots goal (.inr a) l).1.val)
    (hy : (slots goal (.inr a) l).2.val<5 ∨198061≤(slots goal (.inr a) l).2.val) : False := by
  have hb:=wire_slots_bounds a goal l
  rcases a with ⟨k,a,b⟩
  cases k <;> dsimp only [Catalog.SlotRegion,Catalog.SlotBounds] at hb <;> omega

private theorem neighbor_of_close {p r : GridRouting.Point} (hne : p≠r)
    (hclose : p.1≤r.1+1 ∧r.1≤p.1+1 ∧p.2≤r.2+1 ∧r.2≤p.2+1)
    (haxis : p.1=r.1 ∨p.2=r.2) : ∃d,neighbor d p=some r := by
  rcases haxis with hx|hy
  · have hy : p.2≠r.2:=fun h=>hne (Prod.ext hx h)
    rcases lt_or_gt_of_ne hy with hy|hy
    · exact ⟨.south,by simp only [neighbor,Option.some.injEq,Prod.ext_iff]; exact ⟨hx,by omega⟩⟩
    · exact ⟨.north,by simp only [neighbor]; rw [ite_eq_right (show p.2≠0 by omega)]; exact congrArg some (Prod.ext hx (by omega))⟩
  · have hx : p.1≠r.1:=fun h=>hne (Prod.ext h hy)
    rcases lt_or_gt_of_ne hx with hx|hx
    · exact ⟨.east,by simp only [neighbor,Option.some.injEq,Prod.ext_iff]; exact ⟨by omega,hy⟩⟩
    · exact ⟨.west,by simp only [neighbor]; rw [ite_eq_right (show p.1≠0 by omega)]; exact congrArg some (Prod.ext (by omega) hy)⟩

/-- A foreign ordinary canonical slot visible in an actual wire lies on that wire's native walking mask. -/
private theorem wire_foreign_wire_neighbor (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (hne : p≠r) (goal : Bool) (l : Labels (.inr b)) (q : Catalog.Cell)
    (he : coordinates p (.inr a) q=coordinates r (.inr b) (slots goal (.inr b) l)) : ∃d,neighbor d p=some r ∧CellPlan.Consecutive a.1 b.1 d := by
  have hclose:=overlap_neighbors p r (.inr a) (.inr b) q _ he
  have haxis : p.1=r.1 ∨p.2=r.2:=by
    by_contra h
    push Not at h
    apply slot_corner b goal l
    · have hx:=congrArg Prod.fst he
      have hq:=q.1.isLt
      have hs:=(slots goal (.inr b) l).1.isLt
      dsimp only [coordinates,offset,pad,strideX,Catalog.width] at hx hq hs
      omega
    · have hy:=congrArg Prod.snd he
      have hq:=q.2.isLt
      have hs:=(slots goal (.inr b) l).2.isLt
      dsimp only [coordinates,offset,pad,strideY,Catalog.height] at hy hq hs
      omega
  obtain ⟨d,hn⟩:=neighbor_of_close hne hclose haxis
  have hu : Used (.inr a) d:=by
    have hface : Catalog.InFace (face d.opposite) (slots goal (.inr b) l):=by
      have hx:=congrArg Prod.fst he
      have hy:=congrArg Prod.snd he
      have hqx:=q.1.isLt
      have hqy:=q.2.isLt
      cases d <;> dsimp only [neighbor] at hn
      all_goals try split_ifs at hn
      all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
      all_goals dsimp only [coordinates,offset,pad,strideX,strideY,Catalog.InFace,face,Direction.opposite,Catalog.width,Catalog.height] at hx hy hqx hqy ⊢
      all_goals omega
    have hf:=wire_slots_face b goal _ l hface
    exact (used_reciprocal v hP hT hn ha hb).mpr hf
  obtain ⟨e,hac⟩:=wire_code ha
  obtain ⟨f,hbc⟩:=wire_code hb
  have hflow:=(CellPlan.wire_adjacent v hP hT hn hac hbc ((used_key ha d).mp hu)).2
  exact ⟨d,hn,hflow⟩
theorem wire_foreign_wire_mask (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (hne : p≠r) (goal : Bool) (l : Labels (.inr b)) (q : Catalog.Cell)
    (he : coordinates p (.inr a) q=coordinates r (.inr b) (slots goal (.inr b) l)) : Catalog.WalkingMask a.1 q := by
  obtain ⟨d,hn,hflow⟩:=wire_foreign_wire_neighbor v hP hT ha hb hne goal l q he
  exact wire_neighbor_mask d a.1 b.1 (wirePhase b goal) p r q _ hn (wire_slots_bounds b goal l) hflow he

private theorem wire_neighbor_prepared (d : Direction) (k l : Catalog.Kind) (a : Bool)
    (p r : GridRouting.Point) (q s : Catalog.Cell) (hn : neighbor d p=some r)
    (hs : Catalog.SlotRegion l a s) (hf : CellPlan.Consecutive k l d)
    (hsource : Catalog.sourceDirection k=d.opposite→a=false) (htarget : Catalog.targetDirection k=d→a=true)
    (he : coordinates p (.inr (k,false,false)) q=coordinates r (.inr (l,false,false)) s)
    (hfirst : ∀d,¬Adjacent d (Catalog.firstPoint l a) s) (hlast : ∀d,¬Adjacent d s (Catalog.lastPoint l a)) :
    Catalog.PreparedMask k q := by
  have hface : Catalog.InFace (face d.opposite) s:=by
    have hx:=congrArg Prod.fst he
    have hy:=congrArg Prod.snd he
    have hqx:=q.1.isLt
    have hqy:=q.2.isLt
    cases d <;> dsimp only [neighbor] at hn
    all_goals try split_ifs at hn
    all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
    all_goals dsimp only [coordinates,offset,pad,strideX,strideY,Catalog.InFace,face,Direction.opposite,Catalog.width,Catalog.height] at hx hy hqx hqy ⊢
    all_goals omega
  have hb:=Catalog.boundary_point l a (face d.opposite) s hs hface hfirst hlast
  clear hfirst hlast hs hface
  rcases hb with ⟨hface,rfl|⟨hb,rfl⟩⟩|⟨hface,rfl⟩
  all_goals have hx:=congrArg Prod.fst he
  all_goals have hy:=congrArg Prod.snd he
  all_goals have hqx:=q.1.isLt
  all_goals have hqy:=q.2.isLt
  all_goals cases k <;> cases l <;> cases d <;> cases a
  all_goals try cases hb
  all_goals simp only [CellPlan.Consecutive,Catalog.sourceDirection,Catalog.targetDirection,
    Catalog.sourceFace,Catalog.targetFace,face,Direction.opposite,reduceCtorEq,and_true,and_false,or_true,or_false] at hf hface
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite,reduceCtorEq,
    false_implies,true_implies] at hsource htarget
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [coordinates,offset,pad,strideX,strideY] at hx hy
  all_goals simp only [Catalog.PreparedMask,Catalog.sourceCollar,Catalog.targetCollar,Prod.ext_iff,Fin.ext_iff,
    Catalog.width,Catalog.height] at hqx hqy ⊢
  all_goals norm_num [Catalog.firstPoint,Catalog.secondPoint,Catalog.lastPoint,Catalog.width,Catalog.height] at hx hy hqx hqy hsource htarget ⊢
  all_goals try simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

/-- Prepared real predecessor/successor phases leave exactly the two strict native collar slots. -/
theorem wire_foreign_wire_prepared (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {a b : Catalog.Bitmap.Args}
    (ha : key (CellPlan.cell (v,p))=some (.inr a)) (hb : key (CellPlan.cell (v,r))=some (.inr b))
    (hne : p≠r) (goal : Bool) (l : Labels (.inr b)) (q : Catalog.Cell)
    (hsource : neighbor (Catalog.sourceDirection a.1).opposite p=some r→wirePhase b goal=false)
    (htarget : neighbor (Catalog.targetDirection a.1) p=some r→wirePhase b goal=true)
    (he : coordinates p (.inr a) q=coordinates r (.inr b) (slots goal (.inr b) l)) : Catalog.PreparedMask a.1 q := by
  obtain ⟨d,hn,hflow⟩:=wire_foreign_wire_neighbor v hP hT ha hb hne goal l q he
  apply wire_neighbor_prepared d a.1 b.1 (wirePhase b goal) p r q _ hn (wire_slots_bounds b goal l) hflow ?_ ?_ he
    (wire_first_sparse b goal l) (wire_last_sparse b goal l)
  · intro hd
    apply hsource
    rw [hd,Direction.opposite_opposite]
    exact hn
  · intro hd
    exact htarget (hd.symm ▸hn)

private theorem gate_slot_frame {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    {d : Direction} (hn : neighbor d p=some r) (goal : Bool) (l : Labels (.inl g)) (q : Catalog.Cell)
    (he : coordinates p (.inl g) (slots goal (.inl g) l)=coordinates r (.inr a) q) :
    FullGateBoundary.InFrame d ((slots goal (.inl g) l).1.val,(slots goal (.inl g) l).2.val) := by
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  have hqx:=q.1.isLt
  have hqy:=q.2.isLt
  cases d <;> dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [coordinates,offset,pad,strideX,strideY,FullGateBoundary.InFrame,Catalog.width,Catalog.height] at hx hy hqx hqy ⊢
  all_goals omega

/-- An actual neighboring gate supplies only one real external port's canonical collar boxes. -/
theorem wire_foreign_gate_data (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (goal : Bool) (l : Labels (.inl g)) (q : Catalog.Cell)
    (he : coordinates p (.inl g) (slots goal (.inl g) l)=coordinates r (.inr a) q) :
    ∃role : Fin 3,neighbor (PortAnnulus.outerDirection (g.key role).2) p=some r ∧
      Catalog.WalkingMask a.1 q ∧(gatePhase g goal role=false→Catalog.PreparedMask a.1 q) := by
  have hne : p≠r:=by intro h; subst r; cases same_position_key hg ha
  have hc:=overlap_neighbors p r (.inl g) (.inr a) _ q he
  have haxis:=gate_wire_overlap_axis hg ha _ q he
  obtain ⟨d,hn⟩:=neighbor_of_close hne hc (haxis.elim (fun h=>Or.inl h.symm) (fun h=>Or.inr h.symm))
  obtain ⟨role,prev,hd,hpoint⟩:=gate_slots_frame g goal d l (gate_slot_frame hn goal l q he)
  have hepoint : (strideX*p.1+(FullGateBoundary.endpointPoint d (g.incoming.get role) (gatePhase g goal role) prev).1,
      strideY*p.2+(FullGateBoundary.endpointPoint d (g.incoming.get role) (gatePhase g goal role) prev).2)=
      (strideX*r.1+1+q.1.val,strideY*r.2+1+q.2.val) :=
    (congrArg (fun q : ℕ×ℕ=>(strideX*p.1+q.1,strideY*p.2+q.2)) hpoint).symm.trans he
  refine ⟨role,?_,gate_neighbor_mask d (g.incoming.get role) (gatePhase g goal role) prev a.1 p r q
    (gate_neighbor_straight v hP hT hn hg ha) hn (gate_neighbor_flow v hP hT hg ha role hd hn) hepoint⟩
  rw [hd]
  exact hn
end PushPuzzle.PushFS.Reduction.PhysicalTiles
