/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Transit
public import PushFS.Walking

/-! Literal outer-lane access to the real short-turn seam portals, with either phase of all neighboring boxes. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def nearPortal (k : Kind) : Cell (width k) (height k) :=
  (⟨sourceX k-1,by cases k <;> decide⟩,⟨1,by cases k <;> decide⟩)

def farPortal (k : Kind) : Cell (width k) (height k) :=
  (⟨1,by cases k <;> decide⟩,⟨lastY k+1,by cases k <;> decide⟩)

private theorem edge_free_checked : ∀k : Kind,∀p : Cell (width k) (height k),p.2.val=1 ∨p.1.val=1 →
    (template k).wall p=false ∧(template k).reserved p=false := by decide +kernel

private theorem reserved_floor_checked : ∀k : Kind,∀p : Cell (width k) (height k),
    (template k).reserved p=true →(template k).wall p=false := by decide +kernel

private theorem corner_near : ∀k : Kind,((template k).corner 1).2.val=1 := by decide +kernel
private theorem corner_far : ∀k : Kind,((template k).corner 2).1.val=1 := by decide +kernel

private theorem allNeighbors_not_edge (k : Kind) (p : Cell (width k) (height k))
    (hp : p.2.val=1 ∨p.1.val=1) : p∉allNeighbors k := by
  intro hm
  have hh:=(Finset.mem_filter.mp hm).2
  cases k <;> dsimp only [allNeighbors,sourceX,lastY] at hh <;> omega

namespace TransitFrame
variable {k : Kind} {W H : ℕ} {e : GridEmbedding (width k) (height k) W H} {B : Board W H}
    {outside : Finset (Cell W H)} (f : TransitFrame k e B outside)

include f in
private theorem fixed_floor : Disjoint (Polyline.Frame.fixed e outside) (template k).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  exact Finset.disjoint_left.mp f.outside_floor ((Polyline.Frame.mem_fixed _ _ p).mp hp) ((f.walls p).mpr hw)

private theorem actual_floor (actual : Finset (Cell (width k) (height k))) (ha : actual⊆(template k).reservedCells) :
    Disjoint actual (template k).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  have hf:=reserved_floor_checked k p (((template k).mem_reserved p).mp (ha hp))
  exact Bool.noConfusion (hf.symm.trans (((template k).mem_walls p).mp hw))

include f in
private theorem edge_free (actual : Finset (Cell (width k) (height k))) (ha : actual⊆(template k).reservedCells)
    (p : Cell (width k) (height k)) (hp : p.2.val=1 ∨p.1.val=1) :
    Free ((template k).board ∅) (actual∪Polyline.Frame.fixed e outside) p := by
  have hh:=edge_free_checked k p hp
  refine ⟨?_,?_⟩
  · intro hw
    exact Bool.noConfusion (hh.1.symm.trans (((template k).mem_walls p).mp hw))
  · intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · exact Bool.noConfusion (hh.2.symm.trans (((template k).mem_reserved p).mp (ha hm)))
    · exact allNeighbors_not_edge k p hp (f.collar hm)

include f in
private theorem outer_row (actual : Finset (Cell (width k) (height k))) (ha : actual⊆(template k).reservedCells)
    (p q : Cell (width k) (height k)) (hp : p.2.val=1) (hq : q.2.val=1) :
    Reachable B (some 1) (e.extend outside ⟨p,actual⟩) (e.extend outside ⟨q,actual⟩) := by
  have hpath : Reachable ((template k).board ∅) (some 1)
      ⟨p,actual∪Polyline.Frame.fixed e outside⟩ ⟨q,actual∪Polyline.Frame.fixed e outside⟩ := by
    have he : p.2=q.2:=Fin.ext (hp.trans hq.symm)
    have hp' : p=(p.1,p.2):=rfl
    have hq' : q=(q.1,p.2):=Prod.ext rfl he.symm
    rw [hq']
    apply walk_horizontal (Finset.disjoint_union_left.mpr ⟨actual_floor actual ha,f.fixed_floor⟩)
    intro x _ _
    exact f.edge_free actual ha (x,p.2) (Or.inl hp)
  exact e.reachable_withFixed f.walls (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor hpath

include f in
private theorem outer_column (actual : Finset (Cell (width k) (height k))) (ha : actual⊆(template k).reservedCells)
    (p q : Cell (width k) (height k)) (hp : p.1.val=1) (hq : q.1.val=1) :
    Reachable B (some 1) (e.extend outside ⟨p,actual⟩) (e.extend outside ⟨q,actual⟩) := by
  have hpath : Reachable ((template k).board ∅) (some 1)
      ⟨p,actual∪Polyline.Frame.fixed e outside⟩ ⟨q,actual∪Polyline.Frame.fixed e outside⟩ := by
    have he : p.1=q.1:=Fin.ext (hp.trans hq.symm)
    have hq' : q=(p.1,q.2):=Prod.ext he.symm rfl
    rw [hq']
    apply walk_vertical (Finset.disjoint_union_left.mpr ⟨actual_floor actual ha,f.fixed_floor⟩)
    intro y _ _
    exact f.edge_free actual ha (p.1,y) (Or.inr hp)
  exact e.reachable_withFixed f.walls (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor hpath

include f in
/-- The real incoming seam portal is reachable from the short-turn hub with every physical box fixed. -/
theorem near_portal (actual : Finset (Cell (width k) (height k))) (ha : actual⊆(template k).reservedCells) :
    Reachable B (some 1) (e.extend outside ⟨(template k).hub,actual⟩) (e.extend outside ⟨nearPortal k,actual⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨nearPortal k,actual⟩) (e.extend outside ⟨(template k).hub,actual⟩) := by
  have hh:=f.corners actual ha 1
  exact ⟨hh.1.trans (f.outer_row actual ha _ _ (corner_near k) rfl),
    (f.outer_row actual ha _ _ rfl (corner_near k)).trans hh.2⟩

include f in
/-- The real outgoing seam portal is reachable from the short-turn hub with every physical box fixed. -/
theorem far_portal (actual : Finset (Cell (width k) (height k))) (ha : actual⊆(template k).reservedCells) :
    Reachable B (some 1) (e.extend outside ⟨(template k).hub,actual⟩) (e.extend outside ⟨farPortal k,actual⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨farPortal k,actual⟩) (e.extend outside ⟨(template k).hub,actual⟩) := by
  have hh:=f.corners actual ha 2
  exact ⟨hh.1.trans (f.outer_column actual ha _ _ (corner_far k) rfl),
    (f.outer_column actual ha _ _ rfl (corner_far k)).trans hh.2⟩

end TransitFrame
end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
