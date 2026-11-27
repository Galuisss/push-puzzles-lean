/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Frame

/-! Literal protected-corner walks with either neighboring long-line phase at both real collars. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners


set_option maxRecDepth 65536
set_option maxHeartbeats 0

def allNeighbors (k : Kind) : Finset (Cell (width k) (height k)) :=
  Finset.univ.filter fun p=>p.2.val=10 ∧sourceX k+1≤p.1.val ∨p.1.val=10 ∧lastY k+2≤p.2.val

private def allNeighborsTest (k : Kind) (p : Cell (width k) (height k)) : Bool :=
  decide (p.2.val=10 ∧sourceX k+1≤p.1.val ∨p.1.val=10 ∧lastY k+2≤p.2.val)

private def transitTemplate (k : Kind) : Template (width k) (height k) (count k) :=
  {template k with reserved:=fun p=>(template k).reserved p ||allNeighborsTest k p}

private theorem transitChecked (k : Kind) : (transitTemplate k).Checked where
  injective:=(checked k).injective
  slots_reserved a l:=by
    change ((template k).reserved ((template k).position a l) ||allNeighborsTest k ((template k).position a l))=true
    rw [(checked k).slots_reserved a l,Bool.true_or]
  neighbors_reserved p hp:=by simp only [transitTemplate,(checked k).neighbors_reserved p hp,Bool.true_or]
  neighbors_floor:=(checked k).neighbors_floor
  static_paths:=(checked k).static_paths
  forward_checked:=(checked k).forward_checked
  backward_checked:=(checked k).backward_checked
  walks_checked:=by cases k <;> decide +kernel

private theorem transitReserved_floor : ∀k : Kind,∀p,
    (transitTemplate k).reserved p=true→(template k).wall p=false := by decide +kernel

private theorem own_reserved (k : Kind) : (template k).reservedCells⊆(transitTemplate k).reservedCells := by
  intro p hp
  apply ((transitTemplate k).mem_reserved p).mpr
  simp only [transitTemplate,((template k).mem_reserved p).mp hp,Bool.true_or]

private theorem allNeighbors_reserved (k : Kind) : allNeighbors k⊆(transitTemplate k).reservedCells := by
  intro p hp
  apply ((transitTemplate k).mem_reserved p).mpr
  have ht : allNeighborsTest k p=true := decide_eq_true (Finset.mem_filter.mp hp).2
  simp only [transitTemplate,ht,Bool.or_true]

structure TransitFrame (k : Kind) {W H : ℕ} (e : GridEmbedding (width k) (height k) W H)
    (B : Board W H) (outside : Finset (Cell W H)) : Prop where
  walls : e.WallsAgree ((template k).board ∅) B
  outside_floor : Disjoint outside B.walls
  collar : Polyline.Frame.fixed e outside⊆allNeighbors k

namespace TransitFrame

variable {k : Kind} {W H : ℕ} {e : GridEmbedding (width k) (height k) W H} {B : Board W H}
    {outside : Finset (Cell W H)} (f : TransitFrame k e B outside)

include f in
/-- Every protected-corner exterior walk survives either complete phase of each actual foreign long-line endpoint. -/
theorem corners (actual : Finset (Cell (width k) (height k)))
    (ha : actual⊆(template k).reservedCells) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside ⟨(template k).hub,actual⟩)
      (e.extend outside ⟨(template k).corner i,actual⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(template k).corner i,actual⟩)
      (e.extend outside ⟨(template k).hub,actual⟩) := by
  let fixed:=Polyline.Frame.fixed e outside
  have hm : actual∪fixed⊆(transitTemplate k).reservedCells :=
    Finset.union_subset (ha.trans (own_reserved k)) (f.collar.trans (allNeighbors_reserved k))
  have hw : Disjoint (actual∪fixed) (template k).walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hwall
    have hf:=transitReserved_floor k p (((transitTemplate k).mem_reserved _).mp (hm hp))
    exact Bool.noConfusion (hf.symm.trans (((template k).mem_walls p).mp hwall))
  have hin:=(transitChecked k).corner_reachable i ∅ (actual∪fixed) hm hw
  have hout:=(transitChecked k).corner_to_hub i ∅ (actual∪fixed) hm hw
  exact ⟨e.reachable_withFixed f.walls
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor hin,
    e.reachable_withFixed f.walls
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor hout⟩

end TransitFrame
end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
