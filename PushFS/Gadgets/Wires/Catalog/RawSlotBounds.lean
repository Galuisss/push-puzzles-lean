/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.InOrder
public import PushFS.Gadgets.Wires.Catalog.OutOrder

/-! Exact canonical physical-slot supports and endpoint bounds of native long L glyphs. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem turn_slot_bounds : ∀(a : Bool) (i : Fin 29),
    ((Turn.template.position a i).1.val=10 ∨(Turn.template.position a i).2.val=9) ∧
    10≤(Turn.template.position a i).1.val ∧(Turn.template.position a i).1.val≤40 ∧
    9≤(Turn.template.position a i).2.val ∧(Turn.template.position a i).2.val≤39 := by decide +kernel

/-- The common actual corner and both complete endpoint-extremal intervals. -/
def RawSlotBounds {w h : ℕ} (maxX maxY : ℕ) (a : Bool) (p : PushFS.Cell w h) : Prop :=
  (p.1.val=10 ∨p.2.val=10) ∧10≤p.1.val ∧p.1.val+a.toNat≤maxX ∧10≤p.2.val ∧p.2.val≤maxY+a.toNat

theorem normal_source_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) (l : Polyline.L.Label m n) :
    RawSlotBounds (m+40) (n+39) a ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source l) := by
  rw [Polyline.L.source_position m n hm hn a b l]
  have ha : a.toNat≤1 := by cases a <;> decide
  obtain ⟨i,l⟩:=l
  have cases3 : i=0∨i=1∨i=2 := by have:=i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases3 with rfl|rfl|rfl
  · have hb:=Polyline.chain_phase_bounds m hm a l
    have hy:=Chain.position_row m hm (Chain.uniform m a) l
    unfold RawSlotBounds
    rw [Polyline.L.position0 m n hm hn a l,Polyline.L.in_x,Polyline.L.in_y]
    omega
  · have hb:=turn_slot_bounds a l
    unfold RawSlotBounds
    rw [Polyline.L.position1 m n hm hn a l,Polyline.L.turn_x,Polyline.L.turn_y]
    omega
  · have hb:=Polyline.chain_phase_bounds n hn a l
    have hy:=Chain.position_row n hn (Chain.uniform n a) l
    unfold RawSlotBounds
    rw [Polyline.L.position2 m n hm hn a l,Polyline.L.out_x,Polyline.L.out_y]
    omega

theorem out_source_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) (l : Out.Label m n) :
    RawSlotBounds (m+40) (n+59) a ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source l) := by
  rw [Out.source_position m n hm hn a b l]
  have ha : a.toNat≤1 := by cases a <;> decide
  obtain ⟨i,l⟩:=l
  have cases3 : i=0∨i=1∨i=2 := by have:=i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases3 with rfl|rfl|rfl
  · have hb:=Polyline.chain_phase_bounds m hm a l
    have hy:=Chain.position_row m hm (Chain.uniform m a) l
    unfold RawSlotBounds
    rw [Out.position0 m n hm hn a l,Out.in_x,Out.in_y]
    omega
  · have hb:=turn_slot_bounds a l
    unfold RawSlotBounds
    rw [Out.position1 m n hm hn a l,Out.turn_x,Out.turn_y]
    omega
  · have hb:=Tail.phase_bounds n hn a l
    have hy:=Tail.position_row n hn (Tail.uniform n a) l
    unfold RawSlotBounds
    rw [Out.position2 m n hm hn a l,Out.out_x,Out.out_y]
    omega

theorem in_source_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) (l : In.Label m n) :
    RawSlotBounds (m+60) (n+39) a ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source l) := by
  rw [In.source_position m n hm hn a b l]
  have ha : a.toNat≤1 := by cases a <;> decide
  obtain ⟨i,l⟩:=l
  have cases3 : i=0∨i=1∨i=2 := by have:=i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases3 with rfl|rfl|rfl
  · have hb:=Head.phase_bounds m hm a l
    have hy:=Head.position_row m hm (Head.uniform m a) l
    unfold RawSlotBounds
    rw [In.position0 m n hm hn a l,In.in_x,In.in_y]
    change (Tail.position m hm (Tail.uniform m a) l).2.val=10 at hy
    change 2+a.toNat≤(Tail.position m hm (Tail.uniform m a) l).1.val ∧
      (Tail.position m hm (Tail.uniform m a) l).1.val≤m+20+a.toNat at hb
    omega
  · have hb:=turn_slot_bounds a l
    unfold RawSlotBounds
    rw [In.position1 m n hm hn a l,In.turn_x,In.turn_y]
    omega
  · have hb:=Polyline.chain_phase_bounds n hn a l
    have hy:=Chain.position_row n hn (Chain.uniform n a) l
    unfold RawSlotBounds
    rw [In.position2 m n hm hn a l,In.out_x,In.out_y]
    omega

theorem normal_target_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) (l : Polyline.L.Label m n) :
    RawSlotBounds (m+40) (n+39) b ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).target l) := by
  rw [Polyline.L.target_position m n hm hn a b l]
  have hh:=normal_source_bounds m n hm hn b b l
  rw [Polyline.L.source_position m n hm hn b b l] at hh
  exact hh

theorem normal_source_sparse (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (i j : Polyline.L.Label m n) (d : Direction) : ¬Adjacent d ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source i) ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source j) := by
  have hi : (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source i∈(Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).initial.boxes := Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hj : (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source j∈(Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).initial.boxes := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  rw [Polyline.L.initial_boxes] at hi hj
  exact Polyline.L.sparse_targets m n hm hn a hi hj d

theorem out_target_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) (l : Out.Label m n) :
    RawSlotBounds (m+40) (n+59) b ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).target l) := by
  rw [Out.target_position m n hm hn a b l]
  have hh:=out_source_bounds m n hm hn b b l
  rw [Out.source_position m n hm hn b b l] at hh
  exact hh

theorem out_source_sparse (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (i j : Out.Label m n) (d : Direction) : ¬Adjacent d ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source i) ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source j) := by
  have hi : (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source i∈(Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).initial.boxes := Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hj : (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source j∈(Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).initial.boxes := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  rw [Out.initial_boxes] at hi hj
  exact Out.sparse_targets m n hm hn a hi hj d

theorem in_target_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) (l : In.Label m n) :
    RawSlotBounds (m+60) (n+39) b ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).target l) := by
  rw [In.target_position m n hm hn a b l]
  have hh:=in_source_bounds m n hm hn b b l
  rw [In.source_position m n hm hn b b l] at hh
  exact hh

theorem in_source_sparse (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (i j : In.Label m n) (d : Direction) : ¬Adjacent d ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source i) ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source j) := by
  have hi : (In.atlas m n hm hn (In.uniform a) (In.uniform b)).source i∈(In.atlas m n hm hn (In.uniform a) (In.uniform b)).initial.boxes := Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hj : (In.atlas m n hm hn (In.uniform a) (In.uniform b)).source j∈(In.atlas m n hm hn (In.uniform a) (In.uniform b)).initial.boxes := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  rw [In.initial_boxes] at hi hj
  exact In.sparse_targets m n hm hn a hi hj d

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
