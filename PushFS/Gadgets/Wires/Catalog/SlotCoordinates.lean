/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.EndpointBounds
public import PushFS.Gadgets.Wires.Catalog.Statics
public import PushFS.Gadgets.Wires.Catalog.RawSlotBounds

/-! Exact first/second/last physical coordinates and complete canonical source/goal separation. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 100000
set_option maxRecDepth 65536

def secondBaseLabel : (k : Kind)→Labels k
  | .east | .west=>chainSecond 200000 (by decide)
  | .south=>chainSecond 198061 (by decide)
  | .westSouth=>⟨0,chainSecond 99970 (by decide)⟩
  | .eastSouth=>⟨0,chainSecond 99970 (by decide)⟩
  | .southEast=>⟨0,flippedSecond 98981 (by decide)⟩
  | .southWest=>⟨0,chainSecond 99001 (by decide)⟩

def secondLabel (k : Kind) : (_i : Fin 1)×Labels k := ⟨0,secondBaseLabel k⟩

def secondPoint (k : Kind) (a : Bool) : Cell :=
  match k with
  | .east | .eastSouth=>(⟨4+a.toNat,by cases a <;> decide⟩,99033)
  | .west | .westSouth=>(⟨200000-a.toNat,by cases a <;> decide⟩,99033)
  | .south | .southEast | .southWest=>(100002,⟨4+a.toNat,by cases a <;> decide⟩)

private theorem normal_second_coordinates (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨0,chainSecond m hm⟩).1.val+a.toNat=m+38 ∧
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨0,chainSecond m hm⟩).2.val=10 := by
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · rw [Polyline.L.source0 m n hm hn _ _ _,Polyline.L.in_x]
    dsimp only [Polyline.L.uniform]
    rw [chain_second_x]
    omega
  · rw [Polyline.L.source0 m n hm hn _ _ _,Polyline.L.in_y,Chain.position_row]

private theorem out_second_coordinates (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨0,chainSecond m hm⟩).1.val+a.toNat=m+38 ∧
    ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨0,chainSecond m hm⟩).2.val=10 := by
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · rw [Out.source0 m n hm hn _ _ _,Out.in_x]
    dsimp only [Out.uniform]
    rw [chain_second_x]
    omega
  · rw [Out.source0 m n hm hn _ _ _,Out.in_y,Chain.position_row]

private theorem in_second_coordinates (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨0,flippedSecond m hm⟩).1.val+a.toNat=m+58 ∧
    ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨0,flippedSecond m hm⟩).2.val=10 := by
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · rw [In.source0 m n hm hn _ _ _,In.in_x]
    dsimp only [In.uniform]
    rw [flipped_second_x]
    omega
  · rw [In.source0 m n hm hn _ _ _,In.in_y,FlippedChain.position_row]

/-- The second real source identity has its exact canonical position, including the false-phase extra collar box. -/
theorem source_second (k : Kind) (a b : Bool) : (slotMatching k a b).source (secondLabel k)=secondPoint k a := by
  have ha : a.toNat≤1 := by cases a <;> decide
  cases k
  · apply Prod.ext <;> apply Fin.ext
    · change 0+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (chainSecond 200000 (by decide))).1.val=4+a.toNat
      rw [chain_second_x]; omega
    · change 99023+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (chainSecond 200000 (by decide))).2.val=99033
      rw [Chain.position_row]
  · apply Prod.ext <;> apply Fin.ext
    · change 0+(200005-((Chain.position 200000 (by decide) (Chain.uniform 200000 a) (chainSecond 200000 (by decide))).1.val+1))=200000-a.toNat
      rw [chain_second_x]; omega
    · change 99023+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (chainSecond 200000 (by decide))).2.val=99033
      rw [Chain.position_row]
  · apply Prod.ext <;> apply Fin.ext
    · change 99992+(21-((Chain.position 198061 (by decide) (Chain.uniform 198061 a) (chainSecond 198061 (by decide))).2.val+1))=100002
      rw [Chain.position_row]
    · change 0+(Chain.position 198061 (by decide) (Chain.uniform 198061 a) (chainSecond 198061 (by decide))).1.val=4+a.toNat
      rw [chain_second_x]; omega
  · let p:=(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨0,chainSecond 99970 (by decide)⟩
    have hh : p.1.val+a.toNat=100008 ∧p.2.val=10 := normal_second_coordinates 99970 98999 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 99992+p.1.val=200000-a.toNat
      omega
    · change 99023+p.2.val=99033
      omega
  · let p:=(Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).source ⟨0,chainSecond 99970 (by decide)⟩
    have hh : p.1.val+a.toNat=100008 ∧p.2.val=10 := out_second_coordinates 99970 98979 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 0+(100013-(p.1.val+1))=4+a.toNat
      omega
    · change 99023+p.2.val=99033
      omega
  · let p:=(In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).source ⟨0,flippedSecond 98981 (by decide)⟩
    have hh : p.1.val+a.toNat=99039 ∧p.2.val=10 := in_second_coordinates 98981 99969 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 99992+p.2.val=100002
      omega
    · change 0+(99044-(p.1.val+1))=4+a.toNat
      omega
  · let p:=(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨0,chainSecond 99001 (by decide)⟩
    have hh : p.1.val+a.toNat=99039 ∧p.2.val=10 := normal_second_coordinates 99001 99969 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 0+(100013-(p.2.val+1))=100002
      omega
    · change 0+(99044-(p.1.val+1))=4+a.toNat
      omega

theorem target_sparse (k : Kind) (a b : Bool) (i j : (_i : Fin 1)×Labels k) (d : Direction) :
    ¬Adjacent d ((slotMatching k a b).target i) ((slotMatching k a b).target j) := by
  obtain ⟨i,l⟩:=i
  obtain ⟨j,q⟩:=j
  have hl : (baseMatching k a b).target l∈(base k a b).board.goals := by
    rw [←(baseMatching k a b).target_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  have hq : (baseMatching k a b).target q∈(base k a b).board.goals := by
    rw [←(baseMatching k a b).target_image]
    exact Finset.mem_map.mpr ⟨q,Finset.mem_univ _,rfl⟩
  intro hadj
  exact (baseStrong k a b).sparse _ hl _ hq d
    ((Polyline.translate_adjacent_iff (dx k) (dy k) (fitsX k a b) (fitsY k a b) d _ _).mp hadj)

/-- Every canonical physical goal endpoint has its exact true prescribed coordinate. -/
theorem target_first (k : Kind) (a b : Bool) : (slotMatching k a b).target (firstLabel k)=firstPoint k b := by
  cases k <;> cases a <;> cases b <;> rfl

theorem target_second (k : Kind) (a b : Bool) : (slotMatching k a b).target (secondLabel k)=secondPoint k b := by
  cases k <;> cases a <;> cases b <;> rfl

theorem target_last (k : Kind) (a b : Bool) : (slotMatching k a b).target (lastLabel k)=lastPoint k b := by
  cases k <;> cases a <;> cases b <;> rfl

/-- Every canonical physical source pair is separated on the actual full bitmap. -/
theorem source_sparse (k : Kind) (a b : Bool) (i j : (_i : Fin 1)×Labels k) (d : Direction) :
    ¬Adjacent d ((slotMatching k a b).source i) ((slotMatching k a b).source j) := by
  obtain ⟨i,l⟩:=i
  obtain ⟨j,q⟩:=j
  intro hadj
  cases k
  · have hh:=Polyline.isometry_translate_adjacent (GridIsometry.refl 200005 21) 0 99023
      (by decide : 0+200005≤200005) (by decide : 99023+21≤198066)
      (p:=(Chain.position 200000 (by decide) (Chain.uniform 200000 a)) l) (q:=(Chain.position 200000 (by decide) (Chain.uniform 200000 a)) q) hadj
    exact Chain.sparse_targets 200000 (by decide) a l q _ hh
  · have hh:=Polyline.isometry_translate_adjacent (GridIsometry.reflectX 200005 21) 0 99023
      (by decide : 0+200005≤200005) (by decide : 99023+21≤198066)
      (p:=(Chain.position 200000 (by decide) (Chain.uniform 200000 a)) l) (q:=(Chain.position 200000 (by decide) (Chain.uniform 200000 a)) q) hadj
    exact Chain.sparse_targets 200000 (by decide) a l q _ hh
  · have hh:=Polyline.isometry_translate_adjacent ((GridIsometry.transpose 198066 21).trans (GridIsometry.reflectX 21 198066)) 99992 0
      (by decide : 99992+21≤200005) (by decide : 0+198066≤198066)
      (p:=(Chain.position 198061 (by decide) (Chain.uniform 198061 a)) l) (q:=(Chain.position 198061 (by decide) (Chain.uniform 198061 a)) q) hadj
    exact Chain.sparse_targets 198061 (by decide) a l q _ hh
  · have hh:=Polyline.isometry_translate_adjacent (GridIsometry.refl 100013 99043) 99992 99023
      (by decide : 99992+100013≤200005) (by decide : 99023+99043≤198066)
      (p:=((Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source) l) (q:=((Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source) q) hadj
    exact normal_source_sparse 99970 98999 (by decide) (by decide) a b l q _ hh
  · have hh:=Polyline.isometry_translate_adjacent (GridIsometry.reflectX 100013 99043) 0 99023
      (by decide : 0+100013≤200005) (by decide : 99023+99043≤198066)
      (p:=((Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).source) l) (q:=((Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).source) q) hadj
    exact out_source_sparse 99970 98979 (by decide) (by decide) a b l q _ hh
  · have hh:=Polyline.isometry_translate_adjacent ((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013)) 99992 0
      (by decide : 99992+100013≤200005) (by decide : 0+99044≤198066)
      (p:=((In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).source) l) (q:=((In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).source) q) hadj
    exact in_source_sparse 98981 99969 (by decide) (by decide) a b l q _ hh
  · have hh:=Polyline.isometry_translate_adjacent (((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013)).trans (GridIsometry.reflectX 100013 99044)) 0 0
      (by decide : 0+100013≤200005) (by decide : 0+99044≤198066)
      (p:=((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source) l) (q:=((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source) q) hadj
    exact normal_source_sparse 99001 99969 (by decide) (by decide) a b l q _ hh

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
