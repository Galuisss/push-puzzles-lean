/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RawSlotBounds
public import PushFS.Gadgets.Wires.Catalog.Data

/-! Complete canonical physical-slot coordinate bounds on each full padded ordinary cell. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def SlotBounds (k : Kind) (a : Bool) (x y : ℕ) : Prop :=
  match k with
  | .east=>y=99033 ∧2+a.toNat≤x ∧x≤200000+a.toNat
  | .west=>y=99033 ∧4≤x+a.toNat ∧x+a.toNat≤200002
  | .south=>x=100002 ∧2+a.toNat≤y ∧y≤198061+a.toNat
  | .westSouth=>(x=100002 ∨y=99033) ∧100002≤x ∧x+a.toNat≤200002 ∧99033≤y ∧y≤198061+a.toNat
  | .eastSouth=>(x=100002 ∨y=99033) ∧2+a.toNat≤x ∧x≤100002 ∧99033≤y ∧y≤198061+a.toNat
  | .southEast=>(x=100002 ∨y=99033) ∧100002≤x ∧x≤200000+a.toNat ∧2+a.toNat≤y ∧y≤99033
  | .southWest=>(x=100002 ∨y=99033) ∧4≤x+a.toNat ∧x≤100002 ∧2+a.toNat≤y ∧y≤99033

def SlotRegion (k : Kind) (a : Bool) (p : Cell) : Prop := SlotBounds k a p.1.val p.2.val

/-- The real canonical source inventory has the exact rail rows/columns and true first/last extrema. -/
theorem source_bounds (k : Kind) (a b : Bool) (l : (_i : Fin 1)×Labels k) :
    SlotRegion k a ((slotMatching k a b).source l) := by
  have ha : a.toNat≤1 := by cases a <;> decide
  obtain ⟨i,l⟩:=l
  cases k
  · let q:=Chain.position 200000 (by decide) (Chain.uniform 200000 a) l
    have hb:=Polyline.chain_phase_bounds 200000 (by decide) a l
    have hy : q.2.val=10 := Chain.position_row 200000 (by decide) _ _
    change SlotBounds .east a (0+(q.1.val)) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    change 2+a.toNat≤q.1.val ∧q.1.val≤200000+a.toNat at hb
    omega
  · let q:=Chain.position 200000 (by decide) (Chain.uniform 200000 a) l
    have hb:=Polyline.chain_phase_bounds 200000 (by decide) a l
    have hy : q.2.val=10 := Chain.position_row 200000 (by decide) _ _
    change SlotBounds .west a (0+(200005-(q.1.val+1))) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    change 2+a.toNat≤q.1.val ∧q.1.val≤200000+a.toNat at hb
    omega
  · let q:=Chain.position 198061 (by decide) (Chain.uniform 198061 a) l
    have hb:=Polyline.chain_phase_bounds 198061 (by decide) a l
    have hy : q.2.val=10 := Chain.position_row 198061 (by decide) _ _
    change SlotBounds .south a (99992+(21-(q.2.val+1))) (0+(q.1.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    change 2+a.toNat≤q.1.val ∧q.1.val≤198061+a.toNat at hb
    omega
  · let q:=(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source l
    have hb:= normal_source_bounds 99970 98999 (by decide) (by decide) a b l
    change RawSlotBounds _ _ a q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .westSouth a (99992+(q.1.val)) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
  · let q:=(Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).source l
    have hb:= out_source_bounds 99970 98979 (by decide) (by decide) a b l
    change RawSlotBounds _ _ a q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .eastSouth a (0+(100013-(q.1.val+1))) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
  · let q:=(In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).source l
    have hb:= in_source_bounds 98981 99969 (by decide) (by decide) a b l
    change RawSlotBounds _ _ a q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .southEast a (99992+(q.2.val)) (0+(99044-(q.1.val+1)))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
  · let q:=(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source l
    have hb:= normal_source_bounds 99001 99969 (by decide) (by decide) a b l
    change RawSlotBounds _ _ a q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .southWest a (0+(100013-(q.2.val+1))) (0+(99044-(q.1.val+1)))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
/-- The real canonical goal inventory has the exact rail rows/columns and true first/last extrema. -/
theorem target_bounds (k : Kind) (a b : Bool) (l : (_i : Fin 1)×Labels k) :
    SlotRegion k b ((slotMatching k a b).target l) := by
  have ha : b.toNat≤1 := by cases b <;> decide
  obtain ⟨i,l⟩:=l
  cases k
  · let q:=Chain.position 200000 (by decide) (Chain.uniform 200000 b) l
    have hb:=Polyline.chain_phase_bounds 200000 (by decide) b l
    have hy : q.2.val=10 := Chain.position_row 200000 (by decide) _ _
    change SlotBounds .east b (0+(q.1.val)) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    change 2+b.toNat≤q.1.val ∧q.1.val≤200000+b.toNat at hb
    omega
  · let q:=Chain.position 200000 (by decide) (Chain.uniform 200000 b) l
    have hb:=Polyline.chain_phase_bounds 200000 (by decide) b l
    have hy : q.2.val=10 := Chain.position_row 200000 (by decide) _ _
    change SlotBounds .west b (0+(200005-(q.1.val+1))) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    change 2+b.toNat≤q.1.val ∧q.1.val≤200000+b.toNat at hb
    omega
  · let q:=Chain.position 198061 (by decide) (Chain.uniform 198061 b) l
    have hb:=Polyline.chain_phase_bounds 198061 (by decide) b l
    have hy : q.2.val=10 := Chain.position_row 198061 (by decide) _ _
    change SlotBounds .south b (99992+(21-(q.2.val+1))) (0+(q.1.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    change 2+b.toNat≤q.1.val ∧q.1.val≤198061+b.toNat at hb
    omega
  · let q:=(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).target l
    have hb:= normal_target_bounds 99970 98999 (by decide) (by decide) a b l
    change RawSlotBounds _ _ b q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .westSouth b (99992+(q.1.val)) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
  · let q:=(Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).target l
    have hb:= out_target_bounds 99970 98979 (by decide) (by decide) a b l
    change RawSlotBounds _ _ b q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .eastSouth b (0+(100013-(q.1.val+1))) (99023+(q.2.val))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
  · let q:=(In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).target l
    have hb:= in_target_bounds 98981 99969 (by decide) (by decide) a b l
    change RawSlotBounds _ _ b q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .southEast b (99992+(q.2.val)) (0+(99044-(q.1.val+1)))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega
  · let q:=(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).target l
    have hb:= normal_target_bounds 99001 99969 (by decide) (by decide) a b l
    change RawSlotBounds _ _ b q at hb
    unfold RawSlotBounds at hb
    change SlotBounds .southWest b (0+(100013-(q.2.val+1))) (0+(99044-(q.1.val+1)))
    unfold SlotBounds
    have hx:=q.1.isLt
    have hh:=q.2.isLt
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
