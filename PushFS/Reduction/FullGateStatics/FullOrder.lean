/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Certificate
public import PushFS.Reduction.FullGateStatics.CoreMotionOrder
public import PushFS.Reduction.FullGateStatics.PrimitiveOrder
public import PushFS.Gadgets.Gates.Soundness.Geometry

/-! The complete physical gate's actual source/goal identity correspondence preserves SCC coordinate order. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board Mosaic.name

private theorem core_rail_order (g : GateTileState) (l k : Fin (Gates.slots g.core.isAND).length) :
    ((rawSource g ⟨.inl 0,l⟩).2=(rawSource g ⟨.inl 0,k⟩).2 →
      (rawSource g ⟨.inl 0,l⟩).1.val<(rawSource g ⟨.inl 0,k⟩).1.val →
      (rawTarget g ⟨.inl 0,l⟩).1.val<(rawTarget g ⟨.inl 0,k⟩).1.val) ∧
    ((rawSource g ⟨.inl 0,l⟩).1=(rawSource g ⟨.inl 0,k⟩).1 →
      (rawSource g ⟨.inl 0,l⟩).2.val<(rawSource g ⟨.inl 0,k⟩).2.val →
      (rawTarget g ⟨.inl 0,l⟩).2.val<(rawTarget g ⟨.inl 0,k⟩).2.val) := by
  let s:=(Gates.slots g.core.isAND)[l.val]
  let t:=(Gates.slots g.core.isAND)[k.val]
  have hh:=core_slot_rail_order g.core.isAND g.core.initial g.core.target s t
    (List.getElem_mem l.isLt) (List.getElem_mem k.isLt)
  constructor
  · intro he ho
    have he':=congrArg Fin.val he
    change (Inventory.offset g (.inl 0)).2+(s.position g.core.initial).2.val=
      (Inventory.offset g (.inl 0)).2+(t.position g.core.initial).2.val at he'
    change (Inventory.offset g (.inl 0)).1+(s.position g.core.initial).1.val<
      (Inventory.offset g (.inl 0)).1+(t.position g.core.initial).1.val at ho
    change (Inventory.offset g (.inl 0)).1+(s.position g.core.target).1.val<
      (Inventory.offset g (.inl 0)).1+(t.position g.core.target).1.val
    have hpos:=hh.1 (Fin.ext (by omega)) (by omega)
    omega
  · intro he ho
    have he':=congrArg Fin.val he
    change (Inventory.offset g (.inl 0)).1+(s.position g.core.initial).1.val=
      (Inventory.offset g (.inl 0)).1+(t.position g.core.initial).1.val at he'
    change (Inventory.offset g (.inl 0)).2+(s.position g.core.initial).2.val<
      (Inventory.offset g (.inl 0)).2+(t.position g.core.initial).2.val at ho
    change (Inventory.offset g (.inl 0)).2+(s.position g.core.target).2.val<
      (Inventory.offset g (.inl 0)).2+(t.position g.core.target).2.val
    have hpos:=hh.2 (Fin.ext (by omega)) (by omega)
    omega

/-- Actual raw gate identities preserve every common-row and common-column source order. -/
private theorem raw_rail_order (g : GateTileState) (i j : Inventory.Index g)
    (l : Inventory.Labels g i) (k : Inventory.Labels g j) :
    ((rawSource g ⟨i,l⟩).2=(rawSource g ⟨j,k⟩).2 →
      (rawSource g ⟨i,l⟩).1.val<(rawSource g ⟨j,k⟩).1.val →(rawTarget g ⟨i,l⟩).1.val<(rawTarget g ⟨j,k⟩).1.val) ∧
    ((rawSource g ⟨i,l⟩).1=(rawSource g ⟨j,k⟩).1 →
      (rawSource g ⟨i,l⟩).2.val<(rawSource g ⟨j,k⟩).2.val →(rawTarget g ⟨i,l⟩).2.val<(rawTarget g ⟨j,k⟩).2.val) := by
  by_cases hij : i=j
  · subst j
    by_cases hi : i=.inl 0
    · subst i
      exact core_rail_order g l k
    · have hh:=noncore_primitive_order g i hi l k
      exact ⟨fun _ ho=>hh.1 ho,fun _ ho=>hh.2 ho⟩
  · exact different_primitive_order g i j hij l k

/-- The full original catalog pairing retains source rail order even when placed in a larger SCC. -/
theorem full_rail_order (g : GateTileState) (l k : FullLabel g) :
    (((fullSlotMatching g).source l).2=((fullSlotMatching g).source k).2 →
      ((fullSlotMatching g).source l).1.val<((fullSlotMatching g).source k).1.val →
      ((fullSlotMatching g).target l).1.val<((fullSlotMatching g).target k).1.val) ∧
    (((fullSlotMatching g).source l).1=((fullSlotMatching g).source k).1 →
      ((fullSlotMatching g).source l).2.val<((fullSlotMatching g).source k).2.val →
      ((fullSlotMatching g).target l).2.val<((fullSlotMatching g).target k).2.val) := by
  obtain ⟨⟨i,l⟩,rfl⟩:=(rawLabelEquiv g).surjective l
  obtain ⟨⟨j,k⟩,rfl⟩:=(rawLabelEquiv g).surjective k
  have hs (i : Inventory.Index g) (l : Inventory.Labels g i) :
      (fullSlotMatching g).source ((rawLabelEquiv g) ⟨i,l⟩)=rawSource g ⟨i,l⟩ := raw_source g i l
  have ht (i : Inventory.Index g) (l : Inventory.Labels g i) :
      (fullSlotMatching g).target ((rawLabelEquiv g) ⟨i,l⟩)=rawTarget g ⟨i,l⟩ := raw_target g i l
  have hh:=raw_rail_order g i j l k
  constructor
  · intro he ho
    rw [hs,hs] at he ho
    rw [ht,ht]
    exact hh.1 he ho
  · intro he ho
    rw [hs,hs] at he ho
    rw [ht,ht]
    exact hh.2 he ho

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
