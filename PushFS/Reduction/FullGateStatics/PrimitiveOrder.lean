/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Primitive
public import PushFS.Reduction.FullGateRawLabels
public import PushFS.Gadgets.Wires.Chain.Order
public import PushFS.Gadgets.Wires.FlippedChain.Order

/-! Canonical coordinate orders of complete primitive inventories survive actual rectangle orientations. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def CoordinateOrdered {I : Instance} {L : Type} [Fintype L] (M : SlotMatching I L) : Prop :=
  (∀i j,(M.source i).1.val<(M.source j).1.val→(M.target i).1.val<(M.target j).1.val) ∧
  (∀i j,(M.source i).2.val<(M.source j).2.val→(M.target i).2.val<(M.target j).2.val)

private theorem rect_order {L : Type} {w h : ℕ} (s t : L→Cell w h)
    (hx : ∀i j,(s i).1.val<(s j).1.val→(t i).1.val<(t j).1.val)
    (hy : ∀i j,(s i).2.val<(s j).2.val→(t i).2.val<(t j).2.val)
    (o : RectOrientation) (dx dy : ℕ) (i j : L) :
    ((o.coordinates w h dx dy (s i)).1<(o.coordinates w h dx dy (s j)).1→
      (o.coordinates w h dx dy (t i)).1<(o.coordinates w h dx dy (t j)).1) ∧
    ((o.coordinates w h dx dy (s i)).2<(o.coordinates w h dx dy (s j)).2→
      (o.coordinates w h dx dy (t i)).2<(o.coordinates w h dx dy (t j)).2) := by
  have hix:=(s i).1.isLt
  have hjx:=(s j).1.isLt
  have hitx:=(t i).1.isLt
  have hjtx:=(t j).1.isLt
  have hiy:=(s i).2.isLt
  have hjy:=(s j).2.isLt
  have hity:=(t i).2.isLt
  have hjty:=(t j).2.isLt
  rcases o with ⟨swap,flipX,flipY⟩
  cases swap <;> cases flipX <;> cases flipY <;>
    simp only [RectOrientation.coordinates_point,RectOrientation.point,RectOrientation.width,
      RectOrientation.height,Bool.false_eq_true,ite_false,ite_true] <;>
    constructor <;> intro ho
  all_goals first
    | have hh:=hx i j (by omega); omega
    | have hh:=hx j i (by omega); omega
    | have hh:=hy i j (by omega); omega
    | have hh:=hy j i (by omega); omega

theorem reorient_order {I : Instance} {L : Type} [Fintype L] (M : SlotMatching I L)
    (hm : CoordinateOrdered M) (o : RectOrientation) :
    CoordinateOrdered (M.reorient (o.axis I.width I.height).geometry) := by
  constructor
  · intro i j ho
    have hh:=rect_order M.source M.target hm.1 hm.2 o 0 0 i j
    have coord (p : Cell I.width I.height) :
        (((o.axis I.width I.height).geometry.cells p).1.val,((o.axis I.width I.height).geometry.cells p).2.val)=
          o.coordinates I.width I.height 0 0 p := by
      rw [RectOrientation.coordinates_point,←o.point_cells]
      simp only [Nat.zero_add]
    have hs1:=congrArg Prod.fst (coord (M.source i))
    have hs2:=congrArg Prod.fst (coord (M.source j))
    have ht1:=congrArg Prod.fst (coord (M.target i))
    have ht2:=congrArg Prod.fst (coord (M.target j))
    change ((o.axis I.width I.height).geometry.cells (M.source i)).1.val<
      ((o.axis I.width I.height).geometry.cells (M.source j)).1.val at ho
    change ((o.axis I.width I.height).geometry.cells (M.target i)).1.val<
      ((o.axis I.width I.height).geometry.cells (M.target j)).1.val
    dsimp only at hs1 hs2 ht1 ht2
    rw [ht1,ht2]
    exact hh.1 (by rw [←hs1,←hs2]; exact ho)
  · intro i j ho
    have hh:=rect_order M.source M.target hm.1 hm.2 o 0 0 i j
    have coord (p : Cell I.width I.height) :
        (((o.axis I.width I.height).geometry.cells p).1.val,((o.axis I.width I.height).geometry.cells p).2.val)=
          o.coordinates I.width I.height 0 0 p := by
      rw [RectOrientation.coordinates_point,←o.point_cells]
      simp only [Nat.zero_add]
    have hs1:=congrArg Prod.snd (coord (M.source i))
    have hs2:=congrArg Prod.snd (coord (M.source j))
    have ht1:=congrArg Prod.snd (coord (M.target i))
    have ht2:=congrArg Prod.snd (coord (M.target j))
    change ((o.axis I.width I.height).geometry.cells (M.source i)).2.val<
      ((o.axis I.width I.height).geometry.cells (M.source j)).2.val at ho
    change ((o.axis I.width I.height).geometry.cells (M.target i)).2.val<
      ((o.axis I.width I.height).geometry.cells (M.target j)).2.val
    dsimp only at hs1 hs2 ht1 ht2
    rw [ht1,ht2]
    exact hh.2 (by rw [←hs1,←hs2]; exact ho)

theorem chain_coordinate_order (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    CoordinateOrdered (Chain.slotMatching n hn a b) := by
  refine ⟨fun i j ho=>Chain.position_order n hn _ _ i j ho,?_⟩
  intro i j ho
  have hi:=Chain.position_row n hn (Chain.uniform n a) i
  have hj:=Chain.position_row n hn (Chain.uniform n a) j
  change (Chain.position n hn (Chain.uniform n a) i).2.val<(Chain.position n hn (Chain.uniform n a) j).2.val at ho
  omega

private theorem lineBase_coordinate_order (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    CoordinateOrdered (lineMatching f n hn a b) := by
  cases f
  · exact chain_coordinate_order n hn a b
  · constructor
    · intro i j ho
      change FlippedChain.Label n at i j
      change ((FlippedChain.slotMatching n hn a b).source i).1.val<((FlippedChain.slotMatching n hn a b).source j).1.val at ho
      change ((FlippedChain.slotMatching n hn a b).target i).1.val<((FlippedChain.slotMatching n hn a b).target j).1.val
      rw [FlippedChain.source_position,FlippedChain.source_position] at ho
      rw [FlippedChain.target_position,FlippedChain.target_position]
      exact FlippedChain.position_order n hn a b i j ho
    · intro i j ho
      change FlippedChain.Label n at i j
      change ((FlippedChain.slotMatching n hn a b).source i).2.val<((FlippedChain.slotMatching n hn a b).source j).2.val at ho
      rw [FlippedChain.source_position,FlippedChain.source_position,FlippedChain.position_row,FlippedChain.position_row] at ho
      omega

private theorem line_coordinate_order (k : Key) (i : ℕ) (hi : i<(curve k).length) (a b : Bool) :
    CoordinateOrdered (lineSlotMatching k i hi a b) :=
  reorient_order (lineMatching (fillerFlip k i) (fillerSpan k i) (filler_shape k i hi).2.1 a b)
    (lineBase_coordinate_order _ _ _ _ _) (lineOrientation (original k i).travel (fillerFlip k i))

private theorem corner_coordinate_order (k : Key) (i : ℕ) (a b : Bool) :
    CoordinateOrdered (cornerMatching k i a b) :=
  reorient_order (ShortCorners.slotMatching (cornerKind k i) a b)
    ⟨ShortCorners.order_x _ a b,ShortCorners.order_y _ a b⟩ (cornerOrientation k i)

private theorem west_coordinate_order (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    CoordinateOrdered ((Chain.slotMatching n hn a b).reorient (GateLead.westIso kind n)) := by
  cases kind
  · exact reorient_order (Chain.slotMatching n hn a b) (chain_coordinate_order n hn a b) ⟨false,true,true⟩
  · exact reorient_order (Chain.slotMatching n hn a b) (chain_coordinate_order n hn a b) ⟨false,true,false⟩

private theorem buffer_coordinate_order (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) (hi : i≠0) : CoordinateOrdered (GateLead.matching kind n hn a b i) := by
  fin_cases i
  · exact False.elim (hi rfl)
  · exact west_coordinate_order kind n hn a.left b.left
  · exact reorient_order (Chain.slotMatching n hn a.upper b.upper)
      (chain_coordinate_order n hn a.upper b.upper) ⟨true,true,true⟩
  · exact reorient_order (Chain.slotMatching n hn (!a.right) (!b.right))
      (chain_coordinate_order n hn (!a.right) (!b.right)) ⟨false,false,true⟩

/-- Every wire, rotated chain, protected short corner or buffer preserves both coordinate orders. -/
theorem noncore_primitive_order (g : GateTileState) (i : Inventory.Index g) (hi : i≠.inl 0)
    (l k : Inventory.Labels g i) :
    ((rawSource g ⟨i,l⟩).1.val<(rawSource g ⟨i,k⟩).1.val→(rawTarget g ⟨i,l⟩).1.val<(rawTarget g ⟨i,k⟩).1.val) ∧
    ((rawSource g ⟨i,l⟩).2.val<(rawSource g ⟨i,k⟩).2.val→(rawTarget g ⟨i,l⟩).2.val<(rawTarget g ⟨i,k⟩).2.val) := by
  have hh : CoordinateOrdered (Inventory.matching g i) := by
    rcases i with i|(⟨role,j|j⟩|role)
    · exact buffer_coordinate_order g.core.isAND 2301 (by omega) g.core.initial g.core.target i
        (by intro he; exact hi (congrArg Sum.inl he))
    · exact line_coordinate_order _ _ j.isLt _ _
    · exact corner_coordinate_order _ _ _ _
    · exact Fin.elim0 l
  have hs (u : Inventory.Labels g i) :
      ((rawSource g ⟨i,u⟩).1.val,(rawSource g ⟨i,u⟩).2.val)=
        ((Inventory.offset g i).1+((Inventory.matching g i).source u).1.val,
          (Inventory.offset g i).2+((Inventory.matching g i).source u).2.val) := rfl
  have ht (u : Inventory.Labels g i) :
      ((rawTarget g ⟨i,u⟩).1.val,(rawTarget g ⟨i,u⟩).2.val)=
        ((Inventory.offset g i).1+((Inventory.matching g i).target u).1.val,
          (Inventory.offset g i).2+((Inventory.matching g i).target u).2.val) := rfl
  have hslx:=congrArg Prod.fst (hs l)
  have hskx:=congrArg Prod.fst (hs k)
  have htlx:=congrArg Prod.fst (ht l)
  have htkx:=congrArg Prod.fst (ht k)
  have hsly:=congrArg Prod.snd (hs l)
  have hsky:=congrArg Prod.snd (hs k)
  have htly:=congrArg Prod.snd (ht l)
  have htky:=congrArg Prod.snd (ht k)
  constructor
  · intro ho
    have hh':=hh.1 l k (by omega)
    omega
  · intro ho
    have hh':=hh.2 l k (by omega)
    omega

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
