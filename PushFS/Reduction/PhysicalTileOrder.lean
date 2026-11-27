/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.FullOrder
public import PushFS.Gadgets.Wires.Catalog.Statics
public import PushFS.Reduction.PhysicalTiles

/-! Whole-rail coordinate order for every actual complete macrocell pairing. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Gadgets.Wires GateTileRouting.FullGateStatics
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

private theorem normal_coordinate_order (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    CoordinateOrdered (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching := by
  constructor
  · intro l k ho
    change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source l).1.val<((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source k).1.val at ho
    change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).target l).1.val<((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).target k).1.val
    rw [Polyline.L.source_position,Polyline.L.source_position] at ho
    rw [Polyline.L.target_position,Polyline.L.target_position]
    exact Polyline.L.position_order_x m n hm hn a b l k ho
  · intro l k ho
    change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source l).2.val<((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source k).2.val at ho
    change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).target l).2.val<((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).target k).2.val
    rw [Polyline.L.source_position,Polyline.L.source_position] at ho
    rw [Polyline.L.target_position,Polyline.L.target_position]
    exact Polyline.L.position_order_y m n hm hn a b l k ho

private theorem out_coordinate_order (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    CoordinateOrdered (Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).slotMatching := by
  constructor
  · intro l k ho
    change ((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).source l).1.val<((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).source k).1.val at ho
    change ((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).target l).1.val<((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).target k).1.val
    rw [Catalog.Out.source_position,Catalog.Out.source_position] at ho
    rw [Catalog.Out.target_position,Catalog.Out.target_position]
    exact Catalog.Out.position_order_x m n hm hn a b l k ho
  · intro l k ho
    change ((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).source l).2.val<((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).source k).2.val at ho
    change ((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).target l).2.val<((Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).target k).2.val
    rw [Catalog.Out.source_position,Catalog.Out.source_position] at ho
    rw [Catalog.Out.target_position,Catalog.Out.target_position]
    exact Catalog.Out.position_order_y m n hm hn a b l k ho

private theorem in_coordinate_order (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    CoordinateOrdered (Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).slotMatching := by
  constructor
  · intro l k ho
    change ((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).source l).1.val<((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).source k).1.val at ho
    change ((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).target l).1.val<((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).target k).1.val
    rw [Catalog.In.source_position,Catalog.In.source_position] at ho
    rw [Catalog.In.target_position,Catalog.In.target_position]
    exact Catalog.In.position_order_x m n hm hn a b l k ho
  · intro l k ho
    change ((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).source l).2.val<((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).source k).2.val at ho
    change ((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).target l).2.val<((Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).target k).2.val
    rw [Catalog.In.source_position,Catalog.In.source_position] at ho
    rw [Catalog.In.target_position,Catalog.In.target_position]
    exact Catalog.In.position_order_y m n hm hn a b l k ho

private theorem base_coordinate_order (k : Catalog.Kind) (a b : Bool) : CoordinateOrdered (Catalog.baseMatching k a b) := by
  cases k
  · exact chain_coordinate_order 200000 (by decide) a b
  · exact reorient_order _ (chain_coordinate_order 200000 (by decide) a b) ⟨false,true,false⟩
  · exact reorient_order _ (reorient_order _ (chain_coordinate_order 198061 (by decide) a b) ⟨true,false,false⟩) ⟨false,true,false⟩
  · exact normal_coordinate_order 99970 98999 (by decide) (by decide) a b
  · exact reorient_order _ (out_coordinate_order 99970 98979 (by decide) (by decide) a b) ⟨false,true,false⟩
  · exact reorient_order _ (reorient_order _ (in_coordinate_order 98981 99969 (by decide) (by decide) a b) ⟨false,true,false⟩) ⟨true,false,false⟩
  · exact reorient_order _ (reorient_order _ (reorient_order _ (normal_coordinate_order 99001 99969 (by decide) (by decide) a b) ⟨false,true,false⟩) ⟨true,false,false⟩) ⟨false,true,false⟩

private theorem placed_coordinate_order {I : Instance} {L : Type} [Fintype L] {W H : ℕ}
    (M : SlotMatching I L) (hm : CoordinateOrdered M) (dx dy : ℕ) (hx : dx+I.width≤W) (hy : dy+I.height≤H) :
    CoordinateOrdered (Catalog.placedAtlas M dx dy hx hy).slotMatching := by
  constructor
  · rintro ⟨i,l⟩ ⟨j,k⟩ ho
    change dx+(M.source l).1.val<dx+(M.source k).1.val at ho
    change dx+(M.target l).1.val<dx+(M.target k).1.val
    have hh:=hm.1 l k (by omega)
    omega
  · rintro ⟨i,l⟩ ⟨j,k⟩ ho
    change dy+(M.source l).2.val<dy+(M.source k).2.val at ho
    change dy+(M.target l).2.val<dy+(M.target k).2.val
    have hh:=hm.2 l k (by omega)
    omega

private theorem catalog_coordinate_order (k : Catalog.Kind) (a b : Bool) : CoordinateOrdered
    (Catalog.slotMatching k a b) :=
  placed_coordinate_order (Catalog.baseMatching k a b) (base_coordinate_order k a b)
    (Catalog.dx k) (Catalog.dy k) (Catalog.fitsX k a b) (Catalog.fitsY k a b)

/-- A complete macrocell pairing preserves every common-row and common-column source order. -/
theorem rail_order (k : Key) (l m : Labels k) :
    (((matching k).source l).2=((matching k).source m).2 →
      ((matching k).source l).1.val<((matching k).source m).1.val →((matching k).target l).1.val<((matching k).target m).1.val) ∧
    (((matching k).source l).1=((matching k).source m).1 →
      ((matching k).source l).2.val<((matching k).source m).2.val →((matching k).target l).2.val<((matching k).target m).2.val) := by
  cases k with
  | inl g=>exact full_rail_order g l m
  | inr a=>
    have hh:=catalog_coordinate_order a.1 a.2.1 a.2.2
    exact ⟨fun _ ho=>hh.1 l m ho,fun _ ho=>hh.2 l m ho⟩

end PushPuzzle.PushFS.Reduction.PhysicalTiles
