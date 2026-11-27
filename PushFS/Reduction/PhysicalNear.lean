/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSlotOwners

/-! Source-grid contact geometry for adjacent as well as coincident physical cells. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


theorem Nearby.symm {n : ℕ} {p r : ℕ×ℕ} (h : Nearby n p r) : Nearby n r p :=
  ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

end PushPuzzle.PushFS.Reduction

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL Plan PhysicalBitmap

theorem near_neighbors (p r : GridRouting.Point) (k l : Key)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (he : Nearby 1 (coordinates p k q) (coordinates r l s)) :
    p.1≤r.1+1 ∧r.1≤p.1+1 ∧p.2≤r.2+1 ∧r.2≤p.2+1 := by
  have hp := coordinate_bounds p k q
  have hr := coordinate_bounds r l s
  dsimp only [Nearby,strideX,strideY] at he hp hr
  omega

theorem gate_gate_near {v : CellPlan.Source} {p r : GridRouting.Point} {g h : GateTileState}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (hh : key (CellPlan.cell (v,r))=some (.inl h))
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inl h)).width (piece (.inl h)).height)
    (he : Nearby 1 (coordinates p (.inl g) q) (coordinates r (.inl h) s)) : p=r := by
  obtain ⟨a,ha⟩ := gate_code hg
  obtain ⟨b,hb⟩ := gate_code hh
  obtain ⟨_,hap⟩ := Raster.vertexAt_sound (CellPlan.gate_sound ha).1
  obtain ⟨_,hbr⟩ := Raster.vertexAt_sound (CellPlan.gate_sound hb).1
  have hn := near_neighbors p r (.inl g) (.inl h) q s he
  rw [←hap,←hbr] at hn
  exact hap.symm.trans ((refinePoint_near_eq ⟨hn.1,hn.2.1⟩ ⟨hn.2.2.1,hn.2.2.2⟩).trans hbr)

theorem gate_wire_near_axis {v : CellPlan.Source} {p r : GridRouting.Point} {g : GateTileState}
    {a : Gadgets.Wires.Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (he : Nearby 1 (coordinates p (.inl g) q) (coordinates r (.inr a) s)) : r.1=p.1 ∨r.2=p.2 := by
  obtain ⟨b,hb⟩ := gate_code hg
  obtain ⟨e,hc⟩ := wire_code ha
  obtain ⟨_,hbp⟩ := Raster.vertexAt_sound (CellPlan.gate_sound hb).1
  have ht := Raster.owner_sound (CellPlan.wire_sound hc).2.1
  have hn := near_neighbors p r (.inl g) (.inr a) q s he
  rw [←hbp] at hn ⊢
  exact Raster.trace_near_anchor ht ⟨hn.2.1,hn.1⟩ ⟨hn.2.2.2,hn.2.2.1⟩

theorem gate_wire_near_frame (p r : GridRouting.Point) (g : GateTileState)
    (a : Gadgets.Wires.Catalog.Bitmap.Args) (d : Direction) (hn : neighbor d p=some r)
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (he : Nearby 1 (coordinates p (.inl g) q) (coordinates r (.inr a) s)) :
    GateTileRouting.FullGateBoundary.InFrame d (q.1.val,q.2.val) := by
  have hqx : q.1.val<200007 := q.1.isLt
  have hqy : q.2.val<198068 := q.2.isLt
  have hsx : s.1.val<200005 := s.1.isLt
  have hsy : s.2.val<198066 := s.2.isLt
  cases d <;> dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [Nearby,coordinates,offset,pad,strideX,strideY,GateTileRouting.FullGateBoundary.InFrame] at he ⊢
  all_goals omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles
