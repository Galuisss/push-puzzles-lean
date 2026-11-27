/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalTiles

/-! Exact rectangle overlaps of the physical source-grid tiles. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL PhysicalBitmap

def coordinates (p : GridRouting.Point) (k : Key)
    (q : Cell (piece k).width (piece k).height) : ℕ×ℕ :=
  ((offset p k).1+q.1.val,(offset p k).2+q.2.val)

theorem pad_le_one (k : Key) : pad k≤1 := by cases k <;> simp only [pad] <;> omega

theorem coordinate_bounds (p : GridRouting.Point) (k : Key)
    (q : Cell (piece k).width (piece k).height) :
    strideX*p.1≤(coordinates p k q).1 ∧
    (coordinates p k q).1<strideX*p.1+strideX+7 ∧
    strideY*p.2≤(coordinates p k q).2 ∧
    (coordinates p k q).2<strideY*p.2+strideY+7 := by
  have hd := padded_dimensions k
  have hx := q.1.isLt
  have hy := q.2.isLt
  dsimp only [coordinates,offset]
  omega

/-- Coincident physical rectangles lie at equal or neighboring source-grid coordinates. -/
theorem overlap_neighbors (p r : GridRouting.Point) (k l : Key)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (he : coordinates p k q=coordinates r l s) :
    p.1≤r.1+1 ∧r.1≤p.1+1 ∧p.2≤r.2+1 ∧r.2≤p.2+1 := by
  have hp := coordinate_bounds p k q
  have hr := coordinate_bounds r l s
  rw [he] at hp
  dsimp only [strideX,strideY] at hp hr
  omega

/-- A same-row contact uses only the true eastern and western exterior collars. -/
private theorem east_overlap (p r : GridRouting.Point) (k l : Key)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2) (he : coordinates p k q=coordinates r l s) :
    strideX+pad l≤pad k+q.1.val ∧pad l+s.1.val<pad k+(dimensions k).1-strideX ∧
      pad k+q.2.val=pad l+s.2.val := by
  have hdx := (piece_dimensions k).1
  have hq := q.1.isLt
  have hex := congrArg Prod.fst he
  have hey := congrArg Prod.snd he
  dsimp only [coordinates,offset] at hex hey
  rw [hx,Nat.mul_add,Nat.mul_one] at hex
  rw [hy] at hey
  omega

/-- Two ordinary neighbors overlap in exactly their five-column frames. -/
theorem east_wire_overlap (p r : GridRouting.Point) (a b : Gadgets.Wires.Catalog.Bitmap.Args)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inr b)).width (piece (.inr b)).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2)
    (he : coordinates p (.inr a) q=coordinates r (.inr b) s) :
    200000≤q.1.val ∧s.1.val<5 ∧q.2.val=s.2.val := by
  have hh := east_overlap p r (.inr a) (.inr b) q s hx hy he
  dsimp only [pad,dimensions,strideX] at hh
  omega

/-- A pad3 gate followed by an ordinary tile has a six-column true contact. -/
theorem east_gate_wire_overlap (p r : GridRouting.Point) (g : GateTileState)
    (a : Gadgets.Wires.Catalog.Bitmap.Args)
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2)
    (he : coordinates p (.inl g) q=coordinates r (.inr a) s) :
    200001≤q.1.val ∧s.1.val<6 ∧q.2.val=1+s.2.val := by
  have hh := east_overlap p r (.inl g) (.inr a) q s hx hy he
  dsimp only [pad,dimensions,strideX] at hh
  omega

/-- An ordinary tile followed by a pad3 gate uses the ordinary tile's last six columns. -/
theorem east_wire_gate_overlap (p r : GridRouting.Point) (a : Gadgets.Wires.Catalog.Bitmap.Args)
    (g : GateTileState)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2)
    (he : coordinates p (.inr a) q=coordinates r (.inl g) s) :
    199999≤q.1.val ∧s.1.val<6 ∧1+q.2.val=s.2.val := by
  have hh := east_overlap p r (.inr a) (.inl g) q s hx hy he
  dsimp only [pad,dimensions,strideX] at hh
  omega

/-- A same-column contact uses the true southern and northern exterior collars. -/
private theorem south_overlap (p r : GridRouting.Point) (k l : Key)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1) (he : coordinates p k q=coordinates r l s) :
    strideY+pad l≤pad k+q.2.val ∧pad l+s.2.val<pad k+(dimensions k).2-strideY ∧
      pad k+q.1.val=pad l+s.1.val := by
  have hdy := (piece_dimensions k).2
  have hq := q.2.isLt
  have hex := congrArg Prod.fst he
  have hey := congrArg Prod.snd he
  dsimp only [coordinates,offset] at hex hey
  rw [hy,Nat.mul_add,Nat.mul_one] at hey
  rw [hx] at hex
  omega

theorem south_wire_overlap (p r : GridRouting.Point) (a b : Gadgets.Wires.Catalog.Bitmap.Args)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inr b)).width (piece (.inr b)).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1)
    (he : coordinates p (.inr a) q=coordinates r (.inr b) s) :
    198061≤q.2.val ∧s.2.val<5 ∧q.1.val=s.1.val := by
  have hh := south_overlap p r (.inr a) (.inr b) q s hx hy he
  dsimp only [pad,dimensions,strideY] at hh
  omega

theorem south_gate_wire_overlap (p r : GridRouting.Point) (g : GateTileState)
    (a : Gadgets.Wires.Catalog.Bitmap.Args)
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1)
    (he : coordinates p (.inl g) q=coordinates r (.inr a) s) :
    198062≤q.2.val ∧s.2.val<6 ∧q.1.val=1+s.1.val := by
  have hh := south_overlap p r (.inl g) (.inr a) q s hx hy he
  dsimp only [pad,dimensions,strideY] at hh
  omega

theorem south_wire_gate_overlap (p r : GridRouting.Point) (a : Gadgets.Wires.Catalog.Bitmap.Args)
    (g : GateTileState)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1)
    (he : coordinates p (.inr a) q=coordinates r (.inl g) s) :
    198060≤q.2.val ∧s.2.val<6 ∧1+q.1.val=s.1.val := by
  have hh := south_overlap p r (.inr a) (.inl g) q s hx hy he
  dsimp only [pad,dimensions,strideY] at hh
  omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles
