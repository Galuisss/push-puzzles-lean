/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSourceGeometry

/-! Exact physical wall contacts of the actual five-cell and six-cell source-grid seams. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles.WallContacts


open Cslib.Complexity.NCL Gadgets.Wires

theorem wire_east (p r : GridRouting.Point) (a b : Catalog.Bitmap.Args)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inr b)).width (piece (.inr b)).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2) (he : coordinates p (.inr a) q=coordinates r (.inr b) s)
    (hu : Used (.inr a) .east ↔Used (.inr b) .west) :
    q∈(piece (.inr a)).board.walls ↔s∈(piece (.inr b)).board.walls := by
  have hh := east_wire_overlap p r a b q s hx hy he
  have hq := Catalog.boundary_walls a.1 a.2.1 a.2.2 .east q hh.1
  have hs := Catalog.boundary_walls b.1 b.2.1 b.2.2 .west s hh.2.1
  have hg : Catalog.FaceGuard .east q ↔Catalog.FaceGuard .west s := by
    change (q.2.val=99034 ∨q.2.val=99035) ↔s.2.val=99034 ∨s.2.val=99035
    rw [hh.2.2]
  exact hq.trans ((and_congr hu hg).trans hs.symm)

theorem wire_south (p r : GridRouting.Point) (a b : Catalog.Bitmap.Args)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inr b)).width (piece (.inr b)).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1) (he : coordinates p (.inr a) q=coordinates r (.inr b) s)
    (hu : Used (.inr a) .south ↔Used (.inr b) .north) :
    q∈(piece (.inr a)).board.walls ↔s∈(piece (.inr b)).board.walls := by
  have hh := south_wire_overlap p r a b q s hx hy he
  have hq := Catalog.boundary_walls a.1 a.2.1 a.2.2 .south q hh.1
  have hs := Catalog.boundary_walls b.1 b.2.1 b.2.2 .north s hh.2.1
  have hg : Catalog.FaceGuard .south q ↔Catalog.FaceGuard .north s := by
    change (q.1.val=100000 ∨q.1.val=100001) ↔s.1.val=100000 ∨s.1.val=100001
    rw [hh.2.2]
  exact hq.trans ((and_congr hu hg).trans hs.symm)

theorem gate_wire_east (p r : GridRouting.Point) (g : GateTileState) (a : Catalog.Bitmap.Args)
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2) (he : coordinates p (.inl g) q=coordinates r (.inr a) s)
    (hu : Used (.inl g) .east ↔Used (.inr a) .west) (ha : Catalog.Straight a.1) :
    q∈(piece (.inl g)).board.walls ↔s∈(piece (.inr a)).board.walls := by
  have hh := east_gate_wire_overlap p r g a q s hx hy he
  have hq := GateTileRouting.FullGateBoundary.walls g .east q (by change 200000≤q.1.val; omega)
  have hs := Catalog.six_walls a.1 ha a.2.1 a.2.2 .west s hh.2.1
  have hg : GateTileRouting.FullGateBoundary.Guard .east (q.1.val,q.2.val) ↔Catalog.FaceGuard .west s := by
    change (q.2.val=99035 ∨q.2.val=99036) ↔s.2.val=99034 ∨s.2.val=99035
    omega
  exact hq.trans ((and_congr hu hg).trans hs.symm)

theorem wire_gate_east (p r : GridRouting.Point) (a : Catalog.Bitmap.Args) (g : GateTileState)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2) (he : coordinates p (.inr a) q=coordinates r (.inl g) s)
    (hu : Used (.inr a) .east ↔Used (.inl g) .west) (ha : Catalog.Straight a.1) :
    q∈(piece (.inr a)).board.walls ↔s∈(piece (.inl g)).board.walls := by
  have hh := east_wire_gate_overlap p r a g q s hx hy he
  have hq := Catalog.six_walls a.1 ha a.2.1 a.2.2 .east q hh.1
  have hs := GateTileRouting.FullGateBoundary.walls g .west s (by change s.1.val<7; omega)
  have hg : Catalog.FaceGuard .east q ↔GateTileRouting.FullGateBoundary.Guard .west (s.1.val,s.2.val) := by
    change (q.2.val=99034 ∨q.2.val=99035) ↔s.2.val=99035 ∨s.2.val=99036
    omega
  exact hq.trans ((and_congr hu hg).trans hs.symm)

theorem gate_wire_south (p r : GridRouting.Point) (g : GateTileState) (a : Catalog.Bitmap.Args)
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1) (he : coordinates p (.inl g) q=coordinates r (.inr a) s)
    (hu : Used (.inl g) .south ↔Used (.inr a) .north) (ha : Catalog.Straight a.1) :
    q∈(piece (.inl g)).board.walls ↔s∈(piece (.inr a)).board.walls := by
  have hh := south_gate_wire_overlap p r g a q s hx hy he
  have hq := GateTileRouting.FullGateBoundary.walls g .south q (by change 198061≤q.2.val; omega)
  have hs := Catalog.six_walls a.1 ha a.2.1 a.2.2 .north s hh.2.1
  have hg : GateTileRouting.FullGateBoundary.Guard .south (q.1.val,q.2.val) ↔Catalog.FaceGuard .north s := by
    change (q.1.val=100001 ∨q.1.val=100002) ↔s.1.val=100000 ∨s.1.val=100001
    omega
  exact hq.trans ((and_congr hu hg).trans hs.symm)

theorem wire_gate_south (p r : GridRouting.Point) (a : Catalog.Bitmap.Args) (g : GateTileState)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1) (he : coordinates p (.inr a) q=coordinates r (.inl g) s)
    (hu : Used (.inr a) .south ↔Used (.inl g) .north) (ha : Catalog.Straight a.1) :
    q∈(piece (.inr a)).board.walls ↔s∈(piece (.inl g)).board.walls := by
  have hh := south_wire_gate_overlap p r a g q s hx hy he
  have hq := Catalog.six_walls a.1 ha a.2.1 a.2.2 .south q hh.1
  have hs := GateTileRouting.FullGateBoundary.walls g .north s (by change s.2.val<7; omega)
  have hg : Catalog.FaceGuard .south q ↔GateTileRouting.FullGateBoundary.Guard .north (s.1.val,s.2.val) := by
    change (q.1.val=100000 ∨q.1.val=100001) ↔s.1.val=100001 ∨s.1.val=100002
    omega
  exact hq.trans ((and_congr hu hg).trans hs.symm)

end PushPuzzle.PushFS.Reduction.PhysicalTiles.WallContacts
