/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalWallContacts

/-! Unconditional wall compatibility of every complete tile in a checked actual source plan. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap

private theorem east_walls (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {k l : Key}
    (hk : key (CellPlan.cell (v,p))=some k) (hl : key (CellPlan.cell (v,r))=some l)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (hx : r.1=p.1+1) (hy : r.2=p.2) (he : coordinates p k q=coordinates r l s) :
    q∈(piece k).board.walls ↔s∈(piece l).board.walls := by
  have hn : neighbor .east p=some r := by
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hx.symm,hy.symm⟩
  have hu := used_reciprocal v hP hT hn hk hl
  rcases k with g|a <;> rcases l with h|b
  · have hp := gate_gate_overlap hk hl q s he
    have hh := congrArg Prod.fst hp
    omega
  · exact WallContacts.gate_wire_east p r g b q s hx hy he hu (gate_neighbor_straight v hP hT hn hk hl)
  · exact WallContacts.wire_gate_east p r a h q s hx hy he hu
      (gate_neighbor_straight v hP hT (neighbor_reverse hn) hl hk)
  · exact WallContacts.wire_east p r a b q s hx hy he hu

private theorem south_walls (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {k l : Key}
    (hk : key (CellPlan.cell (v,p))=some k) (hl : key (CellPlan.cell (v,r))=some l)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (hx : r.1=p.1) (hy : r.2=p.2+1) (he : coordinates p k q=coordinates r l s) :
    q∈(piece k).board.walls ↔s∈(piece l).board.walls := by
  have hn : neighbor .south p=some r := by
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hx.symm,hy.symm⟩
  have hu := used_reciprocal v hP hT hn hk hl
  rcases k with g|a <;> rcases l with h|b
  · have hp := gate_gate_overlap hk hl q s he
    have hh := congrArg Prod.snd hp
    omega
  · exact WallContacts.gate_wire_south p r g b q s hx hy he hu (gate_neighbor_straight v hP hT hn hk hl)
  · exact WallContacts.wire_gate_south p r a h q s hx hy he hu
      (gate_neighbor_straight v hP hT (neighbor_reverse hn) hl hk)
  · exact WallContacts.wire_south p r a b q s hx hy he hu

private theorem wire_corner_floor (a : Catalog.Bitmap.Args)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (hx : q.1.val<5 ∨200000≤q.1.val) (hy : q.2.val<5 ∨198061≤q.2.val) :
    q∉(piece (.inr a)).board.walls := by
  intro hw
  have hb := Catalog.wall_bounds a.1 a.2.1 a.2.2 hw
  rcases a with ⟨k,a,b⟩
  cases k <;> dsimp only [Catalog.WallRegion,Catalog.HorizontalBand,Catalog.VerticalBand] at hb <;> omega

private theorem wire_diagonal_floor (p r : GridRouting.Point) (a b : Catalog.Bitmap.Args)
    (q : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (s : Cell (piece (.inr b)).width (piece (.inr b)).height)
    (hx : p.1≠r.1) (hy : p.2≠r.2) (he : coordinates p (.inr a) q=coordinates r (.inr b) s) :
    q∉(piece (.inr a)).board.walls := by
  have hex := congrArg Prod.fst he
  have hey := congrArg Prod.snd he
  have hqx : q.1.val<200005 := q.1.isLt
  have hqy : q.2.val<198066 := q.2.isLt
  have hsx : s.1.val<200005 := s.1.isLt
  have hsy : s.2.val<198066 := s.2.isLt
  dsimp only [coordinates,offset,pad,strideX,strideY] at hex hey
  exact wire_corner_floor a q (by omega) (by omega)

/-- Every coincident real local cell has the same wall marker on the complete physical source layout. -/
theorem walls_compatible (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {k l : Key}
    (hk : key (CellPlan.cell (v,p))=some k) (hl : key (CellPlan.cell (v,r))=some l)
    (q : Cell (piece k).width (piece k).height) (s : Cell (piece l).width (piece l).height)
    (he : coordinates p k q=coordinates r l s) :
    q∈(piece k).board.walls ↔s∈(piece l).board.walls := by
  by_cases hp : p=r
  · subst r
    cases same_position_key hk hl
    cases same_position_cell he
    rfl
  have hn := overlap_neighbors p r k l q s he
  by_cases hx : p.1=r.1
  · have hy : p.2≠r.2 := fun hy=>hp (Prod.ext hx hy)
    rcases lt_or_gt_of_ne hy with hy|hy
    · exact south_walls v hP hT hk hl q s hx.symm (by omega) he
    · exact (south_walls v hP hT hl hk s q hx (by omega) he.symm).symm
  by_cases hy : p.2=r.2
  · rcases lt_or_gt_of_ne hx with hx|hx
    · exact east_walls v hP hT hk hl q s (by omega) hy.symm he
    · exact (east_walls v hP hT hl hk s q (by omega) hy he.symm).symm
  rcases k with g|a <;> rcases l with h|b
  · exact False.elim (hp (gate_gate_overlap hk hl q s he))
  · rcases gate_wire_overlap_axis hk hl q s he with hh|hh
    · exact False.elim (hx hh.symm)
    · exact False.elim (hy hh.symm)
  · rcases gate_wire_overlap_axis hl hk s q he.symm with hh|hh
    · exact False.elim (hx hh)
    · exact False.elim (hy hh)
  · exact iff_of_false (wire_diagonal_floor p r a b q s hx hy he)
      (wire_diagonal_floor r p b a s q (Ne.symm hx) (Ne.symm hy) he.symm)

end PushPuzzle.PushFS.Reduction.PhysicalTiles
