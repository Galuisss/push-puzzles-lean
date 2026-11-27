/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSeparatedContacts

/-! Adjacent canonical slots of the full actual physical source board share their source-cell owner. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap

private theorem east_neighbor {p r : GridRouting.Point} (hx : r.1=p.1+1) (hy : r.2=p.2) :
    neighbor .east p=some r := by
  simp only [neighbor,Option.some.injEq,Prod.ext_iff]
  exact ⟨hx.symm,hy.symm⟩

private theorem south_neighbor {p r : GridRouting.Point} (hx : r.1=p.1) (hy : r.2=p.2+1) :
    neighbor .south p=some r := by
  simp only [neighbor,Option.some.injEq,Prod.ext_iff]
  exact ⟨hx.symm,hy.symm⟩

private theorem gate_wire_near_owner (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (i : Labels (.inl g)) (j : Labels (.inr a))
    (he : Nearby 1 (coordinates p (.inl g) (slots goal (.inl g) i)) (coordinates r (.inr a) (slots goal (.inr a) j))) : p=r := by
  by_contra hp
  have hn := near_neighbors p r (.inl g) (.inr a) _ _ he
  rcases gate_wire_near_axis hg ha _ _ he with hx|hy
  · have hny : p.2≠r.2 := fun hy=>hp (Prod.ext hx.symm hy)
    rcases lt_or_gt_of_ne hny with hy|hy
    · exact SeparatedContacts.gate_wire v hP hT goal (south_neighbor hx (by omega)) hg ha i j he
    · exact SeparatedContacts.gate_wire v hP hT goal (neighbor_reverse (south_neighbor hx.symm (by omega))) hg ha i j he
  · have hnx : p.1≠r.1 := fun hx=>hp (Prod.ext hx hy.symm)
    rcases lt_or_gt_of_ne hnx with hx|hx
    · exact SeparatedContacts.gate_wire v hP hT goal (east_neighbor (by omega) hy) hg ha i j he
    · exact SeparatedContacts.gate_wire v hP hT goal (neighbor_reverse (east_neighbor (by omega) hy.symm)) hg ha i j he

private theorem wire_corner_slots (a : Catalog.Bitmap.Args) (goal : Bool) (i : Labels (.inr a))
    (hx : (slots goal (.inr a) i).1.val<6 ∨199999≤(slots goal (.inr a) i).1.val)
    (hy : (slots goal (.inr a) i).2.val<6 ∨198060≤(slots goal (.inr a) i).2.val) : False := by
  have hb := wire_slots_bounds a goal i
  rcases a with ⟨k,a,b⟩
  cases k <;> dsimp only [Catalog.SlotRegion,Catalog.SlotBounds] at hb <;> omega

private theorem wire_diagonal_near (p r : GridRouting.Point) (a b : Catalog.Bitmap.Args)
    (goal : Bool) (i : Labels (.inr a)) (j : Labels (.inr b))
    (hx : p.1≠r.1) (hy : p.2≠r.2)
    (he : Nearby 1 (coordinates p (.inr a) (slots goal (.inr a) i)) (coordinates r (.inr b) (slots goal (.inr b) j))) : False := by
  have hqx : (slots goal (.inr a) i).1.val<200005 := (slots goal (.inr a) i).1.isLt
  have hqy : (slots goal (.inr a) i).2.val<198066 := (slots goal (.inr a) i).2.isLt
  have hsx : (slots goal (.inr b) j).1.val<200005 := (slots goal (.inr b) j).1.isLt
  have hsy : (slots goal (.inr b) j).2.val<198066 := (slots goal (.inr b) j).2.isLt
  dsimp only [Nearby,coordinates,offset,pad,strideX,strideY] at he
  exact wire_corner_slots a goal i (by omega) (by omega)

/-- Coincident or adjacent actual source/target slots have the same physical source-cell owner. -/
theorem slot_near_owners (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {k l : Key}
    (hk : key (CellPlan.cell (v,p))=some k) (hl : key (CellPlan.cell (v,r))=some l)
    (i : Labels k) (j : Labels l)
    (he : Nearby 1 (coordinates p k (slots goal k i)) (coordinates r l (slots goal l j))) : p=r := by
  by_contra hp
  rcases k with g|a <;> rcases l with h|b
  · exact hp (gate_gate_near hk hl _ _ he)
  · exact hp (gate_wire_near_owner v hP hT goal hk hl i j he)
  · exact hp (gate_wire_near_owner v hP hT goal hl hk j i he.symm).symm
  · have hn := near_neighbors p r (.inr a) (.inr b) _ _ he
    by_cases hx : p.1=r.1
    · have hny : p.2≠r.2 := fun hy=>hp (Prod.ext hx hy)
      rcases lt_or_gt_of_ne hny with hy|hy
      · exact SeparatedContacts.wire_south v hP hT goal hk hl i j hx.symm (by omega) he
      · exact SeparatedContacts.wire_south v hP hT goal hl hk j i hx (by omega) he.symm
    by_cases hy : p.2=r.2
    · rcases lt_or_gt_of_ne hx with hx|hx
      · exact SeparatedContacts.wire_east v hP hT goal hk hl i j (by omega) hy.symm he
      · exact SeparatedContacts.wire_east v hP hT goal hl hk j i (by omega) hy he.symm
    exact wire_diagonal_near p r a b goal i j hx hy he

end PushPuzzle.PushFS.Reduction.PhysicalTiles
