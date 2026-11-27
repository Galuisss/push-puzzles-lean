/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalOverlap
public import PushFS.Reduction.CellExterior
public import PushFS.Reduction.FullGateBoundary
public import PushFS.Gadgets.Wires.Catalog.StraightSix

/-! Actual source instructions bind the physical tile faces and all six-cell gate contacts. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Plan Gadgets.Wires

def face : Direction→Catalog.Face
  | .west=>.west | .east=>.east | .north=>.north | .south=>.south

def Used : Key→Direction→Prop
  | .inl g,d=>GateTileRouting.FullGateBoundary.Used g d
  | .inr q,d=>Catalog.FaceUsed q.1 (face d)

private theorem wire_used (k : Catalog.Kind) (d : Direction) :
    Catalog.FaceUsed k (face d) ↔d=(Catalog.sourceDirection k).opposite ∨d=Catalog.targetDirection k := by
  cases k <;> cases d <;> decide

theorem gate_code {c : CellPlan.Code} {g : GateTileState} (hk : key c=some (.inl g)) :
    ∃v,c=some (.inl (v,g)) := by
  rcases c with _| (⟨v,g'⟩|w)
  · cases hk
  · cases hk
    exact ⟨v,rfl⟩
  · cases hk

theorem wire_code {c : CellPlan.Code} {a : Catalog.Bitmap.Args} (hk : key c=some (.inr a)) :
    ∃e,c=some (.inr (e,a)) := by
  rcases c with _| (g|⟨e,a'⟩)
  · cases hk
  · cases hk
  · cases hk
    exact ⟨e,rfl⟩

/-- The real physical wall-face predicate reads exactly the actual compiler's active ports. -/
theorem used_key {q : CellPlan.Source} {p : GridRouting.Point} {k : Key}
    (hk : key (CellPlan.cell (q,p))=some k) (d : Direction) :
    Used k d ↔CellPlan.Used (CellPlan.cell (q,p)) d := by
  rcases k with g|a
  · obtain ⟨v,hc⟩ := gate_code hk
    obtain ⟨_,rfl⟩ := CellPlan.gate_sound hc
    rw [hc]
    rfl
  · obtain ⟨e,hc⟩ := wire_code hk
    rw [hc]
    exact wire_used a.1 d

theorem used_reciprocal (q : CellPlan.Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r) {k l : Key}
    (hk : key (CellPlan.cell (q,p))=some k) (hl : key (CellPlan.cell (q,r))=some l) :
    Used k d ↔Used l d.opposite :=
  (used_key hk d).trans ((CellPlan.used_reciprocal q hP hT hn).trans (used_key hl d.opposite).symm)

/-- Every real ordinary tile adjacent to a gate is one of the three straight physical glyphs. -/
theorem gate_neighbor_straight (q : CellPlan.Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r) {g : GateTileState}
    {a : Catalog.Bitmap.Args} (hg : key (CellPlan.cell (q,p))=some (.inl g))
    (ha : key (CellPlan.cell (q,r))=some (.inr a)) : Catalog.Straight a.1 := by
  obtain ⟨v,hgc⟩ := gate_code hg
  obtain ⟨hgv,_⟩ := CellPlan.gate_sound hgc
  obtain ⟨hv,hvp⟩ := Raster.vertexAt_sound hgv
  obtain ⟨e,hac⟩ := wire_code ha
  obtain ⟨_,he,hka,_,_⟩ := CellPlan.wire_sound hac
  rw [←hvp] at hn
  obtain ⟨role,_,hd⟩ := vertexRecord_neighbor_role hP hT hv hn (Raster.owner_sound he)
  rw [hd] at hn
  cases hi : (v.ports.port role).dir
  · obtain ⟨r',k',hn',_,howner,hk',_,_,hs⟩ := Raster.gate_output_straight hP hT hv role hi
    have hr : r'=r := Option.some.inj (hn'.symm.trans hn)
    subst r'
    have hedge : (v.ports.port role).edge=e := Option.some.inj (howner.symm.trans he)
    rw [hedge,hka] at hk'
    cases Option.some.inj hk'
    exact hs
  · obtain ⟨r',k',hn',_,howner,hk',_,_,hs⟩ := Raster.gate_input_straight hP hT hv role hi
    have hr : r'=r := Option.some.inj (hn'.symm.trans hn)
    subst r'
    have hedge : (v.ports.port role).edge=e := Option.some.inj (howner.symm.trans he)
    rw [hedge,hka] at hk'
    cases Option.some.inj hk'
    exact hs

end PushPuzzle.PushFS.Reduction.PhysicalTiles
