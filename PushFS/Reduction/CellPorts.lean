/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.WireLinks
public import PushFS.Reduction.CanonicalPhases

/-! Reciprocal physical faces of every actual source-cell instruction. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.CellPlan


open Cslib.Complexity.NCL Plan Gadgets.Wires

def Used : Code→Direction→Prop
  | none,_=>False
  | some (.inl (v,_)),d=>∃role,v.portDirection role=d
  | some (.inr (_,(k,_,_))),d=>d=(Catalog.sourceDirection k).opposite ∨d=Catalog.targetDirection k

theorem gate_sound {q : Source} {p : GridRouting.Point} {v : VertexData} {g : GateTileState}
    (hc : cell (q,p)=some (.inl (v,g))) :
    Raster.vertexAt (q.1,p)=some v ∧g=gateTileState (v,q.2) := by
  cases hv : Raster.vertexAt (q.1,p) with
  | none =>
    cases he : Raster.owner (q.1,p) with
    | none => simp only [cell,hv,ordinary,he,Option.elim_none] at hc; cases hc
    | some e =>
      cases hk : Raster.wireAt (q.1,(e,p)) <;>
        simp [cell,hv,ordinary,he,wireData,hk] at hc
  | some v' =>
    have hh : v'=v ∧gateTileState (v',q.2)=g := by
      simpa only [cell,hv,Option.elim_some,Option.some.injEq,Sum.inl.injEq,Prod.mk.injEq] using hc
    rcases hh with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl⟩

theorem wire_sound {q : Source} {p : GridRouting.Point} {e : ℕ} {k : Catalog.Kind} {a b : Bool}
    (hc : cell (q,p)=some (.inr (e,(k,a,b)))) :
    Raster.vertexAt (q.1,p)=none ∧Raster.owner (q.1,p)=some e ∧
      Raster.wireAt (q.1,(e,p))=some k ∧a=!(q.2.1.getD e false) ∧b=!(q.2.2.getD e false) := by
  cases hv : Raster.vertexAt (q.1,p) with
  | some v => simp [cell,hv] at hc
  | none =>
    cases he : Raster.owner (q.1,p) with
    | none => simp [cell,hv,ordinary,he] at hc
    | some e' =>
      cases hk : Raster.wireAt (q.1,(e',p)) with
      | none => simp [cell,hv,ordinary,he,wireData,hk] at hc
      | some k' =>
        have hh : e'=e ∧k'=k ∧(!(q.2.1.getD e' false))=a ∧(!(q.2.2.getD e' false))=b := by
          simpa only [cell,hv,ordinary,he,wireData,hk,Option.elim_none,Option.elim_some,
            Option.map_some,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq] using hc
        rcases hh with ⟨rfl,rfl,rfl,rfl⟩
        exact ⟨rfl,rfl,hk,rfl,rfl⟩

theorem of_wire (q : Source) (p : GridRouting.Point) {e : ℕ} {k : Catalog.Kind}
    (hv : Raster.vertexAt (q.1,p)=none) (he : Raster.owner (q.1,p)=some e)
    (hk : Raster.wireAt (q.1,(e,p))=some k) :
    cell (q,p)=some (.inr (e,(k,!(q.2.1.getD e false),!(q.2.2.getD e false)))) := by
  simp only [cell,hv,ordinary,he,wireData,hk,Option.elim_none,Option.elim_some,Option.map_some]

/-- Every used face meets a real source neighbor with the reciprocal used face. -/
theorem used_neighbor (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    (p : GridRouting.Point) (d : Direction) (hu : Used (cell (q,p)) d) :
    ∃r,neighbor d p=some r ∧Used (cell (q,r)) d.opposite := by
  cases hc : cell (q,p) with
  | none => rw [hc] at hu; exact hu.elim
  | some c =>
    rcases c with ⟨v,g⟩|⟨e,k,a,b⟩
    · obtain ⟨hv,_⟩ := gate_sound hc
      obtain ⟨hmem,rfl⟩ := Raster.vertexAt_sound hv
      rw [hc] at hu
      obtain ⟨role,rfl⟩ := hu
      cases hi : (v.ports.port role).dir
      · obtain ⟨r,k,hn,hr,hs,_,_⟩ := output_cell q hP hT hmem role hi
        refine ⟨r,hn,?_⟩
        rw [hr]
        exact Or.inl (congrArg Direction.opposite hs.symm)
      · obtain ⟨r,k,hn,hr,_,ht,_⟩ := input_cell q hP hT hmem role hi
        refine ⟨r,hn,?_⟩
        rw [hr]
        exact Or.inr ht.symm
    · obtain ⟨_,_,hk,_,_⟩ := wire_sound hc
      rw [hc] at hu
      rcases hu with rfl|rfl
      · obtain ⟨r,hn,hr⟩ := Raster.wire_source_neighbor hP hT hk
        refine ⟨r,hn,?_⟩
        rcases hr with ⟨k',hv,he,hk',ht⟩|⟨v,role,hv,_,_,hd⟩
        · rw [of_wire q r hv he hk']
          exact Or.inr (by simpa only [Direction.opposite_opposite] using ht.symm)
        · rw [cell_gate q r hv]
          exact ⟨role,by simpa only [Direction.opposite_opposite] using hd⟩
      · obtain ⟨r,hn,hr⟩ := Raster.wire_target_neighbor hP hT hk
        refine ⟨r,hn,?_⟩
        rcases hr with ⟨k',hv,he,hk',hs⟩|⟨v,role,hv,_,_,hd⟩
        · rw [of_wire q r hv he hk']
          exact Or.inl (congrArg Direction.opposite hs.symm)
        · rw [cell_gate q r hv]
          exact ⟨role,hd⟩

/-- Actual neighboring cells have exactly matching active physical faces. -/
theorem used_reciprocal (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r) :
    Used (cell (q,p)) d ↔Used (cell (q,r)) d.opposite := by
  constructor
  · intro hu
    obtain ⟨r',hr',hu'⟩ := used_neighbor q hP hT p d hu
    have he : r'=r := Option.some.inj (hr'.symm.trans hn)
    exact he ▸ hu'
  · intro hu
    obtain ⟨p',hp',hu'⟩ := used_neighbor q hP hT r d.opposite hu
    have he : p'=p := Option.some.inj (hp'.symm.trans (neighbor_reverse hn))
    simpa only [he,Direction.opposite_opposite] using hu'

end PushPuzzle.PushFS.Reduction.CellPlan
