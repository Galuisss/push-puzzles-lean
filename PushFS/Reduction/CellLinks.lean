/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CellPorts

/-! Adjacent actual ordinary cells retain the same source edge and reciprocal flow orientation. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.CellPlan


open Cslib.Complexity.NCL Plan Gadgets.Wires

def Consecutive (k l : Catalog.Kind) (d : Direction) : Prop :=
  (Catalog.targetDirection k=d ∧Catalog.sourceDirection l=d) ∨
    (Catalog.sourceDirection k=d.opposite ∧Catalog.targetDirection l=d.opposite)

theorem wire_adjacent (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r)
    {e f : ℕ} {k l : Catalog.Kind} {a b c z : Bool}
    (hp : cell (q,p)=some (.inr (e,(k,a,b)))) (hr : cell (q,r)=some (.inr (f,(l,c,z))))
    (hu : Used (cell (q,p)) d) : e=f ∧Consecutive k l d := by
  obtain ⟨_,_,hk,_,_⟩ := wire_sound hp
  rw [hp] at hu
  rcases hu with rfl|rfl
  · obtain ⟨r',hn',hh⟩ := Raster.wire_source_neighbor hP hT hk
    have hrr : r'=r := Option.some.inj (hn'.symm.trans hn)
    subst r'
    rcases hh with ⟨k',hv,he,hk',ht⟩|⟨v,role,hv,_,_,_⟩
    · have hc := (of_wire q r hv he hk').symm.trans hr
      have hh : e=f ∧k'=l := by
        simpa only [Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq] using
          And.intro (congrArg Prod.fst (Sum.inr.inj (Option.some.inj hc)))
            (congrArg (fun w : Wire=>w.2.1) (Sum.inr.inj (Option.some.inj hc)))
      rcases hh with ⟨hef,rfl⟩
      exact ⟨hef,Or.inr ⟨(Direction.opposite_opposite _).symm,by simpa only [Direction.opposite_opposite] using ht⟩⟩
    · have hc := (cell_gate q r hv).symm.trans hr
      cases hc
  · obtain ⟨r',hn',hh⟩ := Raster.wire_target_neighbor hP hT hk
    have hrr : r'=r := Option.some.inj (hn'.symm.trans hn)
    subst r'
    rcases hh with ⟨k',hv,he,hk',hs⟩|⟨v,role,hv,_,_,_⟩
    · have hc := (of_wire q r hv he hk').symm.trans hr
      have hef : e=f := congrArg Prod.fst (Sum.inr.inj (Option.some.inj hc))
      have hkl : k'=l := congrArg (fun w : Wire=>w.2.1) (Sum.inr.inj (Option.some.inj hc))
      subst k'
      exact ⟨hef,Or.inl ⟨rfl,hs⟩⟩
    · have hc := (cell_gate q r hv).symm.trans hr
      cases hc

theorem gate_adjacent (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords q.1) (role : Fin 3) {r : GridRouting.Point}
    (hn : neighbor (v.portDirection role) (refinePoint v.point)=some r)
    {e : ℕ} {k : Catalog.Kind} {a b : Bool} (hc : cell (q,r)=some (.inr (e,(k,a,b)))) :
    (v.ports.port role).edge=e ∧
      (if (v.ports.port role).dir then Catalog.targetDirection k=(v.portDirection role).opposite
        else Catalog.sourceDirection k=v.portDirection role) := by
  cases hi : (v.ports.port role).dir
  · obtain ⟨r',k',hn',hc',hs,_,_⟩ := output_cell q hP hT hv role hi
    have hrr : r'=r := Option.some.inj (hn'.symm.trans hn)
    subst r'
    have hh := Sum.inr.inj (Option.some.inj (hc'.symm.trans hc))
    have he : (v.ports.port role).edge=e := congrArg Prod.fst hh
    have hk : k'=k := congrArg (fun w : Wire=>w.2.1) hh
    subst k'
    exact ⟨he,hs⟩
  · obtain ⟨r',k',hn',hc',_,ht,_⟩ := input_cell q hP hT hv role hi
    have hrr : r'=r := Option.some.inj (hn'.symm.trans hn)
    subst r'
    have hh := Sum.inr.inj (Option.some.inj (hc'.symm.trans hc))
    have he : (v.ports.port role).edge=e := congrArg Prod.fst hh
    have hk : k'=k := congrArg (fun w : Wire=>w.2.1) hh
    subst k'
    exact ⟨he,ht⟩

end PushPuzzle.PushFS.Reduction.CellPlan
