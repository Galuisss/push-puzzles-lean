/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.SourcePortExact

/-! Actual ordinary-cell ports meet reciprocal same-edge ordinary or gate ports in the compiled source drawing. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


namespace Raster

open Cslib.Complexity.NCL Plan Gadgets.Wires

private theorem incoming_reciprocal {d : Direction} {p q : GridRouting.Point}
    (hn : neighbor d p=some q) (w : Word) (e : ℕ) :
    incoming d.opposite (w,(e,q))=outgoing d (w,(e,p)) := by
  rw [incoming_eq_neighbor,neighbor_reverse hn]
  simp only [Option.elim_some,Direction.opposite_opposite]

theorem wireAt_source_arc {w : Word} {e : ℕ} {p : GridRouting.Point} {k : Catalog.Kind}
    (hk : wireAt (w,(e,p))=some k) : incoming (Catalog.sourceDirection k).opposite (w,(e,p))=true := by
  have hh := congrArg (fun m : Mask=>m.get (Catalog.sourceDirection k).opposite)
    ((selectWire_correct _ _ k).mp hk).1
  simpa only [incomingMask_get,Mask.single_get,decide_true] using hh

theorem wireAt_target_arc {w : Word} {e : ℕ} {p : GridRouting.Point} {k : Catalog.Kind}
    (hk : wireAt (w,(e,p))=some k) : outgoing (Catalog.targetDirection k) (w,(e,p))=true := by
  have hh := congrArg (fun m : Mask=>m.get (Catalog.targetDirection k))
    ((selectWire_correct _ _ k).mp hk).2
  simpa only [outgoingMask_get,Mask.single_get,decide_true] using hh

/-- The exact two possible physical neighbors at an ordinary cell's target port. -/
theorem wire_target_neighbor {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {e : ℕ} {p : GridRouting.Point} {k : Catalog.Kind} (hk : wireAt (w,(e,p))=some k) :
    ∃ q,neighbor (Catalog.targetDirection k) p=some q ∧
      ((∃ k',vertexAt (w,q)=none ∧ owner (w,q)=some e ∧ wireAt (w,(e,q))=some k' ∧
          Catalog.sourceDirection k'=Catalog.targetDirection k) ∨
        (∃ v role,vertexAt (w,q)=some v ∧ (v.ports.port role).edge=e ∧ (v.ports.port role).dir=true ∧
          v.portDirection role=(Catalog.targetDirection k).opposite)) := by
  obtain ⟨q,hq,_,ht⟩ := outgoing_sound (wireAt_target_arc hk)
  have hi : incoming (Catalog.targetDirection k).opposite (w,(e,q))=true := by
    rw [incoming_reciprocal hq]
    exact wireAt_target_arc hk
  refine ⟨q,hq,?_⟩
  cases hv : vertexAt (w,q) with
  | none =>
    have he := owner_unique hP hT ((vertexAt_none_iff w q).mp hv) ht
    obtain ⟨k',hk'⟩ := wireAt_defined hP hT he hv
    exact Or.inl ⟨k',rfl,he,hk',by simpa only [Direction.opposite_opposite] using wireAt_incoming_direction hk' hi⟩
  | some v =>
    obtain ⟨hv',hp⟩ := vertexAt_sound hv
    have ha : HasIncoming (Route.edgeSegments (refinedProgram w,e))
        (Catalog.targetDirection k).opposite (refinePoint v.point) := by
      rw [hp]
      exact (incoming_named _ _ _ _).mp hi
    obtain ⟨role,he,hin,hd⟩ := vertexRecord_incoming_role hP hT hv' ha
    exact Or.inr ⟨v,role,rfl,he,hin,hd.symm⟩

/-- The exact two possible physical neighbors at an ordinary cell's source port. -/
theorem wire_source_neighbor {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {e : ℕ} {p : GridRouting.Point} {k : Catalog.Kind} (hk : wireAt (w,(e,p))=some k) :
    ∃ q,neighbor (Catalog.sourceDirection k).opposite p=some q ∧
      ((∃ k',vertexAt (w,q)=none ∧ owner (w,q)=some e ∧ wireAt (w,(e,q))=some k' ∧
          Catalog.targetDirection k'=Catalog.sourceDirection k) ∨
        (∃ v role,vertexAt (w,q)=some v ∧ (v.ports.port role).edge=e ∧ (v.ports.port role).dir=false ∧
          v.portDirection role=Catalog.sourceDirection k)) := by
  obtain ⟨q,hq,ho,_,ht⟩ := incoming_sound (wireAt_source_arc hk)
  have ho' : outgoing (Catalog.sourceDirection k) (w,(e,q))=true := by
    simpa only [Direction.opposite_opposite] using ho
  refine ⟨q,hq,?_⟩
  cases hv : vertexAt (w,q) with
  | none =>
    have he := owner_unique hP hT ((vertexAt_none_iff w q).mp hv) ht
    obtain ⟨k',hk'⟩ := wireAt_defined hP hT he hv
    exact Or.inl ⟨k',rfl,he,hk',wireAt_outgoing_direction hk' ho'⟩
  | some v =>
    obtain ⟨hv',hp⟩ := vertexAt_sound hv
    have ha : HasArc (Route.edgeSegments (refinedProgram w,e))
        (Catalog.sourceDirection k) (refinePoint v.point) := by
      rw [hp]
      exact (outgoing_named _ _ _ _).mp ho'
    obtain ⟨role,he,hout,hd⟩ := vertexRecord_outgoing_role hP hT hv' ha
    exact Or.inr ⟨v,role,rfl,he,hout,hd.symm⟩

end Raster

namespace CellPlan

end CellPlan
end PushPuzzle.PushFS.Reduction
