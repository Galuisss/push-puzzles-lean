/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Emission
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance

/-!
# Finite native graph input to the actual strip sweep

The routing context contains the existing finite AND/OR graph data and its source/owner row
metadata. The environment is computed by `PushPuzzle.NCL.Strip.ofConstraintGraph`; geometric properties and
sweep interfaces are derived from that computation.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context`: native source graph and row metadata.
* `PushPuzzle.NCL.Strip.Sweep.Context.environment`: actual parity-track routing.
* `PushPuzzle.NCL.Strip.Sweep.Context.program`: the actual standard planar instruction expansion.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- Existing finite source graph data together with the row metadata used by the routing algorithm.
-/
structure Context (A K : ℕ) where
  /-- The existing natural-numbered finite graph representation. -/
  source : AndOrGraph
  /-- Standard source validity, including opposite endpoints and loop freedom. -/
  valid : SourceValid source
  /-- Source panel of each vertex in the finite interpreted vertex list. -/
  vertexRows : Fin (List.ofFn source.graph).length → ℕ
  /-- Owner panel of each original edge. -/
  ownerRows : Fin source.edgeCount → ℕ
  /-- Vertex-slot capacity in each source panel. -/
  vertexCapacity : ∀ r, Fintype.card {i // vertexRows i = r} ≤ A
  /-- Edge-slot capacity in each owner panel. -/
  ownerCapacity : ∀ r, Fintype.card {e // ownerRows e = r} ≤ K
  /-- Every original endpoint lies in its owner's panel or the following panel. -/
  endpointRows : ∀ i p, p ∈ ((List.ofFn source.graph).get i).ports →
    ownerRows p.1.edge ≤ vertexRows i ∧ vertexRows i ≤ ownerRows p.1.edge + 1

namespace Context

open Cslib.Complexity Cslib.Complexity.NCL

variable {A K : ℕ} (C : Context A K)

/-- The actual finite vertex records obtained from the native input graph. -/
@[expose] def vertices : List (Vertex (Fin C.source.edgeCount)) := List.ofFn C.source.graph

/-- The same native graph reindexed by its explicit finite vertex list. -/
@[expose] def graph :
    ConstraintGraph (Fin C.vertices.length) (Fin C.source.edgeCount) := C.vertices.get

private theorem graph_eq : C.graph = C.source.graph ∘ finCongr List.length_ofFn :=
  funext (List.get_ofFn C.source.graph)

/-- Every original interpreted vertex has its native standard AND/OR kind. -/
theorem isAndOr : ∀ v ∈ C.vertices, v.IsAndOr := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact C.valid.isAndOr i

/-- The actual finite interpreted vertex list has the native input's well-formedness. -/
theorem wellFormed : C.graph.WellFormed := by
  rw [graph_eq]
  exact C.valid.wellFormed.reindex _

/-- The actual finite interpreted vertex list has the native input's loop freedom. -/
theorem loopFree : C.graph.LoopFree := by
  rw [graph_eq]
  exact fun i => C.valid.loopFree _

/-- The original source vertices each have three ports. -/
theorem arity (i : Fin C.vertices.length) : (C.graph i).ports.length = 3 :=
  (C.isAndOr _ (List.get_mem _ _)).shape.1

/-- Compute the actual fixed-track routing directly from the native graph and its row metadata. -/
@[expose] def environment :
    Environment (Fin C.vertices.length) (Fin C.source.edgeCount) A K :=
  ofConstraintGraph C.vertices C.wellFormed C.loopFree (fun i => (C.arity i).le)
    C.vertexRows C.ownerRows C.vertexCapacity C.ownerCapacity C.endpointRows

/-- The original edge color obtained by scanning the actual interpreted port data. -/
@[expose] def color : Fin C.source.edgeCount → Color := Planar.Embedding.color C.vertices

/-- Every original weighted port has the color assigned by the actual native graph scan. -/
theorem port_weight {i : Fin C.vertices.length} {p : WeightedPort (Fin C.source.edgeCount)}
    (hp : p ∈ (C.graph i).ports) : p.2 = (C.color p.1.edge).weight :=
  Planar.Embedding.port_weight_color C.isAndOr C.wellFormed (List.get_mem _ _) hp

/-- The actual unit-arc labels on the native source's frontier at one scan cut. -/
@[expose] def frontier (t : ℤ) : List (Arc C.environment) :=
  PushPuzzle.NCL.Strip.Sweep.frontier C.environment (List.finRange C.source.edgeCount) t

/-- Emit the actual standard plane-word expansion of the native source graph's grid scan. -/
@[expose] def program : Word :=
  Sweep.program C.environment C.graph C.arity C.color
    (List.finRange C.vertices.length) (List.finRange C.source.edgeCount)

/-- Every emitted primitive is an actual standard plane cell. -/
theorem program_checkPlane : C.program.checkPlane = true :=
  PushPuzzle.NCL.Strip.Sweep.program_checkPlane C.environment C.graph C.arity C.color _ _

/-- The original weighted port in one of its three actual list slots. -/
@[expose] def sourcePort (i : Fin C.vertices.length) (s : Fin 3) :
    WeightedPort (Fin C.source.edgeCount) := (C.graph i).ports.get (s.cast (C.arity i).symm)

/-- The three actual original port-list entries, in their original order. -/
theorem source_port_list (i : Fin C.vertices.length) :
    (C.graph i).ports = [C.sourcePort i 0, C.sourcePort i 1, C.sourcePort i 2] := by
  have h : List.ofFn (C.sourcePort i) = (C.graph i).ports := by
    unfold sourcePort
    rw [List.ofFn_congr (C.arity i).symm]
    simpa only [Fin.cast_cast, Fin.cast_refl, id_eq] using List.ofFn_get (C.graph i).ports
  simpa only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    using h.symm

private theorem source_color_pattern (i : Fin C.vertices.length) :
    [(C.color (C.sourcePort i 0).1.edge).weight,
      (C.color (C.sourcePort i 1).1.edge).weight,
      (C.color (C.sourcePort i 2).1.edge).weight] ∈
        ([[1, 1, 2], [1, 2, 1], [2, 1, 1], [2, 2, 2]] : List (List ℕ)) := by
  have h := (Vertex.checkAndOr_eq_true_iff (C.graph i)).mpr
    (C.isAndOr _ (List.get_mem _ _))
  simp only [Vertex.checkAndOr, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  have hw (s : Fin 3) : (C.sourcePort i s).2 = (C.color (C.sourcePort i s).1.edge).weight :=
    C.port_weight (List.get_mem _ _)
  simpa only [C.source_port_list i, List.map_cons, List.map_nil, hw] using h.2

/-- The local source fragment retains the colors of the actual incoming/outgoing source arcs. -/
theorem source_fragment_interfaces (i : Fin C.vertices.length) :
    let g := PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.source i)
    let s := slice C.environment (List.finRange C.source.edgeCount) (C.environment.center i)
    g.inputs = s.incoming.map (fun a => C.color a.edge) ∧
      g.outputs = s.outgoing.map (fun a => C.color a.edge) := by
  have h := PushPuzzle.NCL.Strip.Sweep.source_cell C.vertices C.wellFormed C.loopFree C.isAndOr C.vertexRows C.ownerRows
    C.vertexCapacity C.ownerCapacity C.endpointRows i
  have hports :
      (slice C.environment (List.finRange C.source.edgeCount) (C.environment.center i)).incoming =
          [portArc C.environment (C.sourcePort i 0).1.edge (C.sourcePort i 0).1.dir] ∧
        (slice C.environment (List.finRange C.source.edgeCount) (C.environment.center i)).outgoing =
          [portArc C.environment (C.sourcePort i 1).1.edge (C.sourcePort i 1).1.dir,
            portArc C.environment (C.sourcePort i 2).1.edge (C.sourcePort i 2).1.dir] :=
      ⟨h.1, h.2.1⟩
  have hc := PushPuzzle.NCL.Strip.Sweep.Cell.sourceColors_spec _ _ _ (C.source_color_pattern i)
  dsimp only
  rw [hports.1, hports.2]
  simpa only [PushPuzzle.NCL.Strip.Sweep.Site.fragment, List.map_cons, List.map_nil, (portArc_spec C.environment _ _).1,
    sourcePort] using hc

/-- The actual crossing fragment has exactly the colors of its two geometric frontier blocks. -/
theorem crossing_fragment_interfaces {c : Event (Fin C.source.edgeCount)}
    (hc : c ∈ C.environment.events (List.finRange C.source.edgeCount)) :
    let g := PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.crossing c)
    let s := slice C.environment (List.finRange C.source.edgeCount) (c.site C.environment)
    g.inputs = s.incoming.map (fun a => C.color a.edge) ∧
      g.outputs = s.outgoing.map (fun a => C.color a.edge) := by
  have h := crossing_slice C.environment (List.nodup_finRange _) hc
  have hi := congrArg (List.map C.color) h.1
  have ho := congrArg (List.map C.color) h.2
  simp only [List.map_map, List.map_cons, List.map_nil, Function.comp_def] at hi ho
  exact ⟨hi.symm, ho.symm⟩

/-- A selected ordinary port lies on its carrier, away from every source and actual crossing. -/
theorem wire_geometry {p : Cslib.Orthogonal.Point} {a : Arc C.environment}
    (hv : centerAt C.environment (List.finRange C.vertices.length) p = none)
    (hc : C.environment.eventAt (List.finRange C.source.edgeCount) p = none)
    (hp : ((slice C.environment (List.finRange C.source.edgeCount) p).incoming ++
      (slice C.environment (List.finRange C.source.edgeCount) p).outgoing).head? = some a) :
    p ∈ C.environment.unitRoute a.edge ∧
      (∀ v, p ≠ C.environment.center v) ∧
        ∀ c ∈ C.environment.events (List.finRange C.source.edgeCount),
          p ≠ c.site C.environment := by
  let R := C.environment
  let es := List.finRange C.source.edgeCount
  let s := slice R es p
  have hcenters : ∀ v, p ≠ R.center v := by
    intro v he
    have hn := List.find?_eq_none.mp hv v (List.mem_finRange v)
    simp only [decide_eq_true_eq] at hn
    exact hn he.symm
  have hcross : ∀ c ∈ R.events es, p ≠ c.site R := by
    intro c hm he
    have hh := (R.eventAt_eq_some es p c).mpr ⟨hm, he.symm⟩
    rw [hc] at hh
    cases hh
  have ham : a ∈ s.incoming ++ s.outgoing := List.mem_of_head? hp
  have hat : a.edge ∈ es ∧ (a.lower R = p ∨ a.upper R = p) := by
    rcases List.mem_append.mp ham with ha | ha
    · have h := (mem_slice_incoming R es p a).mp ha
      exact ⟨h.1, Or.inr h.2⟩
    · have h := (mem_slice_outgoing R es p a).mp ha
      exact ⟨h.1, Or.inl h.2⟩
  have hap : p ∈ R.unitRoute a.edge := by
    apply (R.mem_unitRoute a.edge p).mpr
    rcases hat.2 with ha | ha
    · exact ha ▸ (a.canonical_endpoints_mem R).1
    · exact ha ▸ (a.canonical_endpoints_mem R).2
  exact ⟨hap, hcenters, hcross⟩

/-- An actual ordinary cell has two ports, both retaining its original carrier's color. -/
theorem wire_port_data {p : Cslib.Orthogonal.Point} {a : Arc C.environment}
    (hv : centerAt C.environment (List.finRange C.vertices.length) p = none)
    (hc : C.environment.eventAt (List.finRange C.source.edgeCount) p = none)
    (hp : ((slice C.environment (List.finRange C.source.edgeCount) p).incoming ++
      (slice C.environment (List.finRange C.source.edgeCount) p).outgoing).head? = some a) :
    let s := slice C.environment (List.finRange C.source.edgeCount) p
    s.incoming.length + s.outgoing.length = 2 ∧
      s.incoming.map (fun b => C.color b.edge) = List.replicate s.incoming.length (C.color a.edge) ∧
      s.outgoing.map (fun b => C.color b.edge) =
        List.replicate s.outgoing.length (C.color a.edge) := by
  let R := C.environment
  let es := List.finRange C.source.edgeCount
  let s := slice R es p
  obtain ⟨hap, hcenters, hcross⟩ := C.wire_geometry hv hc hp
  have ham : a ∈ s.incoming ++ s.outgoing := List.mem_of_head? hp
  obtain ⟨e, _, hl, he⟩ := wire_slice R (List.nodup_finRange _)
    ⟨a.edge, List.mem_finRange _, hap⟩ hcenters hcross
  have hea : a.edge = e := he a ham
  have hi : s.incoming.map (fun b => C.color b.edge) =
      List.replicate s.incoming.length (C.color a.edge) := by
    apply List.map_eq_replicate_iff.mpr
    intro b hb
    exact congrArg C.color ((he b (List.mem_append_left _ hb)).trans hea.symm)
  have ho : s.outgoing.map (fun b => C.color b.edge) =
      List.replicate s.outgoing.length (C.color a.edge) := by
    apply List.map_eq_replicate_iff.mpr
    intro b hb
    exact congrArg C.color ((he b (List.mem_append_right _ hb)).trans hea.symm)
  exact ⟨by simpa only [List.length_append] using hl, hi, ho⟩

/-- Every computed cell selection retains the actual incoming and outgoing frontier colors. -/
theorem selection_interfaces {p : Cslib.Orthogonal.Point}
    {s : Site (Fin C.vertices.length) (Fin C.source.edgeCount)}
    (hs : Selection C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p (some s)) :
    (s.fragment C.graph C.arity C.color).inputs =
        (slice C.environment (List.finRange C.source.edgeCount) p).incoming.map
          (fun a => C.color a.edge) ∧
      (s.fragment C.graph C.arity C.color).outputs =
        (slice C.environment (List.finRange C.source.edgeCount) p).outgoing.map
          (fun a => C.color a.edge) := by
  cases hs with
  | source v hv =>
    have hpoint := ((centerAt_eq_some C.environment _ p v).mp hv).2
    simpa only [hpoint] using C.source_fragment_interfaces v
  | crossing c _ hc =>
    obtain ⟨hmem, hpoint⟩ := (C.environment.eventAt_eq_some _ p c).mp hc
    simpa only [hpoint] using C.crossing_fragment_interfaces hmem
  | cup a hv hc hp hi =>
    have h := C.wire_port_data hv hc hp
    have ho : (slice C.environment (List.finRange C.source.edgeCount) p).outgoing.length = 2 :=
      by omega
    dsimp only [PushPuzzle.NCL.Strip.Sweep.Site.fragment]
    rw [h.2.1, h.2.2, hi, ho]
    exact ⟨rfl, rfl⟩
  | straight a hv hc hp hi ho =>
    have h := C.wire_port_data hv hc hp
    have hi' : (slice C.environment (List.finRange C.source.edgeCount) p).incoming.length = 1 :=
      by omega
    have ho' : (slice C.environment (List.finRange C.source.edgeCount) p).outgoing.length = 1 :=
      by omega
    dsimp only [PushPuzzle.NCL.Strip.Sweep.Site.fragment]
    rw [h.2.1, h.2.2, hi', ho']
    exact ⟨rfl, rfl⟩
  | cap a hv hc hp hi ho =>
    have h := C.wire_port_data hv hc hp
    have hi' : (slice C.environment (List.finRange C.source.edgeCount) p).incoming.length = 2 :=
      by omega
    dsimp only [PushPuzzle.NCL.Strip.Sweep.Site.fragment]
    rw [h.2.1, h.2.2, hi', ho]
    exact ⟨rfl, rfl⟩

end Context
end PushPuzzle.NCL.Strip.Sweep
