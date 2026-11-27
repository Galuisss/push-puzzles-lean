/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context
public import PushS.Source.Strip.Sweep.JointPorts
public import PushS.Source.Strip.Sweep.UnitAt
public import PushS.Source.Strip.Sweep.Cell.Labels

/-!
# Original source constraints in the actual local sweep

Original source cells preserve all three ordered weighted incidences. The actual local labels
therefore give precisely the corresponding vertex of the actual unit-subdivision graph.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.unitGraph_source_eq`: the source's actual weighted local port record.
* `PushPuzzle.NCL.Strip.Sweep.Context.source_generator_legal`: exact legality of an actual source generator.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram ConstraintGraph

variable {A K : ℕ} (C : Context A K)

/-- The actual source unit vertex is its incoming-then-outgoing local weighted port record. -/
theorem unitGraph_source_eq (v : Fin C.vertices.length) :
    unitGraph C.environment C.graph (fun e => (C.color e).weight) (.inl v) =
      ⟨localPorts C.environment (List.finRange C.source.edgeCount) (C.environment.center v)
        (fun e => (C.color e).weight), 2⟩ := by
  have h := PushPuzzle.NCL.Strip.Sweep.source_cell C.vertices C.wellFormed C.loopFree C.isAndOr C.vertexRows C.ownerRows
    C.vertexCapacity C.ownerCapacity C.endpointRows v
  have hi :
      (slice C.environment (List.finRange C.source.edgeCount) (C.environment.center v)).incoming =
        [portArc C.environment (C.sourcePort v 0).1.edge (C.sourcePort v 0).1.dir] := h.1
  have ho :
      (slice C.environment (List.finRange C.source.edgeCount) (C.environment.center v)).outgoing =
        [portArc C.environment (C.sourcePort v 1).1.edge (C.sourcePort v 1).1.dir,
          portArc C.environment (C.sourcePort v 2).1.edge (C.sourcePort v 2).1.dir] := h.2.1
  have hn : (C.graph v).minInflow = 2 := h.2.2.1
  rw [unitGraph_source, C.source_port_list, localPorts, hi, ho]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  have hd (s : Fin 3) :
      ((portArc C.environment (C.sourcePort v s).1.edge (C.sourcePort v s).1.dir).reversed
        C.environment ^^ (C.sourcePort v s).1.dir) = decide (s = 0) := h.2.2.2.2 s
  have hw (s : Fin 3) : (C.sourcePort v s).2 = (C.color (C.sourcePort v s).1.edge).weight :=
    C.port_weight (List.get_mem _ _)
  simp only [hd, hn, hw, (portArc_spec C.environment _ _).1]
  rfl

/-- The single actual source generator has exactly the original unit vertex's constraint. -/
theorem source_generator_legal (v : Fin C.vertices.length)
    (s : Arc C.environment → Bool) :
    let p := C.environment.center v
    let g := (PushPuzzle.NCL.Strip.Sweep.Site.source v).fragment C.graph C.arity C.color
    let x := (slice C.environment (List.finRange C.source.edgeCount) p).incoming
    let y := (slice C.environment (List.finRange C.source.edgeCount) p).outgoing
    let h := C.source_fragment_interfaces v
    ((Diagram.gen g.generator).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
        (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling g.generator x y
          (by rw [h.1, List.length_map]) (by rw [h.2, List.length_map])).label) ↔
      (unitGraph C.environment C.graph (fun e => (C.color e).weight) (.inl v)).Sat s := by
  dsimp only
  let g := (PushPuzzle.NCL.Strip.Sweep.Site.source v).fragment C.graph C.arity C.color
  let x := (slice C.environment (List.finRange C.source.edgeCount)
    (C.environment.center v)).incoming
  let y := (slice C.environment (List.finRange C.source.edgeCount)
    (C.environment.center v)).outgoing
  have h := C.source_fragment_interfaces v
  have hr : PushPuzzle.NCL.Strip.Sweep.Cell.raw g.generator = [genVertex g.inputs g.outputs 2] :=
    PushPuzzle.NCL.Strip.Sweep.Cell.sourceColors_raw _ _ _
  exact (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling_legal g.generator (fun a : Arc C.environment => C.color a.edge)
    x y (by rw [h.1, List.length_map]) (by rw [h.2, List.length_map]) h.1 h.2 2 hr s).trans
      (Iff.of_eq (congrArg (fun w => w.Sat s) (C.unitGraph_source_eq v).symm))

private theorem wire_generator_legal {p : Cslib.Orthogonal.Point} {a : Arc C.environment}
    (hv : centerAt C.environment (List.finRange C.vertices.length) p = none)
    (hc : C.environment.eventAt (List.finRange C.source.edgeCount) p = none)
    (hp : ((slice C.environment (List.finRange C.source.edgeCount) p).incoming ++
      (slice C.environment (List.finRange C.source.edgeCount) p).outgoing).head? = some a)
    {x y : List Color} (g : Cell x y)
    (hi : x = (slice C.environment (List.finRange C.source.edgeCount) p).incoming.map
      (fun a => C.color a.edge))
    (ho : y = (slice C.environment (List.finRange C.source.edgeCount) p).outgoing.map
      (fun a => C.color a.edge))
    (hr : PushPuzzle.NCL.Strip.Sweep.Cell.raw g = [genVertex x y (C.color a.edge).weight])
    (s : Arc C.environment → Bool) :
    ((Diagram.gen g).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
        (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling g
          (slice C.environment (List.finRange C.source.edgeCount) p).incoming
          (slice C.environment (List.finRange C.source.edgeCount) p).outgoing
          (by rw [hi, List.length_map]) (by rw [ho, List.length_map])).label) ↔
      UnitLegalAt C.environment C.graph (fun e => (C.color e).weight) p s := by
  obtain ⟨ha, hcent, hcross⟩ := C.wire_geometry hv hc hp
  have hunit := unitLegalAt_wire C.environment C.graph (fun e => (C.color e).weight)
    (List.nodup_finRange _) (fun e => List.mem_finRange e) ha hcent hcross s
  rw [wire_localPorts_filter C.environment _ (List.mem_finRange _) ha hcent hcross] at hunit
  exact (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling_legal g (fun a : Arc C.environment => C.color a.edge) _ _
    (by rw [hi, List.length_map]) (by rw [ho, List.length_map]) hi ho _ hr s).trans hunit.symm

private theorem map_pair {α β : Type*} (f : α → β) {l : List α} {u v : β}
    (h : l.map f = [u, v]) : ∃ a b, l = [a, b] ∧ f a = u ∧ f b = v := by
  obtain ⟨a, l', hl, ha, hm⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨b, hb, hbe⟩ := List.map_eq_singleton_iff.mp hm
  exact ⟨a, b, by simpa only [hb] using hl, ha, hbe⟩

/-- The actual crossing generator checks exactly its two actual original carrier joints. -/
private theorem crossing_generator_legal {c : Event (Fin C.source.edgeCount)}
    (hc : c ∈ C.environment.events (List.finRange C.source.edgeCount))
    (s : Arc C.environment → Bool) :
    let p := c.site C.environment
    let g := (PushPuzzle.NCL.Strip.Sweep.Site.crossing c).fragment C.graph C.arity C.color
    let x := (slice C.environment (List.finRange C.source.edgeCount) p).incoming
    let y := (slice C.environment (List.finRange C.source.edgeCount) p).outgoing
    let h := C.crossing_fragment_interfaces hc
    ((Diagram.gen g.generator).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
        (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling g.generator x y
          (by rw [h.1, List.length_map]) (by rw [h.2, List.length_map])).label) ↔
      UnitLegalAt C.environment C.graph (fun e => (C.color e).weight) p s := by
  dsimp only
  have hc' := ((C.environment.mem_events _ c).mp hc).2.2
  have hne := hc'.ne
  have hs := crossing_slice C.environment (List.nodup_finRange _) hc
  obtain ⟨a, b, hi, hae, hbe⟩ := map_pair PushPuzzle.NCL.Strip.Sweep.Arc.edge hs.1
  obtain ⟨t, r, ho, hte, hre⟩ := map_pair PushPuzzle.NCL.Strip.Sweep.Arc.edge hs.2
  have hb :
      (localPorts C.environment (List.finRange C.source.edgeCount) (c.site C.environment)
        (fun e => (C.color e).weight)).filter (fun q => decide (q.1.edge.edge = c.bridge)) =
        [⟨⟨a, true⟩, (C.color c.bridge).weight⟩, ⟨⟨r, false⟩, (C.color c.bridge).weight⟩] := by
    simp [localPorts, hi, ho, hae, hbe, hte, hre, Ne.symm hne]
  have ht :
      (localPorts C.environment (List.finRange C.source.edgeCount) (c.site C.environment)
        (fun e => (C.color e).weight)).filter (fun q => decide (q.1.edge.edge = c.stem)) =
        [⟨⟨b, true⟩, (C.color c.stem).weight⟩, ⟨⟨t, false⟩, (C.color c.stem).weight⟩] := by
    simp [localPorts, hi, ho, hae, hbe, hte, hre, hne]
  have hu := unitLegalAt_crossing C.environment C.graph (fun e => (C.color e).weight)
    (List.nodup_finRange _) (fun e => List.mem_finRange e) hc s
  rw [hb, ht] at hu
  simp only [PushPuzzle.NCL.Strip.Sweep.Site.fragment]
  have hl := PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling_congr (.cross (C.color c.bridge) (C.color c.stem)) _ _ [a, b] [t, r]
    (by simpa only [List.length_cons, List.length_nil] using congrArg List.length hi)
    (by simpa only [List.length_cons, List.length_nil] using congrArg List.length ho)
    rfl rfl hi ho
  exact (Iff.of_eq (congrArg (fun f =>
    ((Diagram.gen (PushPuzzle.NCL.Strip.Sweep.Cell.cross (C.color c.bridge) (C.color c.stem))).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
      (s ∘ f)) hl)).trans
    ((PushPuzzle.NCL.Strip.Sweep.Cell.crossLabeling_legal (C.color c.bridge) (C.color c.stem) a b t r s).trans hu.symm)

/-- Every selected actual source, crossing, or wire generator checks the actual unit graph there.
-/
theorem selection_generator_legal {p : Cslib.Orthogonal.Point}
    {site : Site (Fin C.vertices.length) (Fin C.source.edgeCount)}
    (hs : Selection C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p (some site)) (s : Arc C.environment → Bool) :
    let g := site.fragment C.graph C.arity C.color
    let x := (slice C.environment (List.finRange C.source.edgeCount) p).incoming
    let y := (slice C.environment (List.finRange C.source.edgeCount) p).outgoing
    let h := C.selection_interfaces hs
    ((Diagram.gen g.generator).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
        (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling g.generator x y
          (by rw [h.1, List.length_map]) (by rw [h.2, List.length_map])).label) ↔
      UnitLegalAt C.environment C.graph (fun e => (C.color e).weight) p s := by
  cases hs with
  | source v hv =>
    have hp := ((centerAt_eq_some C.environment _ p v).mp hv).2
    subst p
    exact (C.source_generator_legal v s).trans
      (unitLegalAt_center C.environment C.graph _ v s).symm
  | crossing c hv hc =>
    obtain ⟨hm, hp⟩ := (C.environment.eventAt_eq_some _ p c).mp hc
    subst p
    exact C.crossing_generator_legal hm s
  | cup a hv hc hp hi =>
    have h := C.selection_interfaces (PushPuzzle.NCL.Strip.Sweep.Selection.cup a hv hc hp hi)
    exact C.wire_generator_legal hv hc hp (.cup (C.color a.edge)) h.1 h.2 rfl s
  | straight a hv hc hp hi ho =>
    have h := C.selection_interfaces (PushPuzzle.NCL.Strip.Sweep.Selection.straight a hv hc hp hi ho)
    exact C.wire_generator_legal hv hc hp (.straight (C.color a.edge)) h.1 h.2 rfl s
  | cap a hv hc hp hi ho =>
    have h := C.selection_interfaces (PushPuzzle.NCL.Strip.Sweep.Selection.cap a hv hc hp hi ho)
    exact C.wire_generator_legal hv hc hp (.cap (C.color a.edge)) h.1 h.2 rfl s

end PushPuzzle.NCL.Strip.Sweep.Context
