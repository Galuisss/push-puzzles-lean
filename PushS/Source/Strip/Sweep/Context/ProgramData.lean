/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.RoutingMetadata
public import PushS.Source.Strip.Sweep.Context.Code
public import PushS.Source.Strip.PolyTime.ProgramData

/-!
# Actual original source selection in the encoded strip compiler

The standard-data color, source-center, and original port-slot scans retain the native source's
actual incidences. All statements concern the same existing native context and source graph.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.programData_step`: exact original local instruction and offset.
* `PushPuzzle.NCL.Strip.Sweep.Context.programData_programCode`: exact complete original instruction stream.
* `PushPuzzle.NCL.Strip.Sweep.Context.programData_compile`: the same actual original native graph.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib PolyTime

variable {A K : ℕ} (C : Context A K)

/-- The original standard-data scan computes the same actual native edge color. -/
private theorem programData_color (e : Fin C.source.edgeCount) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.color C.routingMetadata e.val = C.color e := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.color routingMetadata PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ofFinite color Planar.Embedding.color
  simp only [List.flatMap_map, Vertex.map, ← List.map_flatMap, List.any_map]
  rfl

/-- The computed standard source point is the same actual original source center. -/
private theorem programData_sourcePoint (i : Fin C.vertices.length) :
    (((PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourcePoint A C.routingMetadata i.val).1 : ℤ),
      ((PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourcePoint A C.routingMetadata i.val).2 : ℤ)) = C.environment.center i := by
  change (((8 * address A (List.ofFn C.vertexRows) i.val + 4 : ℕ) : ℤ), (4 : ℤ)) =
    PushPuzzle.NCL.Strip.Tracks.center ((PushPuzzle.NCL.Strip.Placement.ofRows C.vertexRows C.vertexCapacity).address i)
  rw [← ofRows_address C.vertexRows C.vertexCapacity i]
  simp only [PushPuzzle.NCL.Strip.Tracks.center, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- The encoded original source-center scan chooses exactly the native sweep's source vertex. -/
private theorem programData_sourceAt (t : ℕ) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourceAt A K C.routingMetadata t =
      (centerAt C.environment (List.finRange C.vertices.length) (scanPoint K (t : ℤ))).map
        Fin.val := by
  have hn : C.routingMetadata.vertexRows.length = C.vertices.length := List.length_ofFn
  have hfin : (List.finRange C.vertices.length).map Fin.val = List.range C.vertices.length := by
    apply List.ext_getElem
    · simp
    intro i hi hj
    simp
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourceAt
  rw [hn, ← hfin, List.find?_map]
  unfold centerAt
  apply congrArg (Option.map Fin.val)
  apply congrArg (fun test => (List.finRange C.vertices.length).find? test)
  funext i
  change decide (PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourcePoint A C.routingMetadata i.val = PushPuzzle.NCL.Strip.PolyTime.SliceData.scanPoint K t) =
    decide (C.environment.center i = scanPoint K (t : ℤ))
  apply decide_eq_decide.mpr
  rw [← C.programData_sourcePoint i, ← PushPuzzle.NCL.Strip.PolyTime.SliceData.integer_scanPoint K t]
  simp only [Prod.ext_iff, Int.natCast_inj]

private theorem metadata_vertex (i : Fin C.vertices.length) :
    C.routingMetadata.vertices.getD i.val ⟨[], 0⟩ = (C.graph i).map Fin.val := by
  change (C.vertices.map (Vertex.map Fin.val)).getD i.val ⟨[], 0⟩ = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem i.isLt]
  rfl

private theorem portColor_sourcePort (i : Fin C.vertices.length) (s : Fin 3) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.portColor ((C.graph i).map Fin.val) s.val = C.color (C.sourcePort i s).1.edge := by
  have hs : s.val < (C.graph i).ports.length := by rw [C.arity i]; exact s.isLt
  have he : (((C.graph i).map Fin.val).ports.getD s.val ⟨⟨0, false⟩, 0⟩).2 =
      (C.sourcePort i s).2 := by
    simp only [Vertex.map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hs, Option.map_some, Option.getD_some, sourcePort,
      List.get_eq_getElem]
    rfl
  have hw : (C.sourcePort i s).2 = (C.color (C.sourcePort i s).1.edge).weight :=
    C.port_weight (i := i) (p := C.sourcePort i s) (List.get_mem _ _)
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.portColor
  rw [he, hw]
  cases C.color (C.sourcePort i s).1.edge <;> rfl

/-- The encoded source code preserves all three original port-list slots and their colors. -/
private theorem programData_sourceOpcode (i : Fin C.vertices.length) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourceOpcode (C.routingMetadata.vertices.getD i.val ⟨[], 0⟩) =
      (PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.source i)).code := by
  have hp (s : Fin 3) :
      PushPuzzle.NCL.Strip.PolyTime.ProgramData.portColor (C.routingMetadata.vertices.getD i.val ⟨[], 0⟩) s.val =
      C.color (C.sourcePort i s).1.edge := by
    rw [metadata_vertex]
    exact portColor_sourcePort C i s
  have he : PushPuzzle.NCL.Strip.Sweep.Cell.sourceColors
      (PushPuzzle.NCL.Strip.PolyTime.ProgramData.portColor (C.routingMetadata.vertices.getD i.val ⟨[], 0⟩) 0)
      (PushPuzzle.NCL.Strip.PolyTime.ProgramData.portColor (C.routingMetadata.vertices.getD i.val ⟨[], 0⟩) 1)
      (PushPuzzle.NCL.Strip.PolyTime.ProgramData.portColor (C.routingMetadata.vertices.getD i.val ⟨[], 0⟩) 2) =
      PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.source i) := by
    rw [hp ⟨0, by decide⟩, hp ⟨1, by decide⟩, hp ⟨2, by decide⟩]
    rfl
  exact congrArg PushPuzzle.NCL.Strip.Sweep.Cell.Fragment.code he

/-- The actual original slice as the standard-data local instruction input. -/
@[expose] def programDataInput (t : ℕ) : PushPuzzle.NCL.Strip.PolyTime.ProgramData.SiteInput where
  metadata := C.routingMetadata
  slice := PushPuzzle.NCL.Strip.PolyTime.SliceData.ofSlice C.environment
    (slice C.environment (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ)))
  index := t

private abbrev localSlice (t : ℕ) : Slice C.environment :=
  slice C.environment (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))

/-- The standard-data local-input algorithm returns the same actual original context and ports.
-/
theorem programData_siteInput (t : ℕ) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K C.routingMetadata t = C.programDataInput t := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput programDataInput
  rw [C.unitRoutes_routingMetadata, PushPuzzle.NCL.Strip.PolyTime.SliceData.ofRoutes_ofFn]

/-- The standard-data scan runs over the exact same complete original scan interval. -/
theorem programData_scanLength :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.scanLength A K C.routingMetadata =
      scanLength C.environment (List.finRange C.source.edgeCount) := by
  change (8 * A * ((List.ofFn C.ownerRows).foldr max 0 + 2) + 1) * (height K + 1) =
    (8 * A * (((List.finRange C.source.edgeCount).map C.ownerRows).foldr max 0 + 2) + 1) *
      (height K + 1)
  rw [List.ofFn_eq_map]

private theorem inputColors_of_edges (t : ℕ) (e f : Fin C.source.edgeCount)
    (hi : (C.localSlice t).incoming.map PushPuzzle.NCL.Strip.Sweep.Arc.edge = [e, f]) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.inputColor (C.programDataInput t) 0 = C.color e ∧
      PushPuzzle.NCL.Strip.PolyTime.ProgramData.inputColor (C.programDataInput t) 1 = C.color f := by
  have he : ((C.programDataInput t).slice.incoming.map PushPuzzle.NCL.Strip.PolyTime.ArcData.edge) = [e.val, f.val] := by
    change (((C.localSlice t).incoming.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)).map PushPuzzle.NCL.Strip.PolyTime.ArcData.edge) = _
    rw [List.map_map]
    change ((C.localSlice t).incoming.map (fun a => a.edge.val)) = _
    simpa only [List.map_map, List.map_cons, List.map_nil, Function.comp_def] using
      congrArg (List.map Fin.val) hi
  constructor
  · unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.inputColor
    rw [he]
    exact C.programData_color e
  · unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.inputColor
    rw [he]
    exact C.programData_color f

private theorem localStep_crossing (t : ℕ) (e f : Fin C.source.edgeCount)
    (hi : (C.localSlice t).incoming.map PushPuzzle.NCL.Strip.Sweep.Arc.edge = [e, f])
    (ho : (C.localSlice t).outgoing.map PushPuzzle.NCL.Strip.Sweep.Arc.edge = [f, e]) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep (C.programDataInput t) =
      [((C.localSlice t).above.length, PushPuzzle.NCL.Strip.PolyTime.ProgramData.crossOpcode (C.color e) (C.color f))] := by
  have hni : (C.programDataInput t).slice.incoming.length = 2 := by
    change ((C.localSlice t).incoming.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)).length = 2
    have h := congrArg List.length hi
    simpa only [List.length_map, List.length_cons, List.length_nil, Nat.reduceAdd] using h
  have hno : (C.programDataInput t).slice.outgoing.length = 2 := by
    change ((C.localSlice t).outgoing.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)).length = 2
    have h := congrArg List.length ho
    simpa only [List.length_map, List.length_cons, List.length_nil, Nat.reduceAdd] using h
  have hc := inputColors_of_edges C t e f hi
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep
  rw [ite_eq_left ⟨hni, hno⟩, hc.1, hc.2]
  simp only [programDataInput, PushPuzzle.NCL.Strip.PolyTime.SliceData.ofSlice, List.length_map]
  rfl

private theorem not_cross_of_sum_le (t : ℕ)
    (hl : (C.localSlice t).incoming.length + (C.localSlice t).outgoing.length ≤ 2) :
    ¬((C.programDataInput t).slice.incoming.length = 2 ∧
      (C.programDataInput t).slice.outgoing.length = 2) := by
  change ¬(((C.localSlice t).incoming.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)).length = 2 ∧
    ((C.localSlice t).outgoing.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)).length = 2)
  simp only [List.length_map]
  omega

private theorem localStep_wire (t : ℕ) (a : Arc C.environment)
    (hp : ((C.localSlice t).incoming ++ (C.localSlice t).outgoing).head? = some a)
    (hl : (C.localSlice t).incoming.length + (C.localSlice t).outgoing.length = 2) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep (C.programDataInput t) =
      [((C.localSlice t).above.length,
        PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode (C.localSlice t).incoming.length (C.localSlice t).outgoing.length
          (C.color a.edge))] := by
  have hn := not_cross_of_sum_le C t hl.le
  have hhead : ((C.programDataInput t).slice.incoming ++
      (C.programDataInput t).slice.outgoing).head? = some (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment a) := by
    change (((C.localSlice t).incoming.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)) ++
      ((C.localSlice t).outgoing.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment))).head? = _
    rw [← List.map_append, List.head?_map, hp, Option.map_some]
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep
  rw [ite_eq_right hn, hhead, Option.elim_some]
  have hc : PushPuzzle.NCL.Strip.PolyTime.ProgramData.color (C.programDataInput t).metadata (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment a).edge =
      C.color a.edge := C.programData_color a.edge
  rw [hc]
  simp only [programDataInput, PushPuzzle.NCL.Strip.PolyTime.SliceData.ofSlice, List.length_map]
  rfl

private theorem localStep_empty (t : ℕ)
    (hp : ((C.localSlice t).incoming ++ (C.localSlice t).outgoing).head? = none) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep (C.programDataInput t) = [] := by
  have he : (C.localSlice t).incoming ++ (C.localSlice t).outgoing = [] :=
    List.head?_eq_none_iff.mp hp
  have hl := congrArg List.length he
  simp only [List.length_append, List.length_nil] at hl
  have hn := not_cross_of_sum_le C t (by omega)
  have hhead : ((C.programDataInput t).slice.incoming ++
      (C.programDataInput t).slice.outgoing).head? = none := by
    change (((C.localSlice t).incoming.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment)) ++
      ((C.localSlice t).outgoing.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc C.environment))).head? = _
    rw [← List.map_append, List.head?_map, hp, Option.map_none]
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep
  rw [ite_eq_right hn, hhead, Option.elim_none]

private theorem step_no_source (t : ℕ)
    (hv : centerAt C.environment (List.finRange C.vertices.length) (scanPoint K (t : ℤ)) = none) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.step A K (C.programDataInput t) = PushPuzzle.NCL.Strip.PolyTime.ProgramData.localStep (C.programDataInput t) := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.step
  change (PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourceAt A K C.routingMetadata t).elim _ _ = _
  rw [C.programData_sourceAt, hv, Option.map_none, Option.elim_none]

private theorem step_source (t : ℕ) (i : Fin C.vertices.length)
    (hv : centerAt C.environment (List.finRange C.vertices.length) (scanPoint K (t : ℤ)) =
      some i) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.step A K (C.programDataInput t) =
      [((C.localSlice t).above.length,
        (PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.source i)).code)] := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.step
  change (PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourceAt A K C.routingMetadata t).elim _ _ = _
  rw [C.programData_sourceAt, hv, Option.map_some, Option.elim_some]
  simp only [programDataInput, PushPuzzle.NCL.Strip.PolyTime.SliceData.ofSlice, List.length_map]
  exact congrArg (fun op : Fin 14 => [((C.localSlice t).above.length, op)])
    (C.programData_sourceOpcode i)

private theorem instructionCode_some (t : ℕ) (site : Site (Fin C.vertices.length)
    (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ)) = some site) :
    (instruction C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))).toList.map
        (fun ins => (ins.offset, ins.fragment.code)) =
          [((C.localSlice t).above.length, (site.fragment C.graph C.arity C.color).code)] := by
  simp only [instruction, hc, Option.map_some, Option.toList_some, List.map_cons, List.map_nil]

private theorem instructionCode_none (t : ℕ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ)) = none) :
    (instruction C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))).toList.map
        (fun ins => (ins.offset, ins.fragment.code)) = [] := by
  simp only [instruction, hc, Option.map_none, Option.toList_none, List.map_nil]

/-- Standard-data local emission selects the same actual original finite instruction and offset.
-/
theorem programData_step (t : ℕ) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.step A K (C.programDataInput t) =
      (instruction C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))).toList.map
          (fun ins => (ins.offset, ins.fragment.code)) := by
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))
  generalize hclass : classify C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ)) = selected at hs
  cases hs with
  | empty hv hEvent hp =>
    exact (step_no_source C t hv).trans ((localStep_empty C t hp).trans
      (instructionCode_none C t hclass).symm)
  | source i hv =>
    exact (step_source C t i hv).trans (instructionCode_some C t (.source i) hclass).symm
  | crossing c hv hEvent =>
    obtain ⟨hc, hp⟩ := (C.environment.eventAt_eq_some _ _ c).mp hEvent
    have hports := crossing_slice C.environment (List.nodup_finRange _) hc
    rw [hp] at hports
    exact ((step_no_source C t hv).trans
      (localStep_crossing C t c.bridge c.stem hports.1 hports.2)).trans
        (instructionCode_some C t (.crossing c) hclass).symm
  | cup a hv hEvent hp hi =>
    have hl := (C.wire_port_data hv hEvent hp).1
    have hrun := (step_no_source C t hv).trans (localStep_wire C t a hp hl)
    have hcode : PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode (C.localSlice t).incoming.length
        (C.localSlice t).outgoing.length (C.color a.edge) =
        (PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.cup a.edge)).code := by
      simp only [PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode, hi, ite_true]
      rfl
    exact hrun.trans ((congrArg (fun op : Fin 14 => [((C.localSlice t).above.length, op)])
      hcode).trans (instructionCode_some C t (.cup a.edge) hclass).symm)
  | straight a hv hEvent hp hi ho =>
    have hl := (C.wire_port_data hv hEvent hp).1
    have hrun := (step_no_source C t hv).trans (localStep_wire C t a hp hl)
    have hcode : PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode (C.localSlice t).incoming.length
        (C.localSlice t).outgoing.length (C.color a.edge) =
        (PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.straight a.edge)).code := by
      simp only [PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode, hi, ho, ite_false]
      rfl
    exact hrun.trans ((congrArg (fun op : Fin 14 => [((C.localSlice t).above.length, op)])
      hcode).trans (instructionCode_some C t (.straight a.edge) hclass).symm)
  | cap a hv hEvent hp hi ho =>
    have hl := (C.wire_port_data hv hEvent hp).1
    have hrun := (step_no_source C t hv).trans (localStep_wire C t a hp hl)
    have hcode : PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode (C.localSlice t).incoming.length
        (C.localSlice t).outgoing.length (C.color a.edge) =
        (PushPuzzle.NCL.Strip.Sweep.Site.fragment C.graph C.arity C.color (.cap a.edge)).code := by
      simp only [PushPuzzle.NCL.Strip.PolyTime.ProgramData.wireOpcode, hi, ho, ite_false, ite_true]
      rfl
    exact hrun.trans ((congrArg (fun op : Fin 14 => [((C.localSlice t).above.length, op)])
      hcode).trans (instructionCode_some C t (.cap a.edge) hclass).symm)

/-- The complete standard-data instruction compiler returns the same actual native program code.
-/
theorem programData_programCode :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.programCode A K C.routingMetadata = C.programCode := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.programCode programCode PushPuzzle.NCL.Strip.Sweep.programCode
  rw [C.programData_scanLength]
  apply List.flatMap_congr
  intro t _
  rw [C.programData_siteInput]
  exact C.programData_step t

/-- The standard polynomial-time compiler returns the same actual native strip graph. -/
theorem programData_compile : PushPuzzle.NCL.Strip.PolyTime.ProgramData.compile A K C.routingMetadata = C.program.compile := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ProgramData.compile
  rw [C.programData_programCode, C.compile_programCode]

end PushPuzzle.NCL.Strip.Sweep.Context
