/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.SliceData
public import PushS.Source.Strip.Sweep.ProgramCode
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Emit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.Fold

/-!
# Standard encoded actual strip instruction emission

Read original source ports, decoded source centers, and the actual local slice records. Local
arities identify a crossing or one of the three wire cells. The emitted instructions use the
existing fourteen-cell table and the actual unchanged frontier-prefix length.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.ProgramData.sourceAt`: actual source-center index scan.
* `PushPuzzle.NCL.Strip.PolyTime.ProgramData.scanLength`: complete source-owner scan interval.
* `PushPuzzle.NCL.Strip.PolyTime.ProgramData.SiteInput`: source data and computed local slice at one scan index.
* `PushPuzzle.NCL.Strip.PolyTime.ProgramData.step`: selected finite table instruction at that site.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.ProgramData.computableInPolyTime_programCode`: complete standard instruction PT.
* `PushPuzzle.NCL.Strip.PolyTime.ProgramData.computableInPolyTime_compile`: complete standard native graph PT.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime.ProgramData

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

private instance : Fintype Cslib.Complexity.NCL.Color :=
  ⟨{.red, .blue}, by intro c; cases c <;> simp⟩


/-- Read the actual original edge color by scanning weight-two port occurrences. -/
@[expose] def color (data : RoutingMetadata) (e : ℕ) : Color :=
  if (data.vertices.flatMap Vertex.ports).any (fun p => p.1.edge == e && p.2 == 2)
    then .blue else .red

/-- Read the actual color of an original source port-list slot. -/
@[expose] def portColor (v : Vertex ℕ) (slot : ℕ) : Color :=
  if (v.ports.getD slot ⟨⟨0, false⟩, 0⟩).2 == 2 then .blue else .red

/-- Select the original three-port source cell from its actual slot colors. -/
@[expose] def sourceOpcode (v : Vertex ℕ) : Fin 14 :=
  (PushPuzzle.NCL.Strip.Sweep.Cell.sourceColors (portColor v 0) (portColor v 1) (portColor v 2)).code

/-- Actual center of a source vertex in the original panel/slot allocation. -/
@[expose] def sourcePoint (A : ℕ) (data : RoutingMetadata) (i : ℕ) : ℕ × ℕ :=
  (8 * address A data.vertexRows i + 4, 4)

/-- Scan the actual original source centers at one decoded grid site. -/
@[expose] def sourceAt (A K : ℕ) (data : RoutingMetadata) (t : ℕ) : Option ℕ :=
  (List.range data.vertexRows.length).find?
    (fun i => decide (sourcePoint A data i = PushPuzzle.NCL.Strip.PolyTime.SliceData.scanPoint K t))

/-- Select the same finite crossing-table entry for its two actual incoming colors. -/
@[expose] def crossOpcode (c d : Color) : Fin 14 :=
  (⟨_, _, .cross c d⟩ : PushPuzzle.NCL.Strip.Sweep.Cell.Fragment).code

/-- Select the actual cup, straight, or cap implementation from its local arity and color. -/
@[expose] def wireOpcode (inputs outputs : ℕ) (c : Color) : Fin 14 :=
  if inputs = 0 then (⟨_, _, .cup c⟩ : PushPuzzle.NCL.Strip.Sweep.Cell.Fragment).code
  else if outputs = 0 then (⟨_, _, .cap c⟩ : PushPuzzle.NCL.Strip.Sweep.Cell.Fragment).code
  else (⟨_, _, .straight c⟩ : PushPuzzle.NCL.Strip.Sweep.Cell.Fragment).code

/-- Complete actual scan interval computed from the original owner-row array. -/
@[expose] def scanLength (A K : ℕ) (data : RoutingMetadata) : ℕ :=
  (8 * A * (data.ownerRows.foldr max 0 + 2) + 1) * (PushPuzzle.NCL.Strip.Sweep.height K + 1)

/-- Original source data and its actual computed local slice at one scan index. -/
structure SiteInput where
  /-- The original standard source data and actual row arrays. -/
  metadata : RoutingMetadata
  /-- The same actual unchanged context and local unit-arc port blocks. -/
  slice : SliceData
  /-- Original nonnegative column-major scan index. -/
  index : ℕ

/-- Standard source metadata, local slice records, and unary scan index. -/
enc_structure encSiteInput : SiteInput where
  metadata : encRoutingMetadata, slice : encSliceData, index : encUnary

/-- Read one actual incoming original carrier color, using its existing position in the slice. -/
@[expose] def inputColor (s : SiteInput) (index : ℕ) : Color :=
  color s.metadata ((s.slice.incoming.map PushPuzzle.NCL.Strip.PolyTime.ArcData.edge).getD index 0)

/-- Emit the actual non-source local cell using its original unit-port arity and colors. -/
@[expose] def localStep (s : SiteInput) : PushPuzzle.NCL.Strip.Sweep.Cell.language.Program :=
  if s.slice.incoming.length = 2 ∧ s.slice.outgoing.length = 2 then
    [(s.slice.above.length, crossOpcode (inputColor s 0) (inputColor s 1))]
  else ((s.slice.incoming ++ s.slice.outgoing).head?).elim [] fun a =>
    [(s.slice.above.length, wireOpcode s.slice.incoming.length s.slice.outgoing.length
      (color s.metadata a.edge))]

/-- Emit the selected source, crossing, or ordinary wire code at the actual local prefix offset.
-/
@[expose] def step (A K : ℕ) (s : SiteInput) : PushPuzzle.NCL.Strip.Sweep.Cell.language.Program :=
  (sourceAt A K s.metadata s.index).elim (localStep s) fun i =>
    [(s.slice.above.length, sourceOpcode (s.metadata.vertices.getD i ⟨[], 0⟩))]

@[local fun_prop]
private theorem computableInPolyTime_color :
    ComputableInPolyTime (fun p : RoutingMetadata × ℕ => color p.1 p.2)
      (encPair encRoutingMetadata encUnary) encColor := by
  have he : ComputableInPolyTime (fun p : RoutingMetadata × ℕ => p.2)
      (encPair encRoutingMetadata encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd encRoutingMetadata encUnary)
  have hg : ComputableInPolyTime (fun p : RoutingMetadata × ℕ =>
      (⟨p.1.vertices, p.1.ownerRows.length⟩ : AndOrGraph))
      (encPair encRoutingMetadata encUnary) encAndOrGraph := by
    fun_prop
  exact Planar.Embedding.PolyTime.Emit.computableInPolyTime_edgeColor hg he

@[local fun_prop]
private theorem computableInPolyTime_portColor :
    ComputableInPolyTime (fun p : Vertex ℕ × ℕ => portColor p.1 p.2)
      (encPair (encVertex encNat) encUnary) encColor := by
  have hw : ComputableInPolyTime
      (fun p : Vertex ℕ × ℕ => (p.1.ports.getD p.2 ⟨⟨0, false⟩, 0⟩).2)
      (encPair (encVertex encNat) encUnary) encNat := by fun_prop
  have hb := hw.beq (ComputableInPolyTime.const 2)
  unfold portColor
  exact hb.ite' (ComputableInPolyTime.const (encOut := encColor) Color.blue)
    (ComputableInPolyTime.const (encOut := encColor) Color.red)

@[local fun_prop]
private theorem computableInPolyTime_sourceOpcode :
    ComputableInPolyTime sourceOpcode (encVertex encNat) PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode := by
  have hf := ComputableInPolyTime.of_finite
    (encIn := encPair encColor (encPair encColor encColor))
    (encOut := PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode)
    (fun p : Color × (Color × Color) => (PushPuzzle.NCL.Strip.Sweep.Cell.sourceColors p.1 p.2.1 p.2.2).code)
  have hp : ComputableInPolyTime (fun v : Vertex ℕ =>
      (portColor v 0, (portColor v 1, portColor v 2)))
      (encVertex encNat) (encPair encColor (encPair encColor encColor)) := by fun_prop
  exact (hf.comp hp).of_enc_eq (fun _ => rfl)

@[local fun_prop]
private theorem computableInPolyTime_sourcePoint (A : ℕ) :
    ComputableInPolyTime (fun p : RoutingMetadata × ℕ => sourcePoint A p.1 p.2)
      (encPair encRoutingMetadata encUnary) encNatPoint := by
  have ha : ComputableInPolyTime (fun p : RoutingMetadata × ℕ => address A p.1.vertexRows p.2)
      (encPair encRoutingMetadata encUnary) encUnary := by
    simpa only [Function.comp_def] using (computableInPolyTime_address A).comp
      ((encRoutingMetadata_vertexRows_polyTime (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  unfold sourcePoint
  fun_prop

/-- The original source-center lookup is polynomial-time under the standard explicit encoding.
-/
private theorem computableInPolyTime_sourceAt (A K : ℕ) :
    ComputableInPolyTime (fun p : RoutingMetadata × ℕ => sourceAt A K p.1 p.2)
      (encPair encRoutingMetadata encUnary) (encOption encUnary) := by
  unfold sourceAt
  apply ComputableInPolyTime.findWithInput
  · fun_prop
  · fun_prop

@[local fun_prop]
private theorem computableInPolyTime_crossOpcode :
    ComputableInPolyTime (fun p : Color × Color => crossOpcode p.1 p.2)
      (encPair encColor encColor) PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode := ComputableInPolyTime.of_finite _

@[local fun_prop]
private theorem computableInPolyTime_wireOpcode :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × Color => wireOpcode p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encColor) PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode := by
  have hc := ComputableInPolyTime.snd (encPair encUnary encUnary) encColor
  apply hc.finite_cases (branch := fun c p => wireOpcode p.1.1 p.1.2 c)
  intro c
  unfold wireOpcode
  fun_prop

private theorem computableInPolyTime_maxRow :
    ComputableInPolyTime (fun rows : List ℕ => rows.foldr max 0) (encList encUnary) encUnary := by
  have h : ComputableInPolyTime (fun rows : List ℕ => rows.foldl max 0)
      (encList encUnary) encUnary := by
    apply ComputableInPolyTime.foldlWith_of_bounded_growth
      (encP := encBool) (encA := encUnary) (encB := encUnary) (encL := encList encUnary)
      (par := fun _ => false) (step := fun (_ : Bool) state value => max state value)
      (ComputableInPolyTime.const false) ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
      (by fun_prop) (growth := fun rows => (encList encUnary rows).length) .self
    intro rows state value hv
    have hm : (encUnary value).length ∈ rows.map (fun n => (encUnary n).length) :=
      List.mem_map.mpr ⟨value, hv, rfl⟩
    have he := (List.le_sum_of_mem hm).trans (sum_length_le_length_encList encUnary rows)
    simp only [encUnary_apply, List.length_replicate] at he ⊢
    omega
  simpa only [List.foldl_eq_foldr] using h

/-- The complete actual owner-row scan interval is standard encoded polynomial-time. -/
theorem computableInPolyTime_scanLength (A K : ℕ) :
    ComputableInPolyTime (scanLength A K) encRoutingMetadata encUnary := by
  have hm := computableInPolyTime_maxRow.comp
    (encRoutingMetadata_ownerRows_polyTime ComputableInPolyTime.id')
  unfold scanLength
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_inputColor :
    ComputableInPolyTime (fun p : SiteInput × ℕ => inputColor p.1 p.2)
      (encPair encSiteInput encUnary) encColor := by
  unfold inputColor
  fun_prop

private theorem computableInPolyTime_localStep :
    ComputableInPolyTime localStep encSiteInput PushPuzzle.NCL.Strip.Sweep.Cell.language.encProgram := by
  unfold localStep Word.Fixed.Language.encProgram
  apply ComputableInPolyTime.ite_decide
  · fun_prop
  · fun_prop
  · apply ComputableInPolyTime.optionElimWithInput (encB := encArcData)
    · fun_prop
    · exact ComputableInPolyTime.const []
    · have hi : ComputableInPolyTime (fun p : SiteInput × ArcData =>
          (p.1.slice.above.length, wireOpcode p.1.slice.incoming.length p.1.slice.outgoing.length
            (color p.1.metadata p.2.edge))) (encPair encSiteInput encArcData)
          (encPair encUnary PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode) := by
        have hpar : ComputableInPolyTime (fun p : SiteInput × ArcData =>
            ((p.1.slice.incoming.length, p.1.slice.outgoing.length), color p.1.metadata p.2.edge))
            (encPair encSiteInput encArcData) (encPair (encPair encUnary encUnary) encColor) := by
          fun_prop
        have hw := computableInPolyTime_wireOpcode.comp hpar
        have hk : ComputableInPolyTime (fun p : SiteInput × ArcData => p.1.slice.above.length)
            (encPair encSiteInput encArcData) encUnary := by fun_prop
        exact (hk.prod hw).of_enc_eq (fun _ => rfl)
      exact ((ComputableInPolyTime.cons (encPair encUnary PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode)).comp
        (hi.prod (ComputableInPolyTime.const []))).of_enc_eq (fun _ => rfl)

/-- Read the actual finite local cell code and prefix offset in standard polynomial time. -/
theorem computableInPolyTime_step (A K : ℕ) :
    ComputableInPolyTime (step A K) encSiteInput PushPuzzle.NCL.Strip.Sweep.Cell.language.encProgram := by
  unfold step
  apply ComputableInPolyTime.optionElimWithInput
  · simpa only [Function.comp_def] using (computableInPolyTime_sourceAt A K).comp
      ((encSiteInput_metadata_polyTime ComputableInPolyTime.id').prod
        (encSiteInput_index_polyTime ComputableInPolyTime.id'))
  · exact computableInPolyTime_localStep
  · unfold Word.Fixed.Language.encProgram
    fun_prop

/-- Compute the same actual local input records directly from the complete carrier arrays. -/
@[expose] def siteInput (A K : ℕ) (data : RoutingMetadata) (t : ℕ) : SiteInput where
  metadata := data
  slice := PushPuzzle.NCL.Strip.PolyTime.SliceData.ofRoutes K (data.unitRoutes A K) t
  index := t

/-- All actual local input records emit in standard polynomial time. -/
theorem computableInPolyTime_siteInput (A K : ℕ) :
    ComputableInPolyTime (fun p : RoutingMetadata × ℕ => siteInput A K p.1 p.2)
      (encPair encRoutingMetadata encUnary) encSiteInput := by
  have hr : ComputableInPolyTime (fun p : RoutingMetadata × ℕ => (p.1.unitRoutes A K, p.2))
      (encPair encRoutingMetadata encUnary) (encPair (encList encRoute) encUnary) := by
    have hu := (PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.computableInPolyTime_unitRoutes A K).comp
      (ComputableInPolyTime.fst encRoutingMetadata encUnary)
    fun_prop
  have hs := (PushPuzzle.NCL.Strip.PolyTime.SliceData.computableInPolyTime_ofRoutes K).comp hr
  unfold siteInput
  apply encSiteInput_mk_polyTime
  · exact ComputableInPolyTime.fst _ _
  · exact hs.of_enc_eq (fun _ => rfl)
  · exact ComputableInPolyTime.snd _ _

/-- Emit the selected actual finite instructions over the complete original scan interval. -/
@[expose] def programCode (A K : ℕ) (data : RoutingMetadata) : PushPuzzle.NCL.Strip.Sweep.Cell.language.Program :=
  (List.range (scanLength A K data)).flatMap fun t => step A K (siteInput A K data t)

/-- The complete finite instruction emitter is standard encoded polynomial-time. -/
theorem computableInPolyTime_programCode (A K : ℕ) :
    ComputableInPolyTime (programCode A K) encRoutingMetadata PushPuzzle.NCL.Strip.Sweep.Cell.language.encProgram := by
  unfold programCode Word.Fixed.Language.encProgram
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (computableInPolyTime_scanLength A K))
  exact ((computableInPolyTime_step A K).comp
    (computableInPolyTime_siteInput A K)).of_enc_eq (fun _ => rfl)

/-- Compile the same selected actual finite instructions to the existing native graph data. -/
@[expose] def compile (A K : ℕ) (data : RoutingMetadata) : AndOrGraph :=
  PushPuzzle.NCL.Strip.Sweep.Cell.language.compile (programCode A K data)

/-- The complete native graph compiler is standard encoded polynomial-time. -/
theorem computableInPolyTime_compile (A K : ℕ) :
    ComputableInPolyTime (compile A K) encRoutingMetadata encAndOrGraph :=
  PushPuzzle.NCL.Strip.Sweep.Cell.language.computableInPolyTime_compile.comp (computableInPolyTime_programCode A K)

end PushPuzzle.NCL.Strip.PolyTime.ProgramData
