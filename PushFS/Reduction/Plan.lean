/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortOrder
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.CompilePolyTime
import Mathlib.Data.List.GetD

/-!
# Numbered layers of the source plane word

Each physical layer retains the exact wire stack and edge counter of the
upstream compiler. Its local vertices use those actual edge numbers. The
complete emitted vertex list is exactly `Word.compile`, preserving the source
initial and target bit interpretation. Prefix execution gives a polynomial-time
implementation and bounds every boundary width by the source encoding length.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Complexity.NCL

/-- One source layer with its exact compiler state before execution. -/
structure Layer where
  /-- The structural three-port instruction. -/
  instruction : Slice
  /-- Boundary wire numbers, next edge number and previously emitted vertices. -/
  before : Word.State

/-- Structural instruction followed by the compiler's unary wire stack and edge counter. -/
enc_structure encLayer : Layer where
  instruction : encSlice, before : Word.encState

/-- Execute a word while retaining the exact state at each layer. -/
def annotateFrom : Word → Word.State → List Layer
  | [], _ => []
  | instruction :: rest, st => ⟨instruction, st⟩ :: annotateFrom rest (instruction.run st)

/-- The numbered layers of a closed source word. -/
def annotate (w : Word) : List Layer := annotateFrom w ⟨[], 0, []⟩

/-- The vertices emitted by one layer, with their actual global edge names. -/
def emitted (l : Layer) : List (Vertex ℕ) :=
  (l.instruction.run ⟨l.before.wires, l.before.next, []⟩).verts

private theorem length_annotateFrom (w : Word) (st : Word.State) :
    (annotateFrom w st).length = w.length := by
  induction w generalizing st with
  | nil => rfl
  | cons instruction rest ih => simp only [annotateFrom, List.length_cons, ih]

private theorem step_vertices (instruction : Slice) (st : Word.State) :
    (instruction.run st).verts = st.verts ++ emitted ⟨instruction, st⟩ := by
  cases instruction <;> simp [Slice.run, emitted]

/-- Grouping vertices by physical layer recovers the exact upstream compilation output. -/
theorem run_vertices (w : Word) (st : Word.State) :
    (w.run st).verts = st.verts ++ (annotateFrom w st).flatMap emitted := by
  induction w generalizing st with
  | nil => simp only [Word.run, List.foldl_nil, annotateFrom, List.flatMap_nil, List.append_nil]
  | cons instruction rest ih =>
    change (Word.run rest (instruction.run st)).verts = _
    rw [ih, step_vertices]
    simp only [annotateFrom, List.flatMap_cons, List.append_assoc]

/-- The plan retains every source vertex and every original edge number. -/
theorem compiled_vertices (w : Word) :
    (annotate w).flatMap emitted = (Word.compile w).vertices := by
  simpa only [Word.compile, annotate, List.nil_append] using (run_vertices w ⟨[], 0, []⟩).symm

private theorem getElem_annotateFrom (w : Word) (st : Word.State) (i : ℕ) (hi : i < w.length) :
    (annotateFrom w st)[i]'(by rw [length_annotateFrom]; exact hi) =
      ⟨w[i], Word.run (w.take i) st⟩ := by
  induction w generalizing st i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons instruction rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [annotateFrom, List.getElem_cons_succ, List.take_succ_cons, Word.run,
        List.foldl_cons] using ih (instruction.run st) i (by simp only [List.length_cons] at hi; omega)

private def indexed (w : Word) : List Layer :=
  (List.range w.length).map fun i =>
    ⟨w.getD i (.swap 0), Word.run (w.take i) ⟨[], 0, []⟩⟩

private theorem annotate_eq_indexed (w : Word) : annotate w = indexed w := by
  apply List.ext_getElem
  · simp only [annotate, length_annotateFrom, indexed, List.length_map, List.length_range]
  · intro i hi _
    have hi' : i < w.length := by simpa only [annotate, length_annotateFrom] using hi
    simp only [annotate, getElem_annotateFrom w _ i hi', indexed, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ hi']

/-- Annotating all layer boundaries and retaining their numbered vertices is polynomial time. -/
theorem annotate_polyTime : ComputableInPolyTime annotate encWord (encList encLayer) := by
  have hprefix : ComputableInPolyTime (fun q : Word × ℕ => Word.run (q.1.take q.2) ⟨[], 0, []⟩)
      (encPair encWord encUnary) Word.encState :=
    Word.computableInPolyTime_run_empty.comp (by unfold encWord; fun_prop)
  have hi : ComputableInPolyTime indexed encWord (encList encLayer) := by
    unfold indexed
    fun_prop
  exact hi.of_enc_eq (fun w => congrArg (encList encLayer) (annotate_eq_indexed w))

/-- Each physical gate emits an actual AND/OR vertex of the compiled source. -/
theorem emitted_isAndOr {w : Word} (hw : (Word.compile w).Valid) {l : Layer}
    (hl : l ∈ annotate w) {v : Vertex ℕ} (hv : v ∈ emitted l) : v.IsAndOr := by
  have hmem : v ∈ (Word.compile w).vertices := by
    rw [← compiled_vertices]
    exact List.mem_flatMap.mpr ⟨l, hl, hv⟩
  have hc := (AndOrGraph.checkVertices_eq_true_iff (Word.compile w) hw.1).mpr hw.2.1
  exact (Vertex.checkAndOr_eq_true_iff v).mp (List.all_eq_true.mp hc v hmem)

end PushPuzzle.PushFS.Reduction.Plan
