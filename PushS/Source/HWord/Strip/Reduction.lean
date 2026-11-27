/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip.Configurations
public import PushS.Source.HWord.Strip.Drawing
public import PushS.Source.Strip.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Hardness
import all CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# PSPACE-hard native AND/OR reachability in a fixed strip

The same original word network compiles to its actual native AND/OR graph, its exact canonical
configuration vectors, and its actual standard vertex and directed route arrays. Their complete
continuous supports have fixed width and fixed longitudinal span, with fixed panel feature
budgets. All bounds depend only on the fixed source alphabet.

## Main definitions

* `PushPuzzle.NCL.HWord.Strip.Sweep.reduce`: the actual standard native graph/configuration/drawing compiler.

## Main results

* `PushPuzzle.NCL.HWord.Strip.Sweep.polyTimeReducible_strip`: standard fixed-H strip reduction.
* `exists_StripAndOrNCL_pspaceHard`: fixed strip width and span give PSPACE-hard reachability.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014].
* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*][VanDerZanden2015].
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

namespace HWord

open Cslib.Complexity.NCL.HWord

/-- Comparing the lengths of the two source words is polynomial-time. -/
theorem computableInPolyTime_sameLength (q : ℕ) :
    ComputableInPolyTime (fun x : Cslib.Complexity.NCL.HWord.Instance q =>
      decide (x.source.length = x.target.length)) (encInstance q) encBool := by
  have hs := encInstance_source_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have ht := encInstance_target_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  exact ((ComputableInPolyTime.length (encFinEnum (Fin q))).comp hs).beq
    ((ComputableInPolyTime.length (encFinEnum (Fin q))).comp ht)

end HWord

namespace HWord.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

private def rejected : PushPuzzle.NCL.StripAndOrNCL.Instance :=
  ⟨⟨{ edgeCount := 0, vertices := [] }, [], [true]⟩, ([], [])⟩

private theorem rejected_not_mem (width span : ℕ) : rejected ∉ StripAndOrNCL width span := by
  intro h
  have hlen := h.1.2.2.1
  change 1 = 0 at hlen
  omega

/-- Emit the same actual native graph, canonical direction vectors, and standard drawing arrays.
-/
@[expose] def compile (x : Instance q) : PushPuzzle.NCL.StripAndOrNCL.Instance where
  ncl := ⟨(program (n := x.source.length) H hq).compile,
    bits H hq x.source.length x.source, bits H hq x.source.length x.target⟩
  drawing := drawing H hq x.source.length

/-- The same complete actual graph/configuration/drawing compiler is standard polynomial-time.
-/
theorem computableInPolyTime_compile :
    ComputableInPolyTime (compile H hq) (encInstance q) encStripAndOrNCL := by
  have hs := encInstance_source_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have ht := encInstance_target_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have hn := (ComputableInPolyTime.length (encFinEnum (Fin q))).comp hs
  have hg := (computableInPolyTime_graph H hq).comp hn
  have hb := (computableInPolyTime_bits H hq).comp (hn.prod hs)
  have he := (computableInPolyTime_bits H hq).comp (hn.prod ht)
  have hd := (computableInPolyTime_drawing H hq).comp hn
  exact encStripAndOrNCL_mk_polyTime (encAndOrNCL_mk_polyTime hg hb he) hd

/-- The actual compiler uses exactly its emitted arrays and the fixed strip geometry. -/
theorem compile_validDrawing (x : Instance q) :
    PushPuzzle.NCL.StripAndOrNCL.ValidDrawing (drawingWidth q) (drawingSpan q) (compile H hq x) :=
  emitted_panel_drawing H hq

private theorem compile_mem_AndOrNCL_iff (x : Instance q) :
    (compile H hq x).ncl ∈ AndOrNCL ↔
      Legal H x.source.get ∧ Reachable H x.source.get (Planarized.targetWord hq x) := by
  have hs := bits_eq H hq x.source x.source.get (fun i => List.getD_eq_getElem _ _ i.isLt)
  have ht := bits_eq H hq x.target (Planarized.targetWord hq x) (fun _ => rfl)
  change (AndOrGraph.Valid _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
  dsimp only [compile]
  rw [and_iff_right (program_valid (n := x.source.length) H hq).toValid]
  simp only [hs, ht, List.length_ofFn, AndOrGraph.config_ofFn, true_and]
  exact and_congr (legal_orientation_iff H hq _) (reachable_orientation_iff H hq _ _)

/-- A total source reduction, using a fixed rejected instance for unequal word lengths. -/
def reduce (x : Instance q) : PushPuzzle.NCL.StripAndOrNCL.Instance :=
  if x.source.length = x.target.length then compile H hq x else rejected

/-- The total actual strip instance map is polynomial-time under the standard encodings. -/
private theorem computableInPolyTime_reduce :
    ComputableInPolyTime (reduce H hq) (encInstance q) encStripAndOrNCL := by
  have htest := computableInPolyTime_sameLength q
  exact (ComputableInPolyTime.ite_decide htest (computableInPolyTime_compile H hq)
    (ComputableInPolyTime.const rejected)).of_enc_eq (fun _ => rfl)

/-- The exact native configurations and drawing preserve and reflect the original word problem.
-/
theorem reduce_mem_iff (x : Instance q) :
    reduce H hq x ∈ StripAndOrNCL (drawingWidth q) (drawingSpan q) ↔ x ∈ language H := by
  rw [Planarized.language_iff H hq]
  by_cases hlen : x.source.length = x.target.length
  · rw [reduce, ite_eq_left hlen, and_iff_right hlen]
    change (compile H hq x).ncl ∈ AndOrNCL ∧ _ ↔ _
    rw [and_iff_left ⟨(program_valid (n := x.source.length) H hq).loopFree,
      compile_validDrawing H hq x⟩, compile_mem_AndOrNCL_iff]
  · rw [reduce, ite_eq_right hlen]
    exact iff_of_false (rejected_not_mem _ _) (fun h => hlen h.1)

omit [DecidableRel H.Adj] in
/-- The fixed-H language reduces to the same actual native constant-width strip family. -/
theorem polyTimeReducible_strip (hq : 0 < q) :
    PolyTimeReducible (encInstance q) encStripAndOrNCL (language H)
      (StripAndOrNCL (drawingWidth q) (drawingSpan q)) := by
  classical
  exact ⟨reduce H hq, computableInPolyTime_reduce H hq, fun x => (reduce_mem_iff H hq x).symm⟩

end HWord.Strip.Sweep

/-- For fixed width and fixed whole-route longitudinal span, standard native planar AND/OR
configuration reachability with the stated strip-panel bounds is PSPACE-hard. -/
theorem exists_StripAndOrNCL_pspaceHard :
    ∃ width span, PSPACEHard encStripAndOrNCL (StripAndOrNCL width span) := by
  classical
  obtain ⟨q, H, hq, hhard⟩ := HWord.exists_language_pspaceHard
  exact ⟨PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q, PushPuzzle.NCL.HWord.Strip.Sweep.drawingSpan q,
    hhard.trans (PushPuzzle.NCL.HWord.Strip.Sweep.polyTimeReducible_strip H hq)⟩

end PushPuzzle.NCL
