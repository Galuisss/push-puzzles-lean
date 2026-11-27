/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.StripSourceConfiguration
public import PushS.StripSourceGeometry
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.StepPolyTime
import all PushS.Source.HWord.Strip.Reduction
import all PushS.StripSourceConfiguration

/-! The actual fixed-alphabet word family and its polynomial-time endpoint checks. -/

public section
namespace PushPuzzle.PushS.WordSource

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The original fixed-alphabet compiler, including its actual native drawing arrays. -/
abbrev native := PushPuzzle.NCL.HWord.Strip.Sweep.compile H hq

/-- Every emitted original native graph is a valid AND/OR graph. -/
theorem native_valid (x : NCL.HWord.Instance q) : NCL.SourceValid (native H hq x).ncl.graph :=
  PushPuzzle.NCL.HWord.Strip.Sweep.program_valid H hq

/-- All words emit the same fixed-width, fixed-span drawing family. -/
theorem native_validDrawing (x : NCL.HWord.Instance q) :
    PushPuzzle.NCL.StripAndOrNCL.ValidDrawing (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)
      (PushPuzzle.NCL.HWord.Strip.Sweep.drawingSpan q) (native H hq x) :=
  PushPuzzle.NCL.HWord.Strip.Sweep.compile_validDrawing H hq x

/-- Every initial native vector contains exactly one bit per emitted original edge. -/
theorem native_initial_length (x : NCL.HWord.Instance q) :
    (native H hq x).ncl.initial.length = (native H hq x).ncl.graph.edgeCount :=
  PushPuzzle.NCL.HWord.Strip.Sweep.length_bits H hq _ _

/-- Every target native vector contains exactly one bit per emitted original edge. -/
theorem native_target_length (x : NCL.HWord.Instance q) :
    (native H hq x).ncl.target.length = (native H hq x).ncl.graph.edgeCount :=
  PushPuzzle.NCL.HWord.Strip.Sweep.length_bits H hq _ _

/-- The actual native drawing contains exactly the original vertex and edge arrays. -/
theorem native_drawing_counts (x : NCL.HWord.Instance q) :
    (native H hq x).drawing.1.length = (native H hq x).ncl.graph.vertices.length ∧
      (native H hq x).drawing.2.length = (native H hq x).ncl.graph.edgeCount := by
  obtain ⟨P, he, _⟩ := native_validDrawing H hq x
  rw [← he]
  exact ⟨List.length_ofFn, List.length_ofFn⟩

/-- Check equal source lengths and the two actual native endpoint configurations. -/
@[expose] def guard (x : NCL.HWord.Instance q) : Bool :=
  decide (x.source.length = x.target.length) &&
    (native H hq x).ncl.graph.checkLegal (native H hq x).ncl.initial &&
    (native H hq x).ncl.graph.checkLegal (native H hq x).ncl.target

/-- The executable guard checks exactly equal lengths and the two actual native legalities. -/
theorem guard_eq_true_iff (x : NCL.HWord.Instance q) :
    guard H hq x = true ↔ x.source.length = x.target.length ∧
      (native H hq x).ncl.graph.graph.Legal
        ((native H hq x).ncl.graph.config (native H hq x).ncl.initial) ∧
      (native H hq x).ncl.graph.graph.Legal
        ((native H hq x).ncl.graph.config (native H hq x).ncl.target) := by
  have hg := native_valid H hq x
  simp only [guard, Bool.and_eq_true, decide_eq_true_eq,
    NCL.AndOrGraph.checkLegal_eq_true_iff _ hg.1]
  exact and_assoc

/-- Reading and checking the actual endpoint vectors is standard polynomial-time. -/
theorem computableInPolyTime_guard :
    ComputableInPolyTime (guard H hq) (NCL.HWord.encInstance q) encBool := by
  have hn : ComputableInPolyTime (native H hq) (NCL.HWord.encInstance q) PushPuzzle.NCL.encStripAndOrNCL :=
    PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq
  have hd := PushPuzzle.NCL.encStripAndOrNCL_ncl_polyTime hn
  have hg := NCL.encAndOrNCL_graph_polyTime hd
  have hs := NCL.encAndOrNCL_initial_polyTime hd
  have ht := NCL.encAndOrNCL_target_polyTime hd
  have hl := NCL.HWord.computableInPolyTime_sameLength q
  have hi := NCL.AndOrGraph.computableInPolyTime_checkLegal hg
    ((bits_encList_polyTime encBool).2.comp hs)
  have he := NCL.AndOrGraph.computableInPolyTime_checkLegal hg
    ((bits_encList_polyTime encBool).2.comp ht)
  change ComputableInPolyTime (fun x : NCL.HWord.Instance q =>
    decide (x.source.length = x.target.length) &&
      (native H hq x).ncl.graph.checkLegal (native H hq x).ncl.initial &&
      (native H hq x).ncl.graph.checkLegal (native H hq x).ncl.target) _ _
  exact (hl.bool_and' hi).bool_and' he

/-- Every accepted word instance passes the actual endpoint guard. -/
theorem guard_of_mem {x : NCL.HWord.Instance q} (hx : x ∈ NCL.HWord.language H) :
    guard H hq x = true := by
  have hm := (PushPuzzle.NCL.HWord.Strip.Sweep.reduce_mem_iff H hq x).mpr hx
  have hlen : x.source.length = x.target.length := by
    obtain ⟨t, ht, _, _⟩ := hx
    rw [← ht, List.length_ofFn]
  rw [PushPuzzle.NCL.HWord.Strip.Sweep.reduce, ite_eq_left hlen] at hm
  exact (guard_eq_true_iff H hq x).mpr
    ⟨hlen, hm.1.2.2.2.1, hm.1.2.2.2.2.legal hm.1.2.2.2.1⟩

/-- On equal-length words, membership is exactly the original native graph's reachability. -/
theorem native_mem_iff (x : NCL.HWord.Instance q)
    (hlen : x.source.length = x.target.length) :
    (native H hq x).ncl ∈ NCL.AndOrNCL ↔ x ∈ NCL.HWord.language H := by
  have hr := PushPuzzle.NCL.HWord.Strip.Sweep.reduce_mem_iff H hq x
  rw [PushPuzzle.NCL.HWord.Strip.Sweep.reduce, ite_eq_left hlen] at hr
  exact (and_iff_left ⟨(native_valid H hq x).loopFree, native_validDrawing H hq x⟩).symm.trans hr

/-- For admitted endpoints, the original native path is exactly the original word problem. -/
theorem native_reachable_iff {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    (native H hq x).ncl.graph.graph.Reachable
      ((native H hq x).ncl.graph.config (native H hq x).ncl.initial)
      ((native H hq x).ncl.graph.config (native H hq x).ncl.target) ↔
      x ∈ NCL.HWord.language H := by
  have hg := (guard_eq_true_iff H hq x).mp hx
  rw [← native_mem_iff H hq x hg.1]
  exact ⟨fun hr => ⟨native_valid H hq x, native_initial_length H hq x,
    native_target_length H hq x, hg.2.1, hr⟩, fun hm => hm.2.2.2.2⟩

private theorem native_ordered (x : NCL.HWord.Instance q) (bits : List Bool)
    (hs : (native H hq x).ncl.graph.graph.Legal
      ((native H hq x).ncl.graph.config bits)) :
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).OrderedInputs
      ((Comb.ConfigurationInput.mk (StripSource.toComb (native H hq x)) bits).normalizedAxes
        (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)) := by
  obtain ⟨hv, he'⟩ := native_drawing_counts H hq x
  exact (Comb.ConfigurationInput.mk (StripSource.toComb (native H hq x)) bits).normalizedAxes_orderedInputs
    _ (native_valid H hq x) hs hv he'

/-- Every admitted word emits ordered legal actual initial contour directions. -/
theorem initial_ordered {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).OrderedInputs
      (StripSource.normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)) :=
  native_ordered H hq x _ ((guard_eq_true_iff H hq x).mp hx).2.1

/-- Every admitted word emits ordered legal actual target contour directions. -/
theorem target_ordered {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).OrderedInputs
      (StripSource.normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)) :=
  native_ordered H hq x _ ((guard_eq_true_iff H hq x).mp hx).2.2

end PushPuzzle.PushS.WordSource
