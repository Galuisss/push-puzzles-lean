/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: local-only (certifies the pinned routing implementation's concrete segment data)

public import PushFS.Reduction.Segments
public import PushFS.UnarySum
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridRouting
import Mathlib.Data.List.GetD

/-!
# Executable data for disjoint routing bands

Two ordered rows are connected through the same six-segment construction as
the upstream geometric routing theorem. The raw list program has a polynomial-
time machine certificate. Its exact equality with the geometric paths supplies
pairwise disjointness for the emitted segment data.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Turing.MultiTapeTM ComputableInPolyTime
open NCL.GridRouting
open scoped PushPuzzle.PushFS.Reduction

/-- The unary columns of two ordered boundary rows. -/
structure Band where
  /-- Top columns, in wire order. -/
  source : List ℕ
  /-- Bottom columns, in the same wire order. -/
  target : List ℕ

/-- Two framed lists of unary endpoint columns. -/
enc_structure encBand : Band where
  source : (encList encUnary), target : (encList encUnary)

/-- The six explicit segments of one route through two joined routing bands. -/
def Band.curve (q : Band × ℕ) : List Segment :=
  let n := q.1.source.length
  let i := q.2
  let s := q.1.source.getD i 0
  let t := q.1.target.getD i 0
  let mid := (q.1.source ++ q.1.target).sum + i + 1
  [⟨(s, 0), (s, n - i)⟩,
   ⟨(s, n - i), (mid, n - i)⟩,
   ⟨(mid, n - i), (mid, n + 1)⟩,
   ⟨(mid, n + 1), (mid, i + 1 + (n + 1))⟩,
   ⟨(mid, i + 1 + (n + 1)), (t, i + 1 + (n + 1))⟩,
   ⟨(t, i + 1 + (n + 1)), (t, n + 1 + (n + 1))⟩]

/-- Unary column data from two finite ordered rows. -/
def Band.ofFunctions {n : ℕ} (source target : Fin n → ℕ) : Band :=
  ⟨List.ofFn source, List.ofFn target⟩

private theorem segments_cast {p q p' q' : Point} (r : NCL.GridRouting.Path p q) (hp : p = p') (hq : q = q') :
    segments (r.cast hp hq) = segments r := by
  cases hp
  cases hq
  rfl

private theorem segments_translate {p q : Point} (r : NCL.GridRouting.Path p q) (dx dy : ℕ) :
    segments (r.translate dx dy) = (segments r).map
      (fun s => Segment.mk (s.start.1 + dx, s.start.2 + dy) (s.finish.1 + dx, s.finish.2 + dy)) := by
  induction r with
  | horizontal => rfl
  | vertical => rfl
  | comp r s ihr ihs => simp only [NCL.GridRouting.Path.translate, segments, ihr, ihs, List.map_append]

/-- The actual raw segment program emits precisely the upstream constructed path. -/
private theorem Band.curve_ofFunctions {n : ℕ} (source target : Fin n → ℕ)
    (hs : StrictMono source) (ht : StrictMono target) (i : Fin n) :
    Band.curve (Band.ofFunctions source target, i.val) =
      segments ((route source target hs ht).path i) := by
  rw [OrderedRouting.path]
  change _ = segments _ ++ segments _
  rw [segments_cast, segments_cast, segments_translate]
  simp [Band.curve, Band.ofFunctions, Elbow.path, segments, route, portBound,
    List.getD_eq_getElem?_getD, i.isLt]

/-- The route data represent exactly the geometric routing trace. -/
private theorem Band.curve_trace {n : ℕ} (source target : Fin n → ℕ)
    (hs : StrictMono source) (ht : StrictMono target) (i : Fin n) (p : Point) :
    (∃ s ∈ Band.curve (Band.ofFunctions source target, i.val), s.Contains p) ↔
      (route source target hs ht).Contains i p := by
  rw [Band.curve_ofFunctions source target hs ht i, mem_segments_iff,
    OrderedRouting.path_contains_iff]

/-- Distinct emitted routes have disjoint lattice traces. -/
theorem Band.curves_disjoint {n : ℕ} (source target : Fin n → ℕ)
    (hs : StrictMono source) (ht : StrictMono target) {i j : Fin n} (hij : i ≠ j) (p : Point) :
    ¬((∃ s ∈ Band.curve (Band.ofFunctions source target, i.val), s.Contains p) ∧
      (∃ s ∈ Band.curve (Band.ofFunctions source target, j.val), s.Contains p)) := by
  rw [Band.curve_trace source target hs ht i p, Band.curve_trace source target hs ht j p]
  exact (route source target hs ht).disjoint hij p

/-- Building one six-segment route has a polynomial-time machine under unary coordinates. -/
@[fun_prop] theorem Band.curve_polyTime :
    ComputableInPolyTime Band.curve (encPair encBand encUnary) (encList encSegment) := by
  have hn : ComputableInPolyTime (fun q : Band × ℕ => q.1.source.length)
      (encPair encBand encUnary) encUnary := by fun_prop
  have hs : ComputableInPolyTime (fun q : Band × ℕ => q.1.source.getD q.2 0)
      (encPair encBand encUnary) encUnary := by fun_prop
  have ht : ComputableInPolyTime (fun q : Band × ℕ => q.1.target.getD q.2 0)
      (encPair encBand encUnary) encUnary := by fun_prop
  have hm : ComputableInPolyTime (fun q : Band × ℕ => (q.1.source ++ q.1.target).sum + q.2 + 1)
      (encPair encBand encUnary) encUnary := by fun_prop
  unfold Band.curve
  dsimp only
  fun_prop

end PushPuzzle.PushFS.Reduction
