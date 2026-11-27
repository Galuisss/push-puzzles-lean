/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.EdgeTrace

/-!
# Vertically composed concrete layer programs

The indexed implementation is polynomial time. Its recursive equation follows
the actual source compiler state and advances by the actual layer height.
The named trace of an allocated edge absent from the cut stays empty.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

namespace Plan

/-- Place all complete connections at their computed prefix-height rows. -/
def placedConnections (q : List Layer × ℕ) : List Route :=
  (List.range q.1.length).flatMap fun i =>
    let l := q.1.getD i ⟨.swap 0, ⟨[], 0, []⟩⟩
    l.connections.map (fun r => r.translate 0 (q.2 + rowOffset q.1 i))

/-- The numbered route program starting from an arbitrary source compiler cut. -/
def programFrom (w : Word) (st : Word.State) (y : ℕ) : List Route :=
  placedConnections (annotateFrom w st, y)

/-- The complete route program of the closed source word. -/
def program (w : Word) : List Route := programFrom w ⟨[], 0, []⟩ 0

/-- Advancing one layer preserves its real connection table and exact vertical offset. -/
private theorem placedConnections_cons (l : Layer) (ls : List Layer) (y : ℕ) :
    placedConnections (l :: ls, y) =
      l.connections.map (fun r => r.translate 0 y) ++ placedConnections (ls, y + l.height) := by
  simp [placedConnections, List.range_succ_eq_map, List.flatMap_map,
    rowOffset, Nat.add_assoc]

@[simp] theorem programFrom_nil (st : Word.State) (y : ℕ) : programFrom [] st y = [] := rfl

/-- Recursive source execution and the polynomial indexed implementation are identical. -/
theorem programFrom_cons (sl : Slice) (w : Word) (st : Word.State) (y : ℕ) :
    programFrom (sl :: w) st y =
      (Layer.mk sl st).connections.map (fun r => r.translate 0 y) ++
        programFrom w (sl.run st) (y + (Layer.mk sl st).height) := by
  exact placedConnections_cons _ _ _

@[fun_prop] theorem placedConnections_polyTime :
    ComputableInPolyTime placedConnections
      (encPair (encList encLayer) encUnary) (encList encRoute) := by
  unfold placedConnections
  dsimp only
  fun_prop

/-- The complete route program is generated in polynomial time under the actual source encoding. -/
theorem program_polyTime : ComputableInPolyTime program encWord (encList encRoute) := by
  have ha := annotate_polyTime
  unfold program programFrom
  change ComputableInPolyTime (fun w => placedConnections (annotate w, 0)) encWord (encList encRoute)
  fun_prop

/-- A typed drawing updates the numeric cut to its declared target width. -/
theorem drawn_after_length {sl : Slice} {a b : List Color}
    (D : sl.OrthogonalDrawing a b) (st : Word.State) (hlen : st.wires.length = a.length) :
    (sl.run st).wires.length = b.length := by
  rw [D.layer_eq]
  have hs := congrArg List.length D.source_eq
  have ht := congrArg List.length D.target_eq
  simp only [List.length_append] at hs ht
  simp only [Slice.run, List.length_append, List.length_take, List.length_ofFn, List.length_drop]
  omega

/-- Once an allocated edge has left the live cut, no subsequent route fragment reuses its name. -/
theorem programFrom_absent {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (st : Word.State) (hn : Numbered st)
    (hlen : st.wires.length = a.length) {e : ℕ} (he : e < st.next)
    (ha : e ∉ st.wires) (y : ℕ) (p : GridRouting.Point) :
    ¬Route.Trace (programFrom w st y) e p := by
  induction D generalizing st y with
  | nil a => simp [Route.Trace]
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl, st⟩
    have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
    rw [programFrom_cons, Route.trace_append]
    rintro (hlocal | hrest)
    · have ht := (Route.trace_translate _ e 0 y p).mp hlocal
      exact l.trace_absent he ha _ ht.2.2
    · have hn' := l.after_numbered hn hl
      have he' : e < (sl.run st).next := he.trans_le (by change st.next ≤ l.after.next; rw [l.after_next hl]; exact Nat.le_add_right _ _)
      exact ih _ hn' (drawn_after_length layer st hlen) he' (l.absent_after hl he ha) _ hrest

end Plan
end PushPuzzle.PushFS.Reduction
