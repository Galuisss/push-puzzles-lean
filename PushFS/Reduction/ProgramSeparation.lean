/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerSeparation
public import PushFS.Reduction.LayerProgram

/-!
# Separation of the actual complete source route program

At a shared layer boundary the standard column determines the very same live
edge on both sides. Distinct edge traces can consequently meet only at one
of the actual source vertices, including across arbitrarily many layers.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- One actual source vertex at its exact prefix-height row. -/
inductive VertexPointFrom : Word → Word.State → ℕ → GridRouting.Point → Prop
  | here (sl : Slice) (w : Word) (st : Word.State) (y : ℕ) :
      VertexPointFrom (sl :: w) st y
        ((Layer.mk sl st).vertexPoint.1, (Layer.mk sl st).vertexPoint.2 + y)
  | later {sl : Slice} {w : Word} {st : Word.State} {y : ℕ} {p : GridRouting.Point} :
      VertexPointFrom w (sl.run st) (y + (Layer.mk sl st).height) p →
      VertexPointFrom (sl :: w) st y p

/-- Every source layer has two positive routing bands around its gate. -/
private theorem Layer.height_pos (l : Layer) : 0 < l.height := by unfold Layer.height; omega

/-- Placement never emits a route pixel above the beginning of its source suffix. -/
theorem programFrom_row_lower (w : Word) (st : Word.State) (y : ℕ)
    {e : ℕ} {p : GridRouting.Point} (hp : Route.Trace (programFrom w st y) e p) : y ≤ p.2 := by
  induction w generalizing st y with
  | nil => simp [Route.Trace] at hp
  | cons sl w ih =>
    rw [programFrom_cons, Route.trace_append] at hp
    rcases hp with hp | hp
    · exact ((Route.trace_translate _ _ 0 y p).mp hp).2.1
    · have hh := ih (sl.run st) (y + (Layer.mk sl st).height) hp
      omega

/-- At the first row, the complete suffix meets precisely its real active incoming cut. -/
theorem programFrom_top {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hlen : st.wires.length = a.length) (y : ℕ)
    {e : ℕ} {p : GridRouting.Point} (hp : Route.Trace (programFrom w st y) e p) (hy : p.2 = y) :
    ∃ i : Fin st.wires.length, p.1 = 4 * i.val ∧ st.wires.getD i.val 0 = e := by
  cases D with
  | nil a => simp [Route.Trace] at hp
  | @cons sl w a b c layer rest =>
    let l : Layer := ⟨sl, st⟩
    have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
    rw [programFrom_cons, Route.trace_append] at hp
    rcases hp with hp | hp
    · have ht := (Route.trace_translate l.connections e 0 y p).mp hp
      have ht' : Route.Trace l.connections e (p.1, 0) := by
        simpa only [hy, Nat.sub_self, Nat.sub_zero] using ht.2.2
      exact (l.trace_classified hl ht').top hl rfl
    · have hh := programFrom_row_lower w (sl.run st) (y + l.height) hp
      have hpos := l.height_pos
      omega

private theorem interface_false {sl : Slice} {w : Word} {a b c : List Color}
    (layer : sl.OrthogonalDrawing a b) (rest : w.OrthogonalDrawing b c)
    (st : Word.State) (hlen : st.wires.length = a.length) (y : ℕ)
    {e f : ℕ} (hef : e ≠ f) (p : GridRouting.Point)
    (he : Route.Trace ((Layer.mk sl st).connections.map (fun r => r.translate 0 y)) e p)
    (hf : Route.Trace (programFrom w (sl.run st) (y + (Layer.mk sl st).height)) f p) : False := by
  let l : Layer := ⟨sl, st⟩
  have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
  have ht := (Route.trace_translate l.connections e 0 y p).mp he
  have hpart := l.trace_classified hl ht.2.2
  have hupper := hpart.row_le hl
  have hlower := programFrom_row_lower w (sl.run st) (y + l.height) hf
  have hy : p.2 = y + l.height := by omega
  have hy' : p.2 - y = l.height := by omega
  obtain ⟨i, hi, hie⟩ := hpart.bottom hl hy'
  obtain ⟨j, hj, hjf⟩ := programFrom_top rest (sl.run st) (drawn_after_length layer st hlen)
    (y + l.height) hf hy
  have hij : i.val = j.val := by dsimp only at hi; omega
  have hij' : i = j := Fin.ext hij
  exact hef (hie.symm.trans (hij' ▸ hjf))

/-- Every overlap between different emitted source-edge names lies at an actual source vertex. -/
theorem programFrom_separated {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hlen : st.wires.length = a.length) (y : ℕ)
    {e f : ℕ} (hef : e ≠ f) {p : GridRouting.Point}
    (he : Route.Trace (programFrom w st y) e p) (hf : Route.Trace (programFrom w st y) f p) :
    VertexPointFrom w st y p := by
  induction D generalizing st y with
  | nil a => simp [Route.Trace] at he
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl, st⟩
    have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
    rw [programFrom_cons, Route.trace_append] at he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · have he' := (Route.trace_translate l.connections e 0 y p).mp he
      have hf' := (Route.trace_translate l.connections f 0 y p).mp hf
      have hp := l.trace_separated hl hef he'.2.2 hf'.2.2
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      have heq : p = (l.vertexPoint.1, l.vertexPoint.2 + y) := by
        apply Prod.ext
        · dsimp only at hx
          omega
        · dsimp only at hy
          omega
      rw [heq]
      exact VertexPointFrom.here sl w st y
    · exact False.elim (interface_false layer rest st hlen y hef p he hf)
    · exact False.elim (interface_false layer rest st hlen y (Ne.symm hef) p hf he)
    · exact VertexPointFrom.later (ih (sl.run st) (drawn_after_length layer st hlen) (y + l.height) he hf)

end PushPuzzle.PushFS.Reduction.Plan
