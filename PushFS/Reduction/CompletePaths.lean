/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerProgram

/-!
# Complete named paths of the actual closed source word

Each active edge continues until its consuming input. Each allocated edge
therefore has a complete orthogonal path from its creating output to its
consuming input. Its trace is exactly every emitted pixel with that edge name.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- An actual consuming input incidence, placed at the source compiler's layer row. -/
inductive InputEndpoint : Word → Word.State → ℕ → ℕ → GridRouting.Point → Prop
  | here (sl : Slice) (w : Word) (st : Word.State) (y : ℕ)
      (i : Fin sl.data.inputs.length) :
      InputEndpoint (sl :: w) st y
        ((Layer.mk sl st).inputPort i.val).port.edge
        ((Layer.mk sl st).vertexPoint.1, (Layer.mk sl st).vertexPoint.2 + y)
  | later {sl : Slice} {w : Word} {st : Word.State} {y e : ℕ} {p : GridRouting.Point} :
      InputEndpoint w (sl.run st) (y + (Layer.mk sl st).height) e p →
      InputEndpoint (sl :: w) st y e p

/-- An actual creating output incidence, placed at the source compiler's layer row. -/
inductive OutputEndpoint : Word → Word.State → ℕ → ℕ → GridRouting.Point → Prop
  | here (sl : Slice) (w : Word) (st : Word.State) (y : ℕ)
      (i : Fin sl.data.outputs.length) :
      OutputEndpoint (sl :: w) st y ((Layer.mk sl st).outputPort i.val).port.edge
        ((Layer.mk sl st).vertexPoint.1, (Layer.mk sl st).vertexPoint.2 + y)
  | later {sl : Slice} {w : Word} {st : Word.State} {y e : ℕ} {p : GridRouting.Point} :
      OutputEndpoint w (sl.run st) (y + (Layer.mk sl st).height) e p →
      OutputEndpoint (sl :: w) st y e p

theorem incoming_endpoint {sl : Slice} {w : Word} {st : Word.State} {y : ℕ}
    (i : Fin st.wires.length) (hx : (Layer.mk sl st).exitIndex i.val = none) :
    InputEndpoint (sl :: w) st y (st.wires.getD i.val 0)
      ((Layer.mk sl st).vertexPoint.1, (Layer.mk sl st).vertexPoint.2 + y) := by
  let l : Layer := ⟨sl, st⟩
  have hi : l.instruction.data.offset ≤ i.val ∧
      i.val < l.instruction.data.offset + l.instruction.data.inputs.length := by
    change l.exitIndex i.val = none at hx
    unfold Layer.exitIndex at hx
    split_ifs at hx; simp_all
  have hj : i.val - l.instruction.data.offset < sl.data.inputs.length := by
    change i.val - l.instruction.data.offset < l.instruction.data.inputs.length
    omega
  have he : sl.data.offset + (i.val - sl.data.offset) = i.val := by
    change l.instruction.data.offset + (i.val - l.instruction.data.offset) = i.val
    omega
  simpa only [Layer.inputPort, he] using
    InputEndpoint.here sl w st y ⟨i.val - sl.data.offset, hj⟩

end PushPuzzle.PushFS.Reduction.Plan
