/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Bits

/-!
# Exact serialized configurations of the native diagram compiler

The existing compiler simulation numbers original edges in their exact creation order. Reading
its full native configuration therefore returns the original diagram bit stream.

## Main results

* `PushPuzzle.NCL.Diagram.compileSimulation_bits`: exact native edge-order serialization.
-/

public section

namespace PushPuzzle.NCL.Diagram

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Diagram Cslib

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- The existing native compiler simulation serializes in the diagram's exact edge-number order.
-/
theorem compileSimulation_bits (D : Diagram Γ [] []) (s : D.Edge → Bool) :
    List.ofFn ((compileSimulation I D).enc s) = D.bits s := by
  have transport (G : AndOrGraph) (h : G = AndOrGraph.ofFinite (finiteGraph I D)) :
      let S : ConstraintGraph.Simulation (D.graph I) G.graph := h.symm ▸
        ((finiteSimulation I D).trans (AndOrGraph.ofFiniteSimulation (finiteGraph I D)))
      List.ofFn (S.enc s) = D.bits s := by
    cases h
    rfl
  exact transport _ (compile_toWord I D)

end PushPuzzle.NCL.Diagram
