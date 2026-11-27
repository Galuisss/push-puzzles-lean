/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceForward

/-! Exact serialized source endpoints for the complete physical NCL replay. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL Plan SourceCanonical

attribute [local irreducible] codes inventory

theorem checkedPuzzle_solvable_of_bits (w : ℕ) (hw : 2 ≤ w) (word : Word)
    (hG : word.compile.Valid) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (a b : List Bool) (ha : a.length = word.compile.edgeCount) (hb : b.length = word.compile.edgeCount)
    (G : ∀ f e,word.compile.graph.Legal f → word.compile.graph.Legal (reverse f e) →
      EdgeGeometry w hw word hP hT f e b)
    (hr : word.compile.graph.Reachable (word.compile.config a) (word.compile.config b)) :
    (checkedPuzzle w hw (word,(a,b)) hP hT).Solvable (some 1) := by
  have hcanonical := checkedPuzzle_solvable_of_ncl w hw word hG hP hT
    (fun f e hf he => by simpa only [configBits_config _ b hb] using G f e hf he) hr
  simpa only [configBits_config _ a ha,configBits_config _ b hb] using hcanonical

end PushPuzzle.PushS.FiniteSourceInventory
