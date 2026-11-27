/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Labeling
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Substitution
import Mathlib.Logic.Function.Basic

/-!
# Relabeling and extending actual diagram boundary labels

Map a diagram's labels, or extend them through the injective boundary-preserving edge map of an
open simulation. The latter keeps every original edge label and uses the supplied labels only

for new internal edges.

## Main definitions

* `PushPuzzle.NCL.Diagram.Labeling.map`: apply a function to every actual edge and boundary label.
* `PushPuzzle.NCL.Diagram.Labeling.extend`: extend actual labels along an open simulation's edge injection.

## Main results

* `PushPuzzle.NCL.Diagram.Labeling.extend_label_image`: original edges retain their exact labels.
* `PushPuzzle.NCL.Diagram.Labeling.extend_label_not_image`: new edges use the supplied internal labels.
-/

public section

namespace PushPuzzle.NCL.Diagram.Labeling

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Diagram Cslib.Complexity.NCL.Diagram.Labeling Cslib

variable {Γ Γ' : List Color → List Color → Type} {I : Interp Γ} {I' : Interp Γ'}
  {a b : List Color} {D : Diagram Γ a b} {D' : Diagram Γ' a b} {Label Label' : Type*}
  {xs ys : List Label}

/-- Apply a function to the same actual edge labels and both actual boundary lists. -/
@[expose] def map (L : Labeling D xs ys) (f : Label → Label') :
    Labeling D (xs.map f) (ys.map f) where
  label := f ∘ L.label
  top_eq := (List.ofFn_comp' (fun i : Fin a.length => L.label (.inl i)) f).trans
    (congrArg (List.map f) L.top_eq)
  bot_eq := (List.ofFn_comp' (fun i : Fin b.length => L.label (D.bottom i)) f).trans
    (congrArg (List.map f) L.bot_eq)

/-- Keep the actual boundary-preserving image labels and fill the remaining internal edges. -/
@[expose] noncomputable def extend (L : Labeling D xs ys) (S : OpenSim I I' D D')
    (internal : D'.Edge → Label) : Labeling D' xs ys where
  label := Function.extend S.ι L.label internal
  top_eq := by
    refine Eq.trans ?_ L.top_eq
    apply congrArg List.ofFn
    funext i
    exact (congrArg (Function.extend S.ι L.label internal) (S.ι_top i)).symm.trans
      (S.ι_injective.extend_apply L.label _ _)
  bot_eq := by
    refine Eq.trans ?_ L.bot_eq
    apply congrArg List.ofFn
    funext i
    exact (congrArg (Function.extend S.ι L.label internal) (S.ι_bottom i)).symm.trans
      (S.ι_injective.extend_apply L.label _ _)

/-- Every actual original edge retains its exact old label after extension. -/
theorem extend_label_image (L : Labeling D xs ys) (S : OpenSim I I' D D')
    (internal : D'.Edge → Label) (e : D.Edge) :
    ((PushPuzzle.NCL.Diagram.Labeling.extend L) S internal).label (S.ι e) = L.label e := S.ι_injective.extend_apply L.label internal e

/-- Every new internal edge uses its supplied internal label. -/
theorem extend_label_not_image (L : Labeling D xs ys) (S : OpenSim I I' D D')
    (internal : D'.Edge → Label) (e : D'.Edge) (he : ¬∃ f, S.ι f = e) :
    ((PushPuzzle.NCL.Diagram.Labeling.extend L) S internal).label e = internal e := Function.extend_apply' _ _ _ he

end PushPuzzle.NCL.Diagram.Labeling
