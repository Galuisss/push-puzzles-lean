/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.BitMap
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Labeling

/-!
# Compositional serialization through actual wire labels

Read an arbitrary orientation through a diagram's actual wire labels, then apply a compositional
bit map. Matching labeled boundaries ensure that stacking and tensor preserve the actual
component orientations and serialize them in creation order.

## Main definitions

* `PushPuzzle.NCL.Diagram.BitMap.labelledBits`: serialize an orientation read through actual labels.

## Main results

* `PushPuzzle.NCL.Diagram.BitMap.labelledBits_comp`, `.labelledBits_tensor`: actual creation-order gluing.
-/

public section

namespace PushPuzzle.NCL.Diagram.BitMap

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Diagram Cslib.Complexity.NCL.Diagram.BitMap Cslib

variable {Γ : List Color → List Color → Type} (B : BitMap Γ)
  {Label : Type*} {a b c d : List Color} {xs ys zs ws : List Label}

/-- Serialize the transformed orientation obtained by reading the same actual wire labels. -/
@[expose] def labelledBits {D : Diagram Γ a b} (L : Labeling D xs ys) (u : Label → Bool) :
    List Bool := B.bits D (u ∘ L.label)

/-- Stacking matching actual labeled interfaces concatenates their created-edge bit streams. -/
theorem labelledBits_comp {D : Diagram Γ a b} {D' : Diagram Γ b c}
    (L : Labeling D xs ys) (L' : Labeling D' ys zs) (u : Label → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) (L.comp L') u = (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) L u ++ (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) L' u := by
  unfold labelledBits
  rw [B.bits_comp]
  simp only [Function.comp_assoc, Labeling.comp_label_left, Labeling.comp_label_right]

/-- Juxtaposition serializes the actual left component before the actual right component. -/
theorem labelledBits_tensor {D : Diagram Γ a b} {D' : Diagram Γ c d}
    (L : Labeling D xs ys) (L' : Labeling D' zs ws) (u : Label → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) (L.tensor L') u = (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) L u ++ (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) L' u := by
  unfold labelledBits
  rw [B.bits_tensor]
  simp only [Function.comp_assoc, Labeling.tensor_label_left, Labeling.tensor_label_right]

/-- Actual labeled identity wires create no configuration bits. -/
theorem labelledBits_id (a : List Color) (xs : List Label) (h : xs.length = a.length)
    (u : Label → Bool) : (PushPuzzle.NCL.Diagram.BitMap.labelledBits B) (Labeling.id (Γ := Γ) a xs h) u = [] :=
  B.bits_id _ _

end PushPuzzle.NCL.Diagram.BitMap
