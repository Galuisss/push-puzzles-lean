/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Vertices
public import Mathlib.Data.Fintype.Fin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Actual vertex labels in compilation order

Read labels in the same generator order as the actual word and vertex list. Actual finite
vertex numbering returns the corresponding label at each index.

## Main definitions

* `PushPuzzle.NCL.Diagram.vertexLabels`: actual interpreted-vertex labels in compilation order.

## Main results

* `PushPuzzle.NCL.Diagram.get_vertexLabels`: actual finite numbering recovers the original vertex's label.
* `PushPuzzle.NCL.Diagram.vertexLabels_const`: a constant-labeled implementation gives one repeated block.
-/

public section

namespace PushPuzzle.NCL.Diagram

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Diagram Cslib

variable {Γ : List Color → List Color → Type} (I : Interp Γ) {Label : Type*}

/-- Labels of actual interpreted vertices, in their actual compilation order. -/
@[expose] def vertexLabels : {a b : List Color} → (D : Diagram Γ a b) →
    (D.Vtx I → Label) → List Label
  | _, _, .gen _, f => List.ofFn f
  | _, _, .id _, _ | _, _, .swap .., _ => []
  | _, _, .comp D D', f | _, _, .tensor D D', f =>
      vertexLabels D (f ∘ Sum.inl) ++ vertexLabels D' (f ∘ Sum.inr)

/-- Exactly one label is read for each actual compiled vertex. -/
private theorem length_vertexLabels {a b : List Color} (D : Diagram Γ a b) (f : D.Vtx I → Label) :
    (vertexLabels I D f).length = (vertexList I D).length := by
  induction D with
  | gen g => exact List.length_ofFn
  | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [vertexLabels, List.length_append, ih₁, ih₂, vertexList, List.length_map]

/-- Actual finite vertex numbering reads back that exact vertex's actual label. -/
theorem get_vertexLabels {a b : List Color} (D : Diagram Γ a b)
    (f : D.Vtx I → Label) (v : D.Vtx I) :
    (vertexLabels I D f)[(vertexEquiv I D v).val]'(by
      rw [length_vertexLabels]; exact (vertexEquiv I D v).isLt) = f v := by
  induction D with
  | gen g =>
    change (List.ofFn (fun i : Fin (I.verts g).length => f i))[v.val]'(by
      rw [List.length_ofFn]; exact v.isLt) = f v
    simp only [List.getElem_ofFn]
    apply congrArg f
    exact Fin.ext rfl
  | id _ | swap _ _ => exact v.elim
  | comp D D' ih₁ ih₂ | tensor D D' ih₁ ih₂ =>
    cases v with
    | inl v =>
      have hi : (vertexEquiv I D v).val < (vertexLabels I D (f ∘ Sum.inl)).length := by
        rw [length_vertexLabels]
        exact (vertexEquiv I D v).isLt
      change (vertexLabels I D (f ∘ Sum.inl) ++ vertexLabels I D' (f ∘ Sum.inr))[
        (vertexEquiv I D v).val]'(by rw [List.length_append]; omega) = f (.inl v)
      rw [List.getElem_append_left hi]
      exact ih₁ _ v
    | inr v =>
      change (vertexLabels I D (f ∘ Sum.inl) ++ vertexLabels I D' (f ∘ Sum.inr))[
        (vertexList I D).length + (vertexEquiv I D' v).val]'(by
          rw [List.length_append, length_vertexLabels, length_vertexLabels]
          have := (vertexEquiv I D' v).isLt
          omega) = f (.inr v)
      rw [List.getElem_append_right (by rw [length_vertexLabels]; omega)]
      simp only [length_vertexLabels, Nat.add_sub_cancel_left]
      exact ih₂ _ v

/-- A constant stage on an actual local implementation gives one actual repeated vertex block.
-/
theorem vertexLabels_const {a b : List Color} (D : Diagram Γ a b) (label : Label) :
    vertexLabels I D (fun _ => label) = List.replicate (vertexList I D).length label := by
  induction D with
  | gen g =>
    change List.ofFn (fun _ : Fin (I.verts g).length => label) =
      List.replicate (I.verts g).length label
    exact List.ofFn_const _ label
  | id _ | swap _ _ => rfl
  | comp D D' ih₁ ih₂ | tensor D D' ih₁ ih₂ =>
    simp only [vertexLabels, vertexList, List.length_append, List.length_map, List.replicate_add]
    exact congrArg₂ (· ++ ·) ih₁ ih₂

/-- The actual label list is the actual finite vertex enumeration read through its inverse. -/
theorem vertexLabels_eq_ofFn {a b : List Color} (D : Diagram Γ a b) (f : D.Vtx I → Label) :
    vertexLabels I D f = List.ofFn (fun i => f ((vertexEquiv I D).symm i)) := by
  apply List.ext_getElem (by rw [length_vertexLabels, List.length_ofFn])
  intro i hi _
  have hj : i < (vertexList I D).length := by simpa only [length_vertexLabels] using hi
  have h := get_vertexLabels I D f ((vertexEquiv I D).symm ⟨i, hj⟩)
  simpa only [Equiv.apply_symm_apply, List.getElem_ofFn] using h

/-- The multiplicity of a vertex label equals the cardinality of its actual vertex fiber. -/
theorem count_vertexLabels [DecidableEq Label] {a b : List Color} (D : Diagram Γ a b)
    (f : D.Vtx I → Label) (label : Label) :
    (vertexLabels I D f).count label = Nat.card {v // f v = label} := by
  rw [vertexLabels_eq_ofFn, List.count_ofFn]
  have he := (vertexEquiv I D).symm.subtypeEquiv
    (q := fun v => f v = label) (fun _ => Iff.rfl)
  rw [← Nat.card_congr he]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

end PushPuzzle.NCL.Diagram
