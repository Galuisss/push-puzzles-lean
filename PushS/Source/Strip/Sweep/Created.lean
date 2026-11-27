/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Labeling
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word

/-!
# Actual labels in diagram creation order

Traverse a diagram in the same generator order as its word. Each generator contributes its
new outgoing edges. The resulting list contains exactly the inner edges' labels, so a distinct
creation stream proves injectivity of the actual labeling.

## Main definitions

* `PushPuzzle.NCL.Diagram.createdLabels`: actual labels of all created edges in word order.

## Main results

* `PushPuzzle.NCL.Diagram.mem_createdLabels`: every listed label belongs to an actual inner edge.
* `PushPuzzle.NCL.Diagram.createdLabels_injective`: distinct creation labels identify the inner edges.
-/

public section

namespace PushPuzzle.NCL.Diagram

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Diagram Cslib

variable {Γ : List Color → List Color → Type} {Label : Type*}

/-- Labels of all actual outgoing generator edges, in the word's order of creation. -/
@[expose] def createdLabels : {a b : List Color} → (D : Diagram Γ a b) →
    (D.Edge → Label) → List Label
  | _, _, .gen _, f => List.ofFn (fun j => f (.inr j))
  | _, _, .id _, _ | _, _, .swap .., _ => []
  | _, _, .comp D₁ D₂, f =>
      createdLabels D₁ (f ∘ compLeft D₁ D₂) ++ createdLabels D₂ (f ∘ compRight D₁ D₂)
  | _, _, .tensor D₁ D₂, f =>
      createdLabels D₁ (f ∘ tensorLeft D₁ D₂) ++ createdLabels D₂ (f ∘ tensorRight D₁ D₂)

/-- The actual creation stream has one entry for each inner diagram edge. -/
theorem length_createdLabels {a b : List Color} (D : Diagram Γ a b) (f : D.Edge → Label) :
    ((PushPuzzle.NCL.Diagram.createdLabels D) f).length = D.innerCount := by
  induction D with
  | gen g => exact List.length_ofFn
  | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [createdLabels, List.length_append, ih₁, ih₂, innerCount]

/-- Looking up an actual edge's creation index returns that exact edge's label. -/
theorem get_createdLabels {a b : List Color} (D : Diagram Γ a b) (f : D.Edge → Label)
    (e : D.Inner) :
    ((PushPuzzle.NCL.Diagram.createdLabels D) f)[D.idx e]'(by rw [length_createdLabels]; exact D.idx_lt e) = f (.inr e) := by
  induction D with
  | gen g =>
    simp only [createdLabels, idx, List.getElem_ofFn]
    apply congrArg f
    apply congrArg Sum.inr
    exact Fin.ext rfl
  | id _ | swap _ _ => exact e.elim
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    cases e with
    | inl e =>
      simp only [createdLabels, idx, Sum.elim_inl, List.getElem_append, length_createdLabels,
        D₁.idx_lt e, dite_true]
      exact ih₁ _ e
    | inr e =>
      have hn : ¬D₁.innerCount + D₂.idx e < D₁.innerCount := by omega
      simp only [createdLabels, idx, Sum.elim_inr, List.getElem_append, length_createdLabels, hn,
        dite_false, Nat.add_sub_cancel_left]
      exact ih₂ _ e

/-- Creation order lists exactly the labels of the actual inner edges. -/
theorem mem_createdLabels {a b : List Color} (D : Diagram Γ a b)
    (f : D.Edge → Label) (tag : Label) :
    tag ∈ (PushPuzzle.NCL.Diagram.createdLabels D) f ↔ ∃ e : D.Inner, f (.inr e) = tag := by
  induction D with
  | gen g => exact List.mem_ofFn
  | id _ | swap _ _ =>
    simp only [createdLabels, List.not_mem_nil, false_iff]
    rintro ⟨e, _⟩
    exact e.elim
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    rw [createdLabels, List.mem_append, ih₁, ih₂]
    constructor
    · rintro (⟨e, he⟩ | ⟨e, he⟩)
      · exact ⟨.inl e, he⟩
      · exact ⟨.inr e, he⟩
    · rintro ⟨e, he⟩
      cases e with
      | inl e => exact Or.inl ⟨e, he⟩
      | inr e => exact Or.inr ⟨e, he⟩

/-- Every actual edge label occurs on the input boundary or in actual creation order. -/
theorem Labeling.mem_top_or_created {a b : List Color} {D : Diagram Γ a b}
    {xs ys : List Label} (L : Labeling D xs ys) (e : D.Edge) :
    L.label e ∈ xs ++ (PushPuzzle.NCL.Diagram.createdLabels D) L.label := by
  cases e with
  | inl i =>
    apply List.mem_append_left
    have hm : L.label (.inl i) ∈ D.topList L.label := List.mem_ofFn.mpr ⟨i, rfl⟩
    simpa only [L.top_eq] using hm
  | inr e => exact List.mem_append_right _ ((mem_createdLabels D L.label _).mpr ⟨e, rfl⟩)

private theorem injective_sum_created {a b c d : List Color} (D₁ : Diagram Γ a b)
    (D₂ : Diagram Γ c d) (f : D₁.Edge → Label) (g : D₂.Edge → Label)
    (hf : Function.Injective (fun e : D₁.Inner => f (.inr e)))
    (hg : Function.Injective (fun e : D₂.Inner => g (.inr e)))
    (hn : ((PushPuzzle.NCL.Diagram.createdLabels D₁) f ++ (PushPuzzle.NCL.Diagram.createdLabels D₂) g).Nodup) :
    Function.Injective (Sum.elim (fun e => f (.inr e)) (fun e => g (.inr e))) := by
  have h := List.nodup_append.mp hn
  intro e e' he
  cases e with
  | inl e =>
    cases e' with
    | inl e' => exact congrArg Sum.inl (hf he)
    | inr e' =>
      have hl := (mem_createdLabels D₁ f (f (.inr e))).mpr ⟨e, rfl⟩
      have hr := (mem_createdLabels D₂ g (g (.inr e'))).mpr ⟨e', rfl⟩
      exact False.elim (h.2.2 _ hl _ hr he)
  | inr e =>
    cases e' with
    | inl e' =>
      have hl := (mem_createdLabels D₁ f (f (.inr e'))).mpr ⟨e', rfl⟩
      have hr := (mem_createdLabels D₂ g (g (.inr e))).mpr ⟨e, rfl⟩
      exact False.elim (h.2.2 _ hl _ hr he.symm)
    | inr e' => exact congrArg Sum.inr (hg he)

/-- Distinct actual creation labels give an injective labeling of all inner edges. -/
theorem createdLabels_injective {a b : List Color} (D : Diagram Γ a b) (f : D.Edge → Label)
    (hn : ((PushPuzzle.NCL.Diagram.createdLabels D) f).Nodup) : Function.Injective (fun e : D.Inner => f (.inr e)) := by
  induction D with
  | gen g => exact List.nodup_ofFn.mp hn
  | id _ | swap _ _ => intro e; exact e.elim
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    have h := List.nodup_append.mp hn
    have hh := injective_sum_created D₁ D₂ _ _ (ih₁ _ h.1) (ih₂ _ h.2.1) hn
    intro e e' he
    apply hh
    cases e <;> cases e' <;> exact he

/-- Stacked actual labelings concatenate their created-label streams. -/
theorem Labeling.createdLabels_comp {a b c : List Color} {D₁ : Diagram Γ a b}
    {D₂ : Diagram Γ b c} {x y z : List Label} (L : Labeling D₁ x y) (M : Labeling D₂ y z) :
    (PushPuzzle.NCL.Diagram.createdLabels (D₁.comp D₂)) (L.comp M).label =
      (PushPuzzle.NCL.Diagram.createdLabels D₁) L.label ++ (PushPuzzle.NCL.Diagram.createdLabels D₂) M.label := by
  simp only [createdLabels, Labeling.comp_label_left, Labeling.comp_label_right]

/-- Juxtaposed actual labelings concatenate their created-label streams. -/
theorem Labeling.createdLabels_tensor {a b c d : List Color} {D₁ : Diagram Γ a b}
    {D₂ : Diagram Γ c d} {x y z w : List Label} (L : Labeling D₁ x y) (M : Labeling D₂ z w) :
    (PushPuzzle.NCL.Diagram.createdLabels (D₁.tensor D₂)) (L.tensor M).label =
      (PushPuzzle.NCL.Diagram.createdLabels D₁) L.label ++ (PushPuzzle.NCL.Diagram.createdLabels D₂) M.label := by
  simp only [createdLabels, Labeling.tensor_label_left, Labeling.tensor_label_right]

end PushPuzzle.NCL.Diagram
