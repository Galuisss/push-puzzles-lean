/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusContacts

/-! The three actual buffered-lead/first-line contacts still needed to assemble the complete annular inventory. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


structure FrontierContactProofs (g : GateTileState) : Prop where
  walls : ∀ (i : Fin 4) (role : Fin 3) (j : Fin (curve (key g role)).length),
    i.val=role.val+1 → j.val=0 →
    ∀ (p : Cell (piece g (.inl i)).width (piece g (.inl i)).height)
      (q : Cell (piece g (.inr (.inl ⟨role,.inl j⟩))).width (piece g (.inr (.inl ⟨role,.inl j⟩))).height),
    ((offset g (.inl i)).1+p.1.val,(offset g (.inl i)).2+p.2.val)=
      ((offset g (.inr (.inl ⟨role,.inl j⟩))).1+q.1.val,(offset g (.inr (.inl ⟨role,.inl j⟩))).2+q.2.val) →
    (p∈(piece g (.inl i)).board.walls ↔ q∈(piece g (.inr (.inl ⟨role,.inl j⟩))).board.walls)
  sources : ∀ (i : Fin 4) (role : Fin 3) (j : Fin (curve (key g role)).length),
    i.val=role.val+1 → j.val=0 → ∀ (l : Labels g (.inl i)) (k : Labels g (.inr (.inl ⟨role,.inl j⟩))),
    ((offset g (.inl i)).1+((matching g (.inl i)).source l).1.val,
      (offset g (.inl i)).2+((matching g (.inl i)).source l).2.val)≠
    ((offset g (.inr (.inl ⟨role,.inl j⟩))).1+((matching g (.inr (.inl ⟨role,.inl j⟩))).source k).1.val,
      (offset g (.inr (.inl ⟨role,.inl j⟩))).2+((matching g (.inr (.inl ⟨role,.inl j⟩))).source k).2.val)
  targets : ∀ (i : Fin 4) (role : Fin 3) (j : Fin (curve (key g role)).length),
    i.val=role.val+1 → j.val=0 → ∀ (l : Labels g (.inl i)) (k : Labels g (.inr (.inl ⟨role,.inl j⟩))),
    ((offset g (.inl i)).1+((matching g (.inl i)).target l).1.val,
      (offset g (.inl i)).2+((matching g (.inl i)).target l).2.val)≠
    ((offset g (.inr (.inl ⟨role,.inl j⟩))).1+((matching g (.inr (.inl ⟨role,.inl j⟩))).target k).1.val,
      (offset g (.inr (.inl ⟨role,.inl j⟩))).2+((matching g (.inr (.inl ⟨role,.inl j⟩))).target k).2.val)

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
