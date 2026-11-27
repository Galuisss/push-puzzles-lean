/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Reduction.InventoryAssembly

/-! Exact physical selections from the actual assembled initial inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.InventoryAssembly

open scoped Classical

variable {n W H : ℕ} {Label : Fin n → Type} [∀ i, Fintype (Label i)]

/-- The literal physical identities owned by one source primitive. -/
def pieceLabels (A : InventoryAssembly n W H Label) (i : Fin n) : Finset A.PhysicalLabel :=
  Finset.univ.map (A.labelEmbedding i)

@[simp] theorem mem_pieceLabels (A : InventoryAssembly n W H Label) (i : Fin n) (l : A.PhysicalLabel) :
    l ∈ A.pieceLabels i ↔ l.1 = i := by
  constructor
  · intro hl
    obtain ⟨q,_,he⟩ := Finset.mem_map.mp hl
    exact (congrArg Sigma.fst he).symm
  · intro hl
    rcases l with ⟨j,q⟩
    dsimp at hl
    subst j
    exact Finset.mem_map.mpr ⟨q,Finset.mem_univ _,rfl⟩

end PushPuzzle.PushFS.Reduction.InventoryAssembly
