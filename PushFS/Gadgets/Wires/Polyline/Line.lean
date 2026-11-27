/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Components

/-! Explicit bidirectional static paths on a literal floor half-row. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


variable {w h : ℕ}

private theorem horizontal_tail_component_of_le {B : Board w h} (y : Fin h)
    (cut : ℕ) (hf : ∀ x : Fin w, cut≤x.val → (x,y) ∉ B.walls) (a b : Fin w)
    (ha : cut < a.val) (hb : b.val+1 < w) (hab : a.val ≤ b.val) :
    SameComponent B (a,y) (b,y) := by
  let positions : Fin (b.val-a.val+1) → Cell w h :=
    fun i => (⟨a.val+i.val,by have := i.isLt; omega⟩,y)
  have he : ∀ i, component B (positions 0) = component B (positions i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      let rear : Cell w h := (⟨a.val+i.val-1,by have := i.isLt; omega⟩,y)
      let ahead : Cell w h := (⟨a.val+i.val+2,by have := i.isLt; omega⟩,y)
      have hforward : Displacement B (positions i.castSucc) (positions i.succ) := by
        refine ⟨hf _ (by dsimp [positions]; omega),.east,rear,?_,?_,hf _ (by dsimp [rear]; omega),hf _ (by dsimp [positions]; omega)⟩
        · constructor
          · dsimp [rear,positions]
            omega
          · rfl
        · constructor
          · dsimp [positions]
            omega
          · rfl
      have hbackward : Displacement B (positions i.succ) (positions i.castSucc) := by
        refine ⟨hf _ (by dsimp [positions]; omega),.west,ahead,?_,?_,hf _ (by dsimp [ahead]; omega),hf _ (by dsimp [positions]; omega)⟩
        · constructor
          · dsimp [ahead,positions]
            omega
          · rfl
        · constructor
          · dsimp [positions]
            omega
          · rfl
      exact ih.trans (component_eq_iff.mpr ⟨.single hforward,.single hbackward⟩)
  have hs : positions 0 = (a,y) := by apply Prod.ext <;> apply Fin.ext <;> simp [positions]
  have ht : positions (Fin.last (b.val-a.val)) = (b,y) := by
    apply Prod.ext <;> apply Fin.ext
    · dsimp [positions]
      omega
    · rfl
  exact component_eq_iff.mp (by simpa only [hs,ht] using he (Fin.last (b.val-a.val)))

/-- Any two interior cells of a completely free floor row share an actual static SCC. -/
theorem horizontal_tail_component {B : Board w h} (y : Fin h)
    (cut : ℕ) (hf : ∀ x : Fin w, cut≤x.val → (x,y) ∉ B.walls) (a b : Fin w)
    (ha : cut < a.val ∧ a.val+1 < w) (hb : cut < b.val ∧ b.val+1 < w) :
    SameComponent B (a,y) (b,y) := by
  rcases le_total a.val b.val with hab | hba
  · exact horizontal_tail_component_of_le y cut hf a b ha.1 hb.2 hab
  · have hh := horizontal_tail_component_of_le y cut hf b a hb.1 ha.2 hba
    exact ⟨hh.2,hh.1⟩

end PushPuzzle.PushFS.Gadgets.Wires.Polyline
