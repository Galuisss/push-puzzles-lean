/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageProfiles

/-! Replay complete owned glyphs from a common player position through exact mixed-phase inventories. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.StorageAtlas


open scoped Classical
variable {n W H : ℕ} {Label : Fin n→Type} [∀i,Fintype (Label i)] (A : StorageAtlas n W H Label)

theorem mem_profileOutside_map (f : Fin n→Bool) (i : Fin n) (p : Cell W H) :
    p∈A.profileOutside f i ↔∃j : Fin n,j≠i ∧p∈(A.pieceMarks f j).map (A.embedding j).cells := by
  simp only [profileOutside,Finset.mem_biUnion,Finset.mem_erase,Finset.mem_univ,and_true]

theorem profile_place_source (f : Fin n→Bool) (i : Fin n) (hi : f i=false) :
    (A.embedding i).extend (A.profileOutside f i) (A.piece i).initial=
      A.profileAt f ((A.embedding i).cells (A.piece i).initial.player) := by
  apply State.ext
  · rfl
  · rw [profileAt,A.profile_split f i]
    simp only [GridEmbedding.extend,pieceMarks,hi,Bool.false_eq_true,ite_false]

theorem profile_place_target (f : Fin n→Bool) (i : Fin n) :
    (A.embedding i).extend (A.profileOutside f i) ⟨(A.piece i).initial.player,(A.piece i).board.goals⟩=
      A.profileAt (Function.update f i true) ((A.embedding i).cells (A.piece i).initial.player) := by
  apply State.ext
  · rfl
  · rw [profileAt,A.profile_split (Function.update f i true) i,A.profileOutside_update f i true]
    simp only [GridEmbedding.extend,pieceMarks,Function.update_self,ite_true]

end PushPuzzle.PushFS.Reduction.StorageAtlas
