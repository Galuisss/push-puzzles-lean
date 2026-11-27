/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
public import PushFS.Reduction.StorageProfiles

/-! A diagonal complete glyph advances its ownership bit without changing any physical state. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.StorageAtlas

open scoped Classical
variable {n W H : ℕ} {Label : Fin n→Type} [∀i,Fintype (Label i)] (A : StorageAtlas n W H Label)

theorem profile_update_of_diagonal (f : Fin n→Bool) (i : Fin n) (p : Cell W H)
    (hi : (A.piece i).initial.boxes=(A.piece i).board.goals) :
    A.profileAt f p=A.profileAt (Function.update f i true) p := by
  apply State.ext
  · rfl
  · apply Finset.biUnion_congr rfl
    intro j _
    by_cases he : j=i
    · subst j
      cases hf : f i <;> simp only [pieceMarks,Function.update_self,hf,Bool.false_eq_true,ite_false,ite_true,hi]
    · simp only [pieceMarks,Function.update_of_ne he]

theorem profile_target_of_unchanged (f : Fin n→Bool)
    (hi : ∀i,f i=false→(A.piece i).initial.boxes=(A.piece i).board.goals) :
    A.profileBoxes f=A.board.goals := by
  have hh : A.profileBoxes f=A.profileBoxes (fun _=>true):=by
    apply Finset.biUnion_congr rfl
    intro i _
    cases hf : f i <;> simp only [pieceMarks,hf,Bool.false_eq_true,ite_false,ite_true]
    exact congrArg (fun boxes=>boxes.map (A.embedding i).cells) (hi i hf)
  exact hh.trans A.profile_target
end PushPuzzle.PushFS.Reduction.StorageAtlas
