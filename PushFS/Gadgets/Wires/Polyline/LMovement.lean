/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.LWalking

/-! Complete physical phase transmission through the assembled L: tail, turn, then incoming train. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline.L


variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

theorem phases_uniform (a : Bool) : phases a a a=uniform a := by funext i; fin_cases i <;> rfl

/-- Every physical target identity is exactly the source identity in the reversed static endpoint assignment. -/
theorem target_source_global (a b : Phases) : (atlas m n hm hn a b).target=(atlas m n hm hn b a).source := by
  apply Function.Embedding.ext
  rintro ⟨i,l⟩
  have hh := target_source m n hm hn a b i l
  apply Prod.ext <;> apply Fin.ext
  · change dx i+((matching m n hm hn a b i).target l).1.val=dx i+((matching m n hm hn b a i).source l).1.val
    exact congrArg (dx i+·) (congrArg Prod.fst hh)
  · change dy i+((matching m n hm hn a b i).target l).2.val=dy i+((matching m n hm hn b a i).source l).2.val
    exact congrArg (dy i+·) (congrArg Prod.snd hh)

theorem goals_eq (a b : Phases) : (atlas m n hm hn a b).board.goals=boxes m n hm hn b := by
  change Finset.univ.map (atlas m n hm hn a b).target=_
  rw [target_source_global]
  exact initial_boxes m n hm hn b a

theorem board_eq (a b : Phases) : (atlas m n hm hn a b).board=board m n hm hn (boxes m n hm hn b) :=
  Board.ext (atlas_walls m n hm hn a b) (goals_eq m n hm hn a b)

end PushPuzzle.PushFS.Gadgets.Wires.Polyline.L
