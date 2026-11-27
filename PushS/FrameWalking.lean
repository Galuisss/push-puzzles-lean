/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.HoleState

/-! Finite straight paths of actual holes lift to ordinary player walks with fixed boxes. -/

public section
namespace PushPuzzle.PushS.HoleState


open PushFS

variable {w h : ℕ}

/-- Traverse a concrete finite line of holes, using only the original walk constructor. -/
theorem walk_along (s : HoleState w h) (B : Board w h) (hB : B.walls = ∅) (cap : Option ℕ)
    (d : Direction) (n : ℕ) (cell : Fin (n + 1) → Cell w h) (hstart : cell 0 = s.player)
    (ha : ∀ i : Fin n, Adjacent d (cell i.castSucc) (cell i.succ))
    (he : ∀ i, cell i ∈ s.empty) :
    Reachable B cap s.toState (s.walk (cell (Fin.last n)) (he _)).toState := by
  have path (i : Fin (n + 1)) :
      Reachable B cap s.toState (s.walk (cell i) (he _)).toState := by
    induction i using Fin.induction with
    | zero =>
      change Reachable B cap s.toState { player := cell 0, boxes := s.emptyᶜ }
      rw [hstart]
      exact .refl
    | succ i ih =>
      apply ih.tail
      refine ⟨d, Move.walk ((s.walk (cell i.castSucc) (he _)).valid B hB) (ha i)
        (by simp [hB]) ?_ rfl⟩
      simpa only [toState, walk, Finset.mem_compl, not_not] using he i.succ
  exact path (Fin.last n)

end PushPuzzle.PushS.HoleState
