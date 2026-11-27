/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Radius

/-! The global hole budget keeps the reader's far eastern reserve unvisited. -/

public section
namespace PushPuzzle.Push.ReaderRadius

open PushFS PushS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {s t : State w h}

/-- Any real trajectory stays strictly within the initial total hole budget. -/
private theorem distance_lt_holes (hr : Reachable B cap s t) (hs : s.player ∉ s.boxes) :
    distance s.player t.player < (holes s).card := by
  have he : Relation.ReflTransGen (Radius.ExcursionStep B cap ∅) s t :=
    Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm, Finset.empty_subset _, Finset.notMem_empty _⟩)
      _ _ hr
  have hd := Radius.excursion_distance he
  have hc := Finset.card_erase_add_one ((mem_holes _).mpr hs)
  simp only [Finset.sdiff_empty] at hd
  omega

/-- Every visited column is strictly west of this bound from the starting column. -/
private theorem player_column_lt (hr : Reachable B cap s t) (hs : s.player ∉ s.boxes) :
    t.player.1.val < s.player.1.val + (holes s).card := by
  have hd := distance_lt_holes hr hs
  simp only [distance, Nat.dist] at hd
  omega

/-- The far eastern reserve cannot be reached, even when its holes are consumed remotely. -/
theorem east_reserve_unvisited (hr : Reachable B cap s t) (hs : s.player ∉ s.boxes)
    {east : ℕ} (he : s.player.1.val + (holes s).card ≤ east) : t.player.1.val < east :=
  (player_column_lt hr hs).trans_le he

end PushPuzzle.Push.ReaderRadius
