/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReadExact
public import PushPush.Walking

/-! A whole-run read may pay more holes while returning to the prescribed quota level. -/

@[expose] public section
namespace PushPuzzle.PushPush.Reader

open PushFS (Cell State)

variable {w h : ℕ}

theorem read_north_selected_path (quota : ℕ) (s : State w h) (cutoff : ℕ)
    (F : Finset (Cell w h)) (H : ExactNorthRead (northData s cutoff) F)
    (hpaid : quota ≤ (northData s cutoff \ F).card) (hv : s.player ∉ s.boxes)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ p : Cell w h, p.1 = s.player.1 → cutoff ≤ p.2.val →
      p.2.val < s.player.2.val → p ∈ s.boxes) :
    ∃ t : State w h, ReadPath s t ∧ t.player.1 = s.player.1 ∧
      t.player.2.val + quota = s.player.2.val ∧ northData t cutoff = F ∧
      (∀ p : Cell w h, p.1 ≠ s.player.1 → (p ∈ t.boxes ↔ p ∈ s.boxes)) ∧
      t.boxesᶜ = (s.boxesᶜ \ (northData s cutoff \ F)) ∪
        northTrail s (northData s cutoff \ F).card := by
  let actual := (northData s cutoff \ F).card
  have hc : actual ≤ (northData s cutoff).card := Finset.card_le_card Finset.sdiff_subset
  obtain ⟨u, hr, hux, huy, hF, hframe, hholes⟩ :=
    read_north_exact_path actual s cutoff F H rfl hv hspace hgap
  let row : Fin h := ⟨s.player.2.val - quota, by have := s.player.2.isLt; omega⟩
  let t : State w h := ⟨(u.player.1, row), u.boxes⟩
  have hwalk : ReadPath u t := by
    change ReadPath ⟨(u.player.1, u.player.2), u.boxes⟩ ⟨(u.player.1, row), u.boxes⟩
    apply ReadPath.walk_vertical
    intro y hlo hhi
    have hyu : u.player.2.val ≤ row.val := by dsimp [row]; omega
    rw [Nat.min_eq_left hyu] at hlo
    rw [Nat.max_eq_right hyu] at hhi
    by_cases he : y = u.player.2
    · simpa only [he] using hr.valid hv
    · apply Finset.mem_compl.mp
      rw [hholes]
      by_cases hs : y.val = s.player.2.val
      · apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, ?_⟩
        · have hp : (u.player.1, y) = s.player := Prod.ext hux (Fin.ext hs)
          exact hp.symm ▸ Finset.mem_compl.mpr hv
        · intro hh
          have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hh).1).2.2
          change y.val < cutoff at this
          omega
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hux, ?_, ?_⟩ <;> dsimp [row] at * <;> omega
  refine ⟨t, hr.trans hwalk, hux, by dsimp [t, row]; omega, ?_, hframe, hholes⟩
  exact hF

end PushPuzzle.PushPush.Reader
