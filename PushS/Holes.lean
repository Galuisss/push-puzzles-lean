/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Basic
public import Mathlib.Data.Fintype.Card

/-! A push transports its first destination hole to the player's next cell. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS

variable {w h n : ℕ} {B : Board w h} {cap : Option ℕ} {d : Direction}
  {s t : State w h}

/-- Empty cells, including the player's cell. -/
def holes (s : State w h) : Finset (Cell w h) := s.boxesᶜ

@[simp] theorem mem_holes (p : Cell w h) : p ∈ holes s ↔ p ∉ s.boxes :=
  Finset.mem_compl

theorem player_mem_holes (hs : s.Valid B) : s.player ∈ holes s :=
  (mem_holes _).mpr hs.2.2

private theorem card_holes (s : State w h) : (holes s).card = w * h - s.boxes.card := by
  simp [holes, Finset.card_compl, Fintype.card_prod]

theorem card_holes_reachable (hr : Reachable B cap s t) :
    (holes t).card = (holes s).card := by
  rw [card_holes, card_holes, hr.card_boxes]

/-- The old player cell remains empty after a walk or a push. -/
theorem source_player_mem_holes (hm : Move B cap d s t) : s.player ∈ holes t := by
  cases hm with
  | walk hv _ _ _ hb => simpa [hb] using hv.2.2
  | @push n hv hn _ run _ hb =>
    have hne : s.player ≠ run.cell ⟨n + 1, by omega⟩ := by
      intro he
      have he' := run.injective (run.start.trans he)
      have := congrArg Fin.val he'
      simp only [Fin.val_zero] at this
      omega
    simp only [mem_holes, hb, Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨hne, fun h => hv.2.2 h.2⟩

theorem players_adjacent (hm : Move B cap d s t) : Adjacent d s.player t.player := by
  cases hm with
  | walk _ ha _ _ _ => exact ha
  | push _ _ _ run hp _ =>
    simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, run.start, hp] using
      run.adjacent 0

/-- Only the first box cell and the first empty destination change occupancy. -/
theorem holes_push (run : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1))) :
    holes t = insert (run.cell 1) ((holes s).erase (run.cell ⟨n + 1, by omega⟩)) := by
  have hq := run.first_occupied hn
  have hne : run.cell 1 ≠ run.cell ⟨n + 1, by omega⟩ := by
    intro he
    have := congrArg Fin.val (run.injective he)
    simp only [Fin.val_one] at this
    omega
  ext p
  simp only [mem_holes, hb, Finset.mem_insert, Finset.mem_erase]
  by_cases hp : p = run.cell 1
  · subst p
    simp [hne]
  · simp only [hp, false_or]
    tauto

/-- A newly created hole is the player's new cell. -/
theorem hole_source_of_ne_player (hm : Move B cap d s t) {p : Cell w h}
    (hp : p ≠ t.player) (ht : p ∈ holes t) : p ∈ holes s := by
  cases hm with
  | walk _ _ _ _ hb => simpa [mem_holes, hb] using ht
  | push _ hn _ run hplayer hb =>
    rw [holes_push run hn hb, Finset.mem_insert] at ht
    rcases ht with he | ht
    · exact False.elim (hp (he.trans hplayer.symm))
    · exact Finset.mem_of_mem_erase ht

end PushPuzzle.PushS
