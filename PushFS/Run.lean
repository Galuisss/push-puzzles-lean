/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Basic

/-!
# Consecutive box runs

Directional coordinates prove injectivity of a run and bound its length by the
number of boxes. Legal moves preserve legality and box count.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h n : ℕ} {B : Board w h} {d : Direction} {s t : State w h}

namespace Run

theorem position (r : Run B d s n) (i : Fin (n + 2)) :
    d.position (r.cell i) = d.position s.player + i.val := by
  induction i using Fin.induction with
  | zero => simp only [r.start, Fin.val_zero, Int.natCast_zero, Int.add_zero]
  | succ i ih =>
    have ha := (r.adjacent i).position
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    rw [ha, ih]
    omega

theorem lane (r : Run B d s n) (i : Fin (n + 2)) :
    d.lane (r.cell i) = d.lane s.player := by
  induction i using Fin.induction with
  | zero => rw [r.start]
  | succ i ih => exact (r.adjacent i).lane.trans ih

theorem injective (r : Run B d s n) : Function.Injective r.cell := by
  intro i j he
  have hi := r.position i
  have hj := r.position j
  rw [he] at hi
  apply Fin.ext
  omega

theorem occupied_at (r : Run B d s n) (i : Fin (n + 2)) (hi : 0 < i.val)
    (hin : i.val ≤ n) : r.cell i ∈ s.boxes := by
  have he : (⟨(i.val - 1) + 1, by omega⟩ : Fin (n + 2)) = i := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  exact he ▸ r.occupied ⟨i.val - 1, by omega⟩

theorem first_occupied (r : Run B d s n) (hn : 0 < n) : r.cell 1 ∈ s.boxes :=
  r.occupied_at 1 (by simp) (by simp only [Fin.val_one]; omega)

theorem length_le_card (r : Run B d s n) : n ≤ s.boxes.card := by
  let f : Fin n → Cell w h := fun i => r.cell ⟨i.val + 1, by omega⟩
  have hf : Function.Injective f := by
    intro i j he
    have := r.injective he
    apply Fin.ext
    have := congrArg Fin.val this
    simpa only [Fin.val_mk, Nat.add_right_cancel_iff] using this
  have hc := Finset.card_image_of_injective (s := Finset.univ) hf
  have hs : Finset.univ.image f ⊆ s.boxes := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact r.occupied i
  have := Finset.card_le_card hs
  simpa only [hc, Finset.card_univ, Fintype.card_fin] using this

end Run

theorem Move.valid_target {cap : Option ℕ} (hm : Move B cap d s t) : t.Valid B := by
  cases hm with
  | walk hv _ hf he hb => exact ⟨hf, hb ▸ hv.2.1, hb ▸ he⟩
  | push hv hn _ run hp hb =>
    refine ⟨hp ▸ run.floor 1, ?_, ?_⟩
    · rw [hb, Finset.disjoint_insert_left]
      exact ⟨run.floor _, hv.2.1.mono_left (Finset.erase_subset _ _)⟩
    · rw [hp, hb]
      simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
      constructor
      · intro he
        have := run.injective he
        have := congrArg Fin.val this
        simp only [Fin.val_one] at this
        omega
      · exact fun hne => False.elim (hne rfl)

private theorem Move.card_boxes {cap : Option ℕ} (hm : Move B cap d s t) :
    t.boxes.card = s.boxes.card := by
  cases hm with
  | walk _ _ _ _ hb => exact congrArg Finset.card hb
  | push _ hn _ run _ hb =>
    have hp := run.first_occupied hn
    rw [hb, Finset.card_insert_of_notMem
      (fun h => run.empty (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hp]
    have := Finset.card_pos.mpr ⟨_, hp⟩
    omega

theorem Step.valid_target {cap : Option ℕ} (hs : Step B cap s t) : t.Valid B :=
  hs.choose_spec.valid_target

theorem Step.card_boxes {cap : Option ℕ} (hs : Step B cap s t) :
    t.boxes.card = s.boxes.card := hs.choose_spec.card_boxes

theorem Reachable.valid {cap : Option ℕ} (hr : Reachable B cap s t)
    (hs : s.Valid B) : t.Valid B := by
  induction hr with
  | refl => exact hs
  | tail _ hm _ => exact hm.valid_target

theorem Reachable.card_boxes {cap : Option ℕ} (hr : Reachable B cap s t) :
    t.boxes.card = s.boxes.card := by
  induction hr with
  | refl => rfl
  | tail _ hm ih => exact hm.card_boxes.trans ih

end PushPuzzle.PushFS
