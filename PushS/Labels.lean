/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Labels

/-! Complete physical identities for arbitrary-length simultaneous box pushes. -/

@[expose] public section
namespace PushPuzzle.PushS.Labels

open PushFS

variable {w h n : ℕ} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h}

private def source (r : Run B d s n) (i : Fin n) : Cell w h :=
  r.cell ⟨i.val + 1, by omega⟩

private def destination (r : Run B d s n) (i : Fin n) : Cell w h :=
  r.cell ⟨i.val + 2, by omega⟩

private theorem source_injective (r : Run B d s n) : Function.Injective (source r) := by
  intro i j he
  have h := congrArg Fin.val (r.injective he)
  apply Fin.ext
  change i.val + 1 = j.val + 1 at h
  omega

private theorem destination_injective (r : Run B d s n) :
    Function.Injective (destination r) := by
  intro i j he
  have h := congrArg Fin.val (r.injective he)
  apply Fin.ext
  change i.val + 2 = j.val + 2 at h
  omega

/-- Shift every box in the consecutive run one cell, fixing all other cells. -/
noncomputable def shiftMap (r : Run B d s n) (p : Cell w h) : Cell w h := by
  classical
  exact if hi : ∃ i : Fin n, r.cell ⟨i.val + 1, by omega⟩ = p then
    r.cell ⟨(Classical.choose hi).val + 2, by omega⟩ else p

private theorem shift_source (r : Run B d s n) (i : Fin n) :
    shiftMap r (source r i) = destination r i := by
  classical
  have hi : ∃ j : Fin n, source r j = source r i := ⟨i, rfl⟩
  change (if h : ∃ j : Fin n, source r j = source r i then
    destination r (Classical.choose h) else source r i) = destination r i
  rw [dite_eq_left hi]
  exact congrArg (destination r) (source_injective r (Classical.choose_spec hi))

private theorem shift_other (r : Run B d s n) (p : Cell w h)
    (hp : ¬∃ i : Fin n, source r i = p) : shiftMap r p = p := by
  classical
  change (if h : ∃ i : Fin n, source r i = p then
    destination r (Classical.choose h) else p) = p
  rw [dite_eq_right hp]

/-- A box at run index i+1 moves to index i+2. -/
theorem shiftMap_on (r : Run B d s n) (i : Fin n) :
    shiftMap r (r.cell ⟨i.val + 1, by omega⟩) = r.cell ⟨i.val + 2, by omega⟩ :=
  shift_source r i

/-- A box either stays in place or has its exact source and destination run indices. -/
theorem shiftMap_cases (r : Run B d s n) (p : Cell w h) :
    shiftMap r p = p ∨ ∃ i : Fin n, p = r.cell ⟨i.val + 1, by omega⟩ ∧
      shiftMap r p = r.cell ⟨i.val + 2, by omega⟩ := by
  classical
  by_cases hp : ∃ i : Fin n, source r i = p
  · obtain ⟨i, rfl⟩ := hp
    exact Or.inr ⟨i, rfl, shift_source r i⟩
  · exact Or.inl (shift_other r p hp)

/-- Every physical identity outside the run keeps its position. -/
private theorem shiftMap_of_not_in_run (r : Run B d s n) (p : Cell w h)
    (hp : ∀ i, p ≠ r.cell i) : shiftMap r p = p :=
  shift_other r p (fun ⟨i, he⟩ => hp ⟨i.val + 1, by omega⟩ he.symm)

private theorem destination_last (r : Run B d s n) (i : Fin n)
    (hi : ¬i.val + 2 ≤ n) : destination r i = r.cell ⟨n + 1, by omega⟩ := by
  apply congrArg r.cell
  apply Fin.ext
  change i.val + 2 = n + 1
  omega

private theorem destination_ne_stationary (r : Run B d s n) (i : Fin n)
    {p : Cell w h} (hp : p ∈ s.boxes) (hoff : ¬∃ j : Fin n, source r j = p) :
    destination r i ≠ p := by
  intro he
  by_cases hi : i.val + 2 ≤ n
  · let j : Fin n := ⟨i.val + 1, by omega⟩
    have hj : source r j = destination r i := rfl
    exact hoff ⟨j, hj.trans he⟩
  · have hp' : destination r i ∈ s.boxes := he.symm ▸ hp
    exact r.empty (destination_last r i hi ▸ hp')

/-- Simultaneously shifted physical boxes remain pairwise distinct. -/
theorem shiftMap_injOn (r : Run B d s n) : Set.InjOn (shiftMap r) s.boxes := by
  classical
  intro p hp q hq he
  by_cases hp' : ∃ i : Fin n, source r i = p
  · obtain ⟨i, rfl⟩ := hp'
    rw [shift_source] at he
    by_cases hq' : ∃ j : Fin n, source r j = q
    · obtain ⟨j, rfl⟩ := hq'
      rw [shift_source] at he
      exact congrArg (source r) (destination_injective r he)
    · rw [shift_other r q hq'] at he
      exact False.elim (destination_ne_stationary r i hq hq' he)
  · rw [shift_other r p hp'] at he
    by_cases hq' : ∃ j : Fin n, source r j = q
    · obtain ⟨j, rfl⟩ := hq'
      rw [shift_source] at he
      exact False.elim (destination_ne_stationary r j hp hp' he.symm)
    · simpa only [shift_other r q hq'] using he

private theorem destination_mem (r : Run B d s n) (i : Fin n) :
    destination r i ∈ insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)) := by
  by_cases hi : i.val + 2 ≤ n
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have h := congrArg Fin.val (r.injective he)
      change i.val + 2 = 1 at h
      omega
    · exact r.occupied_at _ (by change 0 < i.val + 2; omega) hi
  · exact (destination_last r i hi).symm ▸ Finset.mem_insert_self _ _

/-- The physical shift has exactly the unlabelled box-set update of a real push. -/
theorem image_shiftMap (r : Run B d s n) (hn : 0 < n) :
    s.boxes.image (shiftMap r) =
      insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    by_cases hi : ∃ i : Fin n, source r i = q
    · obtain ⟨i, rfl⟩ := hi
      rw [shift_source]
      exact destination_mem r i
    · rw [shift_other r q hi]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      exact ⟨fun he => hi ⟨⟨0, hn⟩, he.symm⟩, hq⟩
  · rw [Finset.card_image_of_injOn (shiftMap_injOn r),
      Finset.card_insert_of_notMem (fun h => r.empty (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem (r.first_occupied hn)]
    have := Finset.card_pos.mpr ⟨_, r.first_occupied hn⟩
    omega

variable {ι : Type} [Fintype ι]

/-- A real walk or complete simultaneous push, with its physical box updates. -/
inductive MultiMove (B : Board w h) (cap : Option ℕ) (d : Direction)
    (S T : LabelledState ι w h) : Prop
  | walk (valid : S.state.Valid B) (adjacent : Adjacent d S.state.player T.state.player)
      (floor : T.state.player ∉ B.walls) (empty : T.state.player ∉ S.state.boxes)
      (boxes : T.state.boxes = S.state.boxes) (positions : T.position = S.position) :
      MultiMove B cap d S T
  | push {n : ℕ} (valid : S.state.Valid B) (positive : 0 < n) (permitted : Permits cap n)
      (run : Run B d S.state n) (player : T.state.player = run.cell 1)
      (boxes : T.state.boxes = insert (run.cell ⟨n + 1, by omega⟩)
        (S.state.boxes.erase (run.cell 1)))
      (positions : T.position = shiftMap run ∘ S.position) : MultiMove B cap d S T

/-- One labelled step at the specified finite or unlimited push cap. -/
def MultiStep (B : Board w h) (cap : Option ℕ) (S T : LabelledState ι w h) : Prop :=
  ∃ d, MultiMove B cap d S T

theorem MultiMove.forget {S T : LabelledState ι w h} (hm : MultiMove B cap d S T) :
    PushFS.Move B cap d S.state T.state := by
  cases hm with
  | walk hv ha hf he hb _ => exact .walk hv ha hf he hb
  | push hv hn hc r hp hb _ => exact .push hv hn hc r hp hb

/-- Lift every legal move, shifting every box of its complete run simultaneously. -/
private theorem lift_move (S : LabelledState ι w h) {t : State w h}
    (hm : PushFS.Move B cap d S.state t) :
    ∃ T : LabelledState ι w h, T.state = t ∧ MultiMove B cap d S T := by
  classical
  cases hm with
  | walk hv ha hf he hb =>
    let T : LabelledState ι w h :=
      ⟨t, S.position, S.injective, S.boxes_image.trans hb.symm⟩
    exact ⟨T, rfl, .walk hv ha hf he hb rfl⟩
  | push hv hn hc r hp hb =>
    have hinj : Function.Injective (shiftMap r ∘ S.position) := by
      intro i j he
      exact S.injective (shiftMap_injOn r (S.position_mem i) (S.position_mem j) he)
    have himage : Finset.univ.image (shiftMap r ∘ S.position) = t.boxes := by
      rw [← Finset.image_image, S.boxes_image, image_shiftMap r hn, hb]
    let T : LabelledState ι w h := ⟨t, _, hinj, himage⟩
    exact ⟨T, rfl, .push hv hn hc r hp hb rfl⟩

theorem lift_step (S : LabelledState ι w h) {t : State w h}
    (hs : PushFS.Step B cap S.state t) :
    ∃ T : LabelledState ι w h, T.state = t ∧ MultiStep B cap S T := by
  obtain ⟨d, hm⟩ := hs
  obtain ⟨T, ht, hmove⟩ := lift_move S hm
  exact ⟨T, ht, d, hmove⟩

/-- The position update fixes each physical identity outside the actual run. -/
theorem position_eq_of_not_in_run {S T : LabelledState ι w h}
    (r : Run B d S.state n) (hpos : T.position = shiftMap r ∘ S.position)
    (i : ι) (hi : ∀ j, S.position i ≠ r.cell j) : T.position i = S.position i := by
  rw [hpos, Function.comp_apply, shiftMap_of_not_in_run r _ hi]

end PushPuzzle.PushS.Labels
