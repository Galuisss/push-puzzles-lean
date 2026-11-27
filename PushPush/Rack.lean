/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.LineCoordinates

/-! The extremal rack column cannot receive boxes in an interior trajectory. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k : ℕ} {d : Direction} {s t : State w h}

namespace Slide

private theorem line_mono (d : Direction) (lane : ℕ) {A B : Finset (Cell w h)} (hAB : A ⊆ B) :
    line d lane A ⊆ line d lane B := by
  intro z hz
  obtain ⟨p, hp, hl, he⟩ := mem_line.mp hz
  exact mem_line.mpr ⟨p, hAB hp, hl, he⟩

private theorem line_disjoint (d : Direction) (lane : ℕ) {A B : Finset (Cell w h)}
    (hAB : Disjoint A B) : Disjoint (line d lane A) (line d lane B) := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨p, hp, hlp, hzp⟩ := mem_line.mp hz
  obtain ⟨q, hq, hlq, hzq⟩ := mem_line.mp hw
  have he : p = q := d.cell_ext (hlp.trans hlq.symm) (hzp.trans hzq.symm)
  exact Finset.disjoint_left.mp hAB hp (he ▸ hq)

/-- A horizontal slide cannot add a box to the easternmost occupied column. -/
private theorem horizontal_after_empty (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hd : d = .east ∨ d = .west) {P : ℕ} (hs : Supported .east P s)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) : line .south P r.after = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨p, hp, hl, _⟩ := mem_line.mp hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hib := hs _ (r.occupied i)
  have hip := r.position ⟨i.val + 1, by omega⟩
  have hjp := r.position ⟨k + i.val + 1, by omega⟩
  dsimp only at hip hjp
  rcases hd with rfl | rfl
  · obtain ⟨q, hq, ha⟩ := r.exists_stopper hn ht
    have hqb := hs q hq
    have hqp := ha.position
    have hlast := r.position ⟨n + k, by omega⟩
    dsimp only at hlast
    simp only [Direction.position, Direction.lane] at hib hip hjp hl hqb hqp hlast
    omega
  · simp only [Direction.position, Direction.lane] at hib hip hjp hl
    omega

theorem horizontal_column (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hd : d = .east ∨ d = .west) {P : ℕ} (hs : Supported .east P s)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) :
    line .south P r.boxes = line .south P s.boxes \ line .south P r.before := by
  rw [Slide.boxes, line_union, line_sdiff, r.horizontal_after_empty hn hk hd hs ht,
    Finset.union_empty]

theorem vertical_before_lane (r : Slide d s n k) (hd : d = .north ∨ d = .south)
    {p : Cell w h} (hp : p ∈ r.before) : p.1.val = s.player.1.val := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have := r.lane ⟨i.val + 1, by omega⟩
  rcases hd with rfl | rfl <;> exact this

theorem vertical_after_lane (r : Slide d s n k) (hd : d = .north ∨ d = .south)
    {p : Cell w h} (hp : p ∈ r.after) : p.1.val = s.player.1.val := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have := r.lane ⟨k + i.val + 1, by omega⟩
  rcases hd with rfl | rfl <;> exact this

private theorem vertical_column_card (r : Slide d s n k) (hd : d = .north ∨ d = .south) (P : ℕ) :
    (line .south P r.boxes).card = (line .south P s.boxes).card := by
  have hb : (line .south P r.before).card = (line .south P r.after).card := by
    by_cases hx : s.player.1.val = P
    · rw [line_card, line_card]
      have hf : r.before.filter (fun p => Direction.south.lane p = P) = r.before :=
        Finset.filter_eq_self.mpr (fun p hp => (r.vertical_before_lane hd hp).trans hx)
      have hg : r.after.filter (fun p => Direction.south.lane p = P) = r.after :=
        Finset.filter_eq_self.mpr (fun p hp => (r.vertical_after_lane hd hp).trans hx)
      rw [hf, hg, r.card_before, r.card_after]
    · have hf : line .south P r.before = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨p, hp, hl, _⟩ := mem_line.mp hz
        exact hx ((r.vertical_before_lane hd hp).symm.trans hl)
      have hg : line .south P r.after = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨p, hp, hl, _⟩ := mem_line.mp hz
        exact hx ((r.vertical_after_lane hd hp).symm.trans hl)
      rw [hf, hg]
  have hsub := line_mono .south P r.before_subset
  have hdis := line_disjoint .south P r.after_disjoint
  rw [Slide.boxes, line_union, Finset.card_union_of_disjoint hdis, line_sdiff,
    Finset.card_sdiff_of_subset hsub, hb]
  have hle := Finset.card_le_card hsub
  omega

end Slide

/-- Along any interior move the extremal column's box inventory is nonincreasing. -/
theorem Move.rack_card_le (hm : Move d s t) {P : ℕ} (hs : Supported .east P s)
    (ht : Interior t) : (line .south P t.boxes).card ≤ (line .south P s.boxes).card := by
  cases hm with
  | walk _ _ _ hb => rw [hb]
  | push _ hn hk r _ hb =>
    have hti : ∀ p ∈ r.boxes, ¬ Boundary p := by simpa only [Interior, hb] using ht
    rw [hb]
    by_cases hd : d = .north ∨ d = .south
    · exact (r.vertical_column_card hd P).le
    · have hh : d = .east ∨ d = .west := by cases d <;> simp_all
      rw [r.horizontal_column hn hk hh hs hti]
      exact Finset.card_le_card (Finset.sdiff_subset)

theorem Reachable.rack_card_le (hr : Reachable s t) {P : ℕ} (hs : Supported .east P s)
    (ht : Interior t) : (line .south P t.boxes).card ≤ (line .south P s.boxes).card := by
  induction hr with
  | refl => exact le_rfl
  | tail hr hm ih =>
    have hi := hm.choose_spec.interior_source ht
    exact (hm.choose_spec.rack_card_le (Reachable.supported hr hi hs) ht).trans (ih hi)

end PushPuzzle.PushPush
