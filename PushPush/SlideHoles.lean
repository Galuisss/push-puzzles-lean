/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.UnitExpansion

/-! Maximum sliding consumes a whole hole component ahead of a sufficiently long train. -/

@[expose] public section
namespace PushPuzzle.PushPush.Slide

open PushFS (Cell Direction Adjacent State)

variable {w h n k : ℕ} {d : Direction} {s : State w h}

/-- Every box on another row or column keeps its original occupancy. -/
theorem off_lane_boxes (r : Slide d s n k) {p : Cell w h}
    (hp : d.lane p ≠ d.lane s.player) : p ∈ r.boxes ↔ p ∈ s.boxes := by
  have hb : p ∉ r.before := by
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    exact hp (he ▸ r.lane _)
  have ha : p ∉ r.after := by
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    exact hp (he ▸ r.lane _)
  simp only [boxes, Finset.mem_union, Finset.mem_sdiff, hb, ha, not_false_eq_true, and_true, or_false]

/-- A moved box's forward neighbour is occupied after a maximum slide. -/
theorem after_forward_full (r : Slide d s n k) {p q : Cell w h} (hp : p ∈ r.after)
    (ha : PushFS.Adjacent d p q) : q ∈ r.boxes := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  by_cases hi : i.val + 1 < n
  · have he : r.cell ⟨k + i.val + 2, by omega⟩ = q :=
      (r.adjacent ⟨k + i.val + 1, by omega⟩).functional ha
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨i.val + 1, hi⟩, Finset.mem_univ _, he⟩
  · have he : (⟨k + i.val + 1, by omega⟩ : Fin (n + k + 1)) =
        ⟨n + k, by omega⟩ := Fin.ext (by change k + i.val + 1 = n + k; omega)
    have hs := r.stopped q (he ▸ ha)
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨hs, ?_⟩
    intro hbefore
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hbefore
    have hp := ha.position
    have h1 := r.position ⟨k + i.val + 1, by omega⟩
    have h2 := r.position ⟨j.val + 1, by omega⟩
    rw [hj] at h2
    dsimp only at h1 h2
    omega

/-- The maximal clear interval immediately ahead of the original box run. -/
def gap (r : Slide d s n k) : Finset (Cell w h) :=
  Finset.univ.image fun i : Fin k => r.cell ⟨n + i.val + 1, by omega⟩

/-- The trailing cells vacated by the translated run. -/
def trail (r : Slide d s n k) : Finset (Cell w h) :=
  Finset.univ.image fun i : Fin k => r.cell ⟨i.val + 1, by omega⟩

theorem gap_empty (r : Slide d s n k) : r.gap ⊆ s.boxesᶜ := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_compl.mpr (r.clear i)

theorem gap_card (r : Slide d s n k) : r.gap.card = k := by
  rw [gap, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ he
    have he := congrArg Fin.val (r.injective he)
    change n + i.val + 1 = n + j.val + 1 at he
    apply Fin.ext
    omega

private theorem mem_gap (r : Slide d s n k) (i : Fin (n + k + 1)) :
    r.cell i ∈ r.gap ↔ n < i.val := by
  constructor
  · intro hp
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
    have he := congrArg Fin.val (r.injective he)
    change n + j.val + 1 = i.val at he
    omega
  · intro hi
    refine Finset.mem_image.mpr ⟨⟨i.val - n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    apply Fin.ext
    change n + (i.val - n - 1) + 1 = i.val
    omega

private theorem mem_trail (r : Slide d s n k) (i : Fin (n + k + 1)) :
    r.cell i ∈ r.trail ↔ 0 < i.val ∧ i.val ≤ k := by
  constructor
  · intro hp
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
    have he := congrArg Fin.val (r.injective he)
    change j.val + 1 = i.val at he
    constructor <;> omega
  · intro hi
    refine Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega

/-- Every adjacent original hole belongs to the same complete gap. -/
theorem gap_closed (r : Slide d s n k) (hn : 0 < n) {p q : Cell w h}
    (hp : p ∈ r.gap) (hq : q ∉ s.boxes)
    (ha : Adjacent d p q ∨ Adjacent d.opposite p q) : q ∈ r.gap := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  rcases ha with ha | ha
  · by_cases hi : i.val + 1 < k
    · have he : r.cell ⟨n + i.val + 2, by omega⟩ = q :=
        (r.adjacent ⟨n + i.val + 1, by omega⟩).functional ha
      rw [← he]
      exact (r.mem_gap _).mpr (by change n < n + i.val + 2; omega)
    · have he : (⟨n + i.val + 1, by omega⟩ : Fin (n + k + 1)) =
          ⟨n + k, by omega⟩ := Fin.ext (by change n + i.val + 1 = n + k; omega)
      exact False.elim (hq (r.stopped q (he ▸ ha)))
  · have he : r.cell ⟨n + i.val, by omega⟩ = q :=
      (r.adjacent ⟨n + i.val, by omega⟩).reverse.functional ha
    by_cases hi : 0 < i.val
    · rw [← he]
      exact (r.mem_gap _).mpr (by change n < n + i.val; omega)
    · have hi : i.val = 0 := by omega
      have heq : (⟨n + i.val, by omega⟩ : Fin (n + k + 1)) =
          ⟨(n - 1) + 1, by omega⟩ := Fin.ext (by change n + i.val = n - 1 + 1; omega)
      exact False.elim (hq (he ▸ heq ▸ r.occupied ⟨n - 1, by omega⟩))

/-- A long train replaces the entire gap by the same number of trailing holes. -/
theorem holes_eq (r : Slide d s n k) (hv : s.player ∉ s.boxes) (hkn : k ≤ n) :
    r.boxesᶜ = (s.boxesᶜ \ r.gap) ∪ r.trail := by
  ext p
  by_cases hp : ∃ i, r.cell i = p
  · obtain ⟨i, rfl⟩ := hp
    have hbox : r.cell i ∈ r.boxes ↔ k < i.val ∧ i.val ≤ k + n :=
      r.mem_stageBoxes hv (Fin.last k) i
    have hsource : r.cell i ∈ s.boxes ↔ 0 < i.val ∧ i.val ≤ n := by
      have hm := r.mem_stageBoxes hv 0 i
      have hs := congrArg State.boxes r.stage_zero
      change r.stageBoxes 0 = s.boxes at hs
      rw [hs] at hm
      simpa only [Fin.val_zero, Nat.zero_add] using hm
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff,
      r.mem_gap, r.mem_trail, hbox, hsource]
    omega
  · have hb : p ∉ r.before := by
      intro hm
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
      exact hp ⟨_, he⟩
    have ha : p ∉ r.after := by
      intro hm
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
      exact hp ⟨_, he⟩
    have hg : p ∉ r.gap := by
      intro hm
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
      exact hp ⟨_, he⟩
    have ht : p ∉ r.trail := by
      intro hm
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
      exact hp ⟨_, he⟩
    simp [boxes, hb, ha, hg, ht]

/-- Restricting to data cells removes the whole gap when the new trailing holes lie outside. -/
theorem source_holes (r : Slide d s n k) (hv : s.player ∉ s.boxes) (hkn : k ≤ n)
    (R : Finset (Cell w h)) (hout : Disjoint r.trail R) :
    r.boxesᶜ ∩ R = (s.boxesᶜ ∩ R) \ r.gap := by
  rw [r.holes_eq hv hkn]
  ext p
  have hd := Finset.disjoint_left.mp hout
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp | hp, hR⟩
    · exact ⟨⟨hp.1, hR⟩, hp.2⟩
    · exact False.elim (hd hp hR)
  · rintro ⟨⟨hp, hR⟩, hg⟩
    exact ⟨Or.inl ⟨hp, hg⟩, hR⟩

end PushPuzzle.PushPush.Slide
