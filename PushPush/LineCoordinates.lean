/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.LineMerge
public import PushPush.Support

/-! Exact one-dimensional coordinates for a sliding box run. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k : ℕ} {d : Direction} {s : State w h}

/-- Occupied signed coordinates on a fixed row or column. -/
def line (d : Direction) (lane : ℕ) (boxes : Finset (Cell w h)) : Finset ℤ :=
  (boxes.filter fun p => d.lane p = lane).image d.position

theorem line_card (d : Direction) (lane : ℕ) (boxes : Finset (Cell w h)) :
    (line d lane boxes).card = (boxes.filter fun p => d.lane p = lane).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  exact d.cell_ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he

private theorem line_opposite (d : Direction) (lane : ℕ) (boxes : Finset (Cell w h)) :
    line d.opposite lane boxes = (line d lane boxes).image (fun z => -z) := by
  have hl (p : Cell w h) : d.opposite.lane p = d.lane p := by cases d <;> rfl
  have hp (p : Cell w h) : d.opposite.position p = -d.position p := by
    cases d <;> simp [Direction.opposite, Direction.position]
  simp only [line, hl, Finset.image_image, Function.comp_def]
  congr 1
  funext p
  exact hp p

theorem line_starts_opposite_card (d : Direction) (lane : ℕ) (boxes : Finset (Cell w h)) :
    (Line.starts (line d.opposite lane boxes)).card = (Line.starts (line d lane boxes)).card := by
  rw [line_opposite, Line.starts_neg_card]

theorem mem_line {boxes : Finset (Cell w h)} {lane : ℕ} {z : ℤ} :
    z ∈ line d lane boxes ↔ ∃ p ∈ boxes, d.lane p = lane ∧ d.position p = z := by
  simp only [line, Finset.mem_image, Finset.mem_filter]
  aesop

theorem line_union (d : Direction) (lane : ℕ) (A B : Finset (Cell w h)) :
    line d lane (A ∪ B) = line d lane A ∪ line d lane B := by
  ext z
  simp only [mem_line, Finset.mem_union]
  aesop

theorem line_sdiff (d : Direction) (lane : ℕ) (A B : Finset (Cell w h)) :
    line d lane (A \ B) = line d lane A \ line d lane B := by
  ext z
  simp only [mem_line, Finset.mem_sdiff]
  constructor
  · rintro ⟨p, ⟨hp, hnot⟩, hl, hz⟩
    refine ⟨⟨p, hp, hl, hz⟩, ?_⟩
    rintro ⟨q, hq, hql, hqz⟩
    have he : p = q := d.cell_ext (hl.trans hql.symm) (hz.trans hqz.symm)
    exact hnot (he ▸ hq)
  · rintro ⟨⟨p, hp, hl, hz⟩, hnot⟩
    exact ⟨p, ⟨hp, fun hb => hnot ⟨p, hb, hl, hz⟩⟩, hl, hz⟩

private theorem Slide.line_before (r : Slide d s n k) :
    line d (d.lane s.player) r.before =
      Finset.Icc (d.position s.player + 1) (d.position s.player + n) := by
  ext z
  simp only [mem_line, Slide.before, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨p, ⟨i, _, rfl⟩, _, rfl⟩
    have := r.position ⟨i.val + 1, by omega⟩
    dsimp only at this
    constructor <;> omega
  · intro hz
    let i : Fin n := ⟨(z - d.position s.player - 1).toNat, by omega⟩
    refine ⟨r.cell ⟨i.val + 1, by omega⟩, ⟨i, Finset.mem_univ _, rfl⟩,
      r.lane _, ?_⟩
    rw [r.position]
    dsimp only [i]
    omega

private theorem Slide.line_after (r : Slide d s n k) :
    line d (d.lane s.player) r.after =
      Finset.Icc (d.position s.player + k + 1) (d.position s.player + n + k) := by
  ext z
  simp only [mem_line, Slide.after, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨p, ⟨i, _, rfl⟩, _, rfl⟩
    have := r.position ⟨k + i.val + 1, by omega⟩
    dsimp only at this
    constructor <;> omega
  · intro hz
    let i : Fin n := ⟨(z - d.position s.player - k - 1).toNat, by omega⟩
    refine ⟨r.cell ⟨k + i.val + 1, by omega⟩, ⟨i, Finset.mem_univ _, rfl⟩,
      r.lane _, ?_⟩
    rw [r.position]
    dsimp only [i]
    omega

/-- The actual unlabeled box update is precisely interval translation on its own line. -/
private theorem Slide.line_boxes (r : Slide d s n k) :
    line d (d.lane s.player) r.boxes =
      Line.slide (line d (d.lane s.player) s.boxes) (d.position s.player + 1) n k := by
  rw [Slide.boxes, line_union, line_sdiff, r.line_before, r.line_after]
  unfold Line.slide
  have h1 : d.position s.player + 1 + (n : ℤ) - 1 = d.position s.player + n := by omega
  have h2 : d.position s.player + 1 + (k : ℤ) = d.position s.player + k + 1 := by omega
  have h3 : d.position s.player + 1 + (n : ℤ) + k - 1 =
      d.position s.player + n + k := by omega
  rw [h1, h2, h3]

private theorem Slide.line_full (r : Slide d s n k) {z : ℤ}
    (hlo : d.position s.player + 1 ≤ z) (hhi : z < d.position s.player + 1 + n) :
    z ∈ line d (d.lane s.player) s.boxes := by
  have hz : z ∈ line d (d.lane s.player) r.before := by
    rw [r.line_before, Finset.mem_Icc]
    constructor <;> omega
  obtain ⟨p, hp, hl, hpos⟩ := mem_line.mp hz
  exact mem_line.mpr ⟨p, r.before_subset hp, hl, hpos⟩

private theorem Slide.line_clear (r : Slide d s n k) {z : ℤ}
    (hlo : d.position s.player + 1 + n ≤ z)
    (hhi : z < d.position s.player + 1 + n + k) :
    z ∉ line d (d.lane s.player) s.boxes := by
  rintro hz
  obtain ⟨p, hp, hl, hpos⟩ := mem_line.mp hz
  let i : Fin k := ⟨(z - d.position s.player - n - 1).toNat, by omega⟩
  have he : r.cell ⟨n + i.val + 1, by omega⟩ = p := by
    apply d.cell_ext ((r.lane _).trans hl.symm)
    rw [r.position]
    dsimp only [i]
    omega
  exact r.clear i (he ▸ hp)

/-- In a boundary-free successful prefix, a slide strictly decreases the line's components. -/
theorem Slide.line_starts_card (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (ht : ∀ p ∈ r.boxes, ¬ Boundary p) :
    (Line.starts (line d (d.lane s.player) r.boxes)).card + 1 =
      (Line.starts (line d (d.lane s.player) s.boxes)).card := by
  rw [r.line_boxes]
  apply Line.starts_slide_card _ (by omega) (by omega)
  · rintro hz
    obtain ⟨p, hp, hl, hpos⟩ := mem_line.mp hz
    have he : p = s.player := d.cell_ext hl (by omega)
    exact hv (he ▸ hp)
  · intro z hlo hhi
    exact r.line_full hlo hhi
  · intro z hlo hhi
    exact r.line_clear hlo hhi
  · obtain ⟨q, hq, ha⟩ := r.exists_stopper hn ht
    apply mem_line.mpr
    refine ⟨q, hq, ha.lane.trans (r.lane _), ?_⟩
    have := ha.position
    have := r.position ⟨n + k, by omega⟩
    dsimp only at this
    omega

end PushPuzzle.PushPush
