/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.SlideHoles
public import PushPush.Doors.RoomSlide
public import PushPush.ReadPath
import Mathlib.Data.Finset.Max

/-! Maximal source-hole runs for the committed column reader. -/

@[expose] public section
namespace PushPuzzle.PushPush.Reader

open PushFS (Cell State Direction Adjacent)

variable {w h : ℕ}

/-- Data holes above the reader, in its current column. -/
def northData (s : State w h) (cutoff : ℕ) : Finset (Cell w h) :=
  s.boxesᶜ.filter fun q => q.1 = s.player.1 ∧ q.2.val < cutoff

/-- The last source-hole run encountered while moving north. -/
structure NorthRun (s : State w h) (cutoff : ℕ) where
  /-- First cell of the run in northward order. -/
  bottom : Cell w h
  /-- Last cell of the run in northward order. -/
  top : Cell w h
  /-- The run begins at the closest source hole. -/
  bottom_mem : bottom ∈ northData s cutoff
  /-- No source hole is closer to the player. -/
  nearest : ∀ q ∈ northData s cutoff, q.2.val ≤ bottom.2.val
  /-- Both ends lie in the same column. -/
  column : top.1 = bottom.1
  /-- The interval is nonempty. -/
  ordered : top.2.val ≤ bottom.2.val
  /-- Every cell of the interval is an original hole. -/
  clear : ∀ q : Cell w h, q.1 = bottom.1 → top.2.val ≤ q.2.val →
    q.2.val ≤ bottom.2.val → q ∉ s.boxes
  /-- The next cell is a box or lies outside the true boundary. -/
  stopped : ∀ q : Cell w h, Adjacent .north top q → q ∈ s.boxes

private def candidates (s : State w h) (b : Cell w h) : Finset (Cell w h) :=
  Finset.univ.filter fun a => a.1 = b.1 ∧ a.2.val ≤ b.2.val ∧
    ∀ q : Cell w h, q.1 = b.1 → a.2.val ≤ q.2.val → q.2.val ≤ b.2.val → q ∉ s.boxes

/-- Every nonempty source column has its nearest complete hole run. -/
theorem exists_northRun (s : State w h) (cutoff : ℕ)
    (hne : (northData s cutoff).Nonempty) : Nonempty (NorthRun s cutoff) := by
  obtain ⟨b, hb, hmax⟩ := (northData s cutoff).exists_max_image (fun q => q.2.val) hne
  have hbm := Finset.mem_filter.mp hb
  have hbfree := Finset.mem_compl.mp hbm.1
  have hbc : b ∈ candidates s b := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, rfl, le_rfl, ?_⟩
    intro q hx hlo hhi
    have he : q = b := Prod.ext hx (Fin.ext (by omega))
    exact he ▸ hbfree
  obtain ⟨a, ha, hmin⟩ := (candidates s b).exists_min_image (fun q => q.2.val) ⟨b, hbc⟩
  obtain ⟨_, hcol, hle, hclear⟩ := Finset.mem_filter.mp ha
  refine ⟨⟨b, a, hb, hmax, hcol, hle, hclear, ?_⟩⟩
  intro q hq
  by_contra hbox
  have hx : q.1 = b.1 := hq.1.trans hcol
  have hy : q.2.val + 1 = a.2.val := hq.2
  have hqc : q ∈ candidates s b := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hx, by omega, ?_⟩
    intro p hpx hlo hhi
    by_cases hpa : a.2.val ≤ p.2.val
    · exact hclear p hpx hpa hhi
    · have he : p = q := Prod.ext (hpx.trans hx.symm) (Fin.ext (by omega))
      exact he ▸ hbox
  have := hmin q hqc
  omega

namespace NorthRun

/-- The length of the solid train between player and the first source hole. -/
def train {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff) : ℕ :=
  s.player.2.val - R.bottom.2.val - 1

/-- Number of consecutive source holes consumed by one maximum slide. -/
def length {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff) : ℕ :=
  R.bottom.2.val - R.top.2.val + 1

theorem train_pos {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val) : 0 < R.train := by
  have hcount : 0 < (northData s cutoff).card := Finset.card_pos.mpr ⟨R.bottom, R.bottom_mem⟩
  have hb := (Finset.mem_filter.mp R.bottom_mem).2.2
  dsimp [train]
  omega

theorem length_pos {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff) : 0 < R.length := by
  dsimp [length]
  omega

/-- The complete train slides across precisely the closest source-hole run. -/
noncomputable def toSlide {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) : Slide .north s R.train R.length := by
  classical
  apply Classical.choice
  have hb := (Finset.mem_filter.mp R.bottom_mem).2
  have hn := R.train_pos hspace
  have hk := R.length_pos
  have hnval : R.train = s.player.2.val - R.bottom.2.val - 1 := rfl
  have hkval : R.length = R.bottom.2.val - R.top.2.val + 1 := rfl
  have hpos : Direction.north.position R.top =
      Direction.north.position s.player + (R.train + R.length : ℕ) := by
    simp only [Direction.position]
    dsimp [train, length]
    have := R.ordered
    omega
  obtain ⟨cell, hstart, hend, hadj⟩ := Doors.straight_ray .north s.player R.top
    (R.train + R.length) (congrArg Fin.val (R.column.trans hb.1)) hpos
  have hp (i : Fin (R.train + R.length + 1)) :
      (cell i).2.val + i.val = s.player.2.val := by
    induction i using Fin.induction with
    | zero => simp only [hstart, Fin.val_zero, Nat.add_zero]
    | succ i ih =>
      have := (hadj i).2
      change (cell i.succ).2.val + 1 = (cell i.castSucc).2.val at this
      change (cell i.castSucc).2.val + i.val = s.player.2.val at ih
      change (cell i.succ).2.val + (i.val + 1) = s.player.2.val
      omega
  have hx (i : Fin (R.train + R.length + 1)) : (cell i).1 = s.player.1 := by
    induction i using Fin.induction with
    | zero => rw [hstart]
    | succ i ih => exact (hadj i).1.trans ih
  refine ⟨⟨cell, hstart, hadj, ?_, ?_, ?_⟩⟩
  · intro i
    have hp := hp ⟨i.val + 1, by omega⟩
    change (cell ⟨i.val + 1, by omega⟩).2.val + (i.val + 1) = s.player.2.val at hp
    by_cases hc : cutoff ≤ (cell ⟨i.val + 1, by omega⟩).2.val
    · exact hgap _ (hx _) hc (by omega)
    · by_contra hnot
      have hmem : cell ⟨i.val + 1, by omega⟩ ∈ northData s cutoff :=
        Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hnot, hx _, by omega⟩
      have := R.nearest _ hmem
      have hi := i.isLt
      omega
  · intro i
    have hp := hp ⟨R.train + i.val + 1, by omega⟩
    change (cell ⟨R.train + i.val + 1, by omega⟩).2.val +
      (R.train + i.val + 1) = s.player.2.val at hp
    have hi := i.isLt
    have := R.ordered
    exact R.clear _ ((hx _).trans hb.1.symm) (by omega) (by omega)
  · intro q hq
    change Adjacent .north (cell (Fin.last (R.train + R.length))) q at hq
    rw [hend] at hq
    exact R.stopped q hq

theorem gap_subset {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    (R.toSlide hspace hgap).gap ⊆ northData s cutoff := by
  let r := R.toSlide hspace hgap
  intro p hp
  have hfree := r.gap_empty hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hy := r.position ⟨R.train + i.val + 1, by omega⟩
  have hx := r.lane ⟨R.train + i.val + 1, by omega⟩
  simp only [Direction.position, Direction.lane] at hy hx
  change -((r.cell ⟨R.train + i.val + 1, by omega⟩).2.val : ℤ) =
    -(s.player.2.val : ℤ) + (R.train + i.val + 1 : ℕ) at hy
  have hb := (Finset.mem_filter.mp R.bottom_mem).2
  have hn := R.train_pos hspace
  have hnval : R.train = s.player.2.val - R.bottom.2.val - 1 := rfl
  dsimp only [r] at hy
  exact Finset.mem_filter.mpr ⟨hfree, Fin.ext hx, by omega⟩

/-- Guard space makes the train at least as long as every source-hole run. -/
theorem length_le_train {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) : R.length ≤ R.train := by
  have hc := Finset.card_le_card (R.gap_subset hspace hgap)
  rw [Slide.gap_card] at hc
  have hb := (Finset.mem_filter.mp R.bottom_mem).2.2
  dsimp [train]
  omega

/-- The source strip in the reader's current column. -/
def region {s : State w h} {cutoff : ℕ} (_R : NorthRun s cutoff) : Finset (Cell w h) :=
  Finset.univ.filter fun q => q.1 = s.player.1 ∧ q.2.val < cutoff

private theorem data_eq_region {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff) :
    northData s cutoff = s.boxesᶜ ∩ R.region := by
  ext q
  simp only [northData, region, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]

private theorem trail_outside {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    Disjoint (R.toSlide hspace hgap).trail R.region := by
  apply Finset.disjoint_left.mpr
  intro p hp hR
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hy := (R.toSlide hspace hgap).position ⟨i.val + 1, by omega⟩
  change -(((R.toSlide hspace hgap).cell ⟨i.val + 1, by omega⟩).2.val : ℤ) =
    -(s.player.2.val : ℤ) + (i.val + 1 : ℕ) at hy
  have hc := Finset.card_le_card (R.gap_subset hspace hgap)
  rw [Slide.gap_card] at hc
  have hlo := (Finset.mem_filter.mp hR).2.2
  omega

/-- One read block ends after walking across its newly vacated corridor. -/
noncomputable def target {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) : State w h :=
  (R.toSlide hspace hgap).returnState (Fin.last R.length)

theorem target_reachable {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (hv : s.player ∉ s.boxes) :
    Reachable s (R.target hspace hgap) :=
  (R.toSlide hspace hgap).advance_reachable (R.train_pos hspace) R.length_pos hv
    (Fin.last R.length) R.length_pos

theorem target_readPath {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (hv : s.player ∉ s.boxes) :
    ReadPath s (R.target hspace hgap) :=
  (R.toSlide hspace hgap).advance_readPath (R.train_pos hspace) R.length_pos hv
    (Fin.last R.length) R.length_pos

theorem target_column {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    (R.target hspace hgap).player.1 = s.player.1 := by
  apply Fin.ext
  exact (R.toSlide hspace hgap).lane ⟨R.length, by omega⟩

theorem target_off_column {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) {p : Cell w h} (hp : p.1 ≠ s.player.1) :
    p ∈ (R.target hspace hgap).boxes ↔ p ∈ s.boxes :=
  (R.toSlide hspace hgap).off_lane_boxes (by
    intro he
    exact hp (Fin.ext he))

theorem target_row {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    (R.target hspace hgap).player.2.val + R.length = s.player.2.val := by
  have hp := (R.toSlide hspace hgap).position ⟨R.length, by omega⟩
  change -(((R.target hspace hgap).player).2.val : ℤ) =
    -(s.player.2.val : ℤ) + (R.length : ℕ) at hp
  omega

/-- The read block removes exactly one entire maximal source-hole run. -/
theorem target_data {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (hv : s.player ∉ s.boxes) :
    northData (R.target hspace hgap) cutoff =
      northData s cutoff \ (R.toSlide hspace hgap).gap := by
  have he := (R.toSlide hspace hgap).source_holes hv (R.length_le_train hspace hgap)
    R.region (R.trail_outside hspace hgap)
  rw [R.data_eq_region]
  rw [← he]
  ext q
  simp only [northData, Finset.mem_filter, Finset.mem_inter, region, Finset.mem_univ,
    true_and, R.target_column]
  rfl

theorem target_data_card {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (hv : s.player ∉ s.boxes) :
    (northData (R.target hspace hgap) cutoff).card + R.length = (northData s cutoff).card := by
  rw [R.target_data hspace hgap hv]
  have hc := Finset.card_sdiff_add_card_eq_card (R.gap_subset hspace hgap)
  rw [Slide.gap_card] at hc
  exact hc

theorem target_gap {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (hv : s.player ∉ s.boxes) :
    ∀ q : Cell w h, q.1 = (R.target hspace hgap).player.1 → cutoff ≤ q.2.val →
      q.2.val < (R.target hspace hgap).player.2.val → q ∈ (R.target hspace hgap).boxes := by
  intro q hx hlo hhi
  have hx : q.1 = s.player.1 := hx.trans (R.target_column hspace hgap)
  have hy := R.target_row hspace hgap
  have hold := hgap q hx hlo (by omega)
  by_contra hn
  have hnew : q ∈ (R.toSlide hspace hgap).boxesᶜ := Finset.mem_compl.mpr hn
  rw [(R.toSlide hspace hgap).holes_eq hv (R.length_le_train hspace hgap)] at hnew
  rcases Finset.mem_union.mp hnew with hnew | hnew
  · exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hnew).1 hold
  · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hnew
    have hp := (R.toSlide hspace hgap).position ⟨i.val + 1, by omega⟩
    change -(((R.toSlide hspace hgap).cell ⟨i.val + 1, by omega⟩).2.val : ℤ) =
      -(s.player.2.val : ℤ) + (i.val + 1 : ℕ) at hp
    rw [he] at hp
    omega

theorem gap_bottom {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    (R.toSlide hspace hgap).cell ⟨R.train + 1, by have := R.length_pos; omega⟩ = R.bottom := by
  apply Prod.ext
  · apply Fin.ext
    exact ((R.toSlide hspace hgap).lane _).trans
      (congrArg Fin.val (Finset.mem_filter.mp R.bottom_mem).2.1.symm)
  · apply Fin.ext
    have hp := (R.toSlide hspace hgap).position ⟨R.train + 1, by have := R.length_pos; omega⟩
    change -(((R.toSlide hspace hgap).cell ⟨R.train + 1, by have := R.length_pos; omega⟩).2.val : ℤ) =
      -(s.player.2.val : ℤ) + (R.train + 1 : ℕ) at hp
    have hn : R.train = s.player.2.val - R.bottom.2.val - 1 := rfl
    have hb := (Finset.mem_filter.mp R.bottom_mem).2.2
    omega

theorem mem_gap {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (p : Cell w h) :
    p ∈ (R.toSlide hspace hgap).gap ↔
      p.1 = s.player.1 ∧ R.top.2.val ≤ p.2.val ∧ p.2.val ≤ R.bottom.2.val := by
  have hnval : R.train = s.player.2.val - R.bottom.2.val - 1 := rfl
  have hkval : R.length = R.bottom.2.val - R.top.2.val + 1 := rfl
  have hb := (Finset.mem_filter.mp R.bottom_mem).2.2
  have hordered := R.ordered
  constructor
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hx := (R.toSlide hspace hgap).lane ⟨R.train + i.val + 1, by omega⟩
    have hy := (R.toSlide hspace hgap).position ⟨R.train + i.val + 1, by omega⟩
    change -(((R.toSlide hspace hgap).cell ⟨R.train + i.val + 1, by omega⟩).2.val : ℤ) =
      -(s.player.2.val : ℤ) + (R.train + i.val + 1 : ℕ) at hy
    refine ⟨Fin.ext hx, ?_, ?_⟩ <;> omega
  · rintro ⟨hx, hlo, hhi⟩
    let i : Fin R.length := ⟨R.bottom.2.val - p.2.val, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    apply Direction.north.cell_ext
    · exact ((R.toSlide hspace hgap).lane _).trans (congrArg Fin.val hx.symm)
    · rw [Slide.position]
      change -(s.player.2.val : ℤ) + (R.train + i.val + 1 : ℕ) = -(p.2.val : ℤ)
      dsimp only [i]
      omega

end NorthRun

end PushPuzzle.PushPush.Reader
