/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Room
public import PushPush.Finite

/-! Straight single-box maximum slides with arbitrary surrounding boxes. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors

open PushFS (Cell State Direction Adjacent)

variable {w h : ℕ}

/-- The first ray cell is adjacent to the actual initial player. -/
theorem slide_first_adjacent {d : Direction} {s : State w h} {n k : ℕ}
    (r : Slide d s n k) (hpositive : 0 < n + k) :
    Adjacent d s.player (r.cell ⟨1, by omega⟩) := by
  have ha := r.adjacent ⟨0, hpositive⟩
  have hz : (⟨0, hpositive⟩ : Fin (n + k)).castSucc = 0 := by
    apply Fin.ext
    simp
  rw [hz, r.start] at ha
  exact ha

/-- A box cannot be pushed from a support cell already occupied by another box. -/
theorem blocked_support {d : Direction} {s : State w h} {n k : ℕ}
    (r : Slide d s n k) (hpositive : 0 < n + k) (support : Cell w h)
    (hsupport : Adjacent d.opposite (r.cell ⟨1, by omega⟩) support)
    (hbox : support ∈ s.boxes) : s.player ∈ s.boxes := by
  have ha := (slide_first_adjacent r hpositive).reverse
  have he := ha.functional hsupport
  exact he ▸ hbox

/-- A directed interval whose endpoints lie in a rectangle stays in that rectangle. -/
theorem straight_ray (d : Direction) (a b : Cell w h) (length : ℕ)
    (hlane : d.lane b = d.lane a)
    (hpos : d.position b = d.position a + length) :
    ∃ cell : Fin (length + 1) → Cell w h,
      cell 0 = a ∧ cell (Fin.last length) = b ∧
      ∀ i : Fin length, Adjacent d (cell i.castSucc) (cell i.succ) := by
  cases d
  · simp only [Direction.lane, Direction.position] at hlane hpos
    let cell : Fin (length + 1) → Cell w h := fun i =>
      (a.1, ⟨a.2.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) a.2.isLt⟩)
    refine ⟨cell, ?_, ?_, ?_⟩
    · apply Prod.ext <;> apply Fin.ext <;> simp [cell]
    · apply Prod.ext <;> apply Fin.ext <;> dsimp [cell] <;> omega
    · intro i
      constructor
      · rfl

      · dsimp [cell]
        have := i.isLt
        omega
  · simp only [Direction.lane, Direction.position] at hlane hpos
    let cell : Fin (length + 1) → Cell w h := fun i =>
      (⟨a.1.val + i.val, by have := i.isLt; have := b.1.isLt; omega⟩, a.2)
    refine ⟨cell, ?_, ?_, ?_⟩
    · apply Prod.ext <;> apply Fin.ext <;> simp [cell]
    · apply Prod.ext <;> apply Fin.ext <;> dsimp [cell] <;> omega
    · intro i
      exact ⟨by dsimp [cell]; omega, rfl⟩
  · simp only [Direction.lane, Direction.position] at hlane hpos
    let cell : Fin (length + 1) → Cell w h := fun i =>
      (a.1, ⟨a.2.val + i.val, by have := i.isLt; have := b.2.isLt; omega⟩)
    refine ⟨cell, ?_, ?_, ?_⟩
    · apply Prod.ext <;> apply Fin.ext <;> simp [cell]
    · apply Prod.ext <;> apply Fin.ext <;> dsimp [cell] <;> omega
    · intro i
      exact ⟨rfl, by dsimp [cell]; omega⟩
  · simp only [Direction.lane, Direction.position] at hlane hpos
    let cell : Fin (length + 1) → Cell w h := fun i =>
      (⟨a.1.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) a.1.isLt⟩, a.2)
    refine ⟨cell, ?_, ?_, ?_⟩
    · apply Prod.ext <;> apply Fin.ext <;> simp [cell]
    · apply Prod.ext <;> apply Fin.ext <;> dsimp [cell] <;> omega
    · intro i
      constructor
      · dsimp [cell]
        have := i.isLt
        omega
      · rfl

/-- Every specified finite path of empty adjacent cells is an actual player walk. -/
private theorem walk_fin_path_single (boxes : Finset (Cell w h)) {n : ℕ}
    (positions : Fin (n + 1) → Cell w h) (hfree : ∀ i, positions i ∉ boxes)
    (hadj : ∀ i : Fin n, ∃ d, Adjacent d (positions i.castSucc) (positions i.succ)) :
    ∀ i, Finite.Reachable 1 ⟨positions 0, boxes⟩ ⟨positions i, boxes⟩ := by
  intro i
  induction i using Fin.induction with
  | zero => exact .refl
  | succ i ih =>
    obtain ⟨d, hd⟩ := hadj i
    exact ih.tail ⟨d, Finite.Move.walk (hfree _) hd (hfree _) rfl⟩

/-- Walk an empty straight interval in either of the four directed orientations. -/
theorem straight_walk_single (boxes : Finset (Cell w h)) (d : Direction) (a b : Cell w h)
    (hlane : d.lane b = d.lane a) (hforward : d.position a ≤ d.position b)
    (hfree : ∀ p : Cell w h, d.lane p = d.lane a →
      d.position a ≤ d.position p → d.position p ≤ d.position b → p ∉ boxes) :
    Finite.Reachable 1 ⟨a, boxes⟩ ⟨b, boxes⟩ := by
  let length := (d.position b - d.position a).toNat
  have hlength : d.position b = d.position a + length := by dsimp [length]; omega
  obtain ⟨cell, hstart, hend, hadj⟩ := straight_ray d a b length hlane hlength
  have hp (i : Fin (length + 1)) : d.position (cell i) = d.position a + i.val := by
    induction i using Fin.induction with
    | zero => simp only [hstart, Fin.val_zero, Int.natCast_zero, Int.add_zero]
    | succ i ih =>
      have hi := (hadj i).position
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega
  have hl (i : Fin (length + 1)) : d.lane (cell i) = d.lane a := by
    induction i using Fin.induction with
    | zero => rw [hstart]
    | succ i ih => exact (hadj i).lane.trans ih
  have hr := walk_fin_path_single boxes cell (fun i =>
    hfree _ (hl i) (by have := hp i; omega) (by have := hp i; have := i.isLt; omega))
    (fun i => ⟨d, hadj i⟩) (Fin.last length)
  simpa only [hstart, hend] using hr

/-- One isolated box slides to the cell immediately before its stopping box.
Every other box in the board is retained. -/
theorem push_single_finite (d : Direction) (s : State w h) (source dest stop : Cell w h)
    (hvalid : s.player ∉ s.boxes) (hsource : source ∈ s.boxes)
    (hfirst : Adjacent d s.player source) (hlane : d.lane dest = d.lane source)
    (hforward : d.position source < d.position dest)
    (hclear : ∀ p : Cell w h, d.lane p = d.lane source →
      d.position source < d.position p → d.position p ≤ d.position dest → p ∉ s.boxes)
    (hstop : Adjacent d dest stop) (hoccupied : stop ∈ s.boxes) :
    Finite.Move 1 d s ⟨source, insert dest (s.boxes.erase source)⟩ := by
  let k := (d.position dest - d.position source).toNat
  have hk : 0 < k := by dsimp [k]; omega
  have hlength : d.position dest = d.position s.player + (1 + k : ℕ) := by
    have hp := hfirst.position
    dsimp [k]
    omega
  obtain ⟨cell, hstart, hend, hadj⟩ := straight_ray d s.player dest (1 + k)
    (hlane.trans hfirst.lane) hlength
  have hp (j : Fin (1 + k + 1)) :
      d.position (cell j) = d.position s.player + j.val := by
    induction j using Fin.induction with
    | zero => simp only [hstart, Fin.val_zero, Int.natCast_zero, Int.add_zero]
    | succ j ih =>
      have hj := (hadj j).position
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega
  have hl (j : Fin (1 + k + 1)) : d.lane (cell j) = d.lane s.player := by
    induction j using Fin.induction with
    | zero => rw [hstart]
    | succ j ih => exact (hadj j).lane.trans ih
  have hcell1 : cell ⟨1, by omega⟩ = source := by
    apply d.cell_ext ((hl _).trans hfirst.lane.symm)
    have hp := hp ⟨1, by omega⟩
    have hf := hfirst.position
    change d.position (cell ⟨1, by omega⟩) = d.position s.player + (1 : ℕ) at hp
    omega
  let r : Slide d s 1 k := {
    cell := cell
    start := hstart
    adjacent := hadj
    occupied := by
      intro i
      have hi : i.val = 0 := by have := i.isLt; omega
      have hc : cell ⟨i.val + 1, by omega⟩ = source := by
        have he : (⟨i.val + 1, by omega⟩ : Fin (1 + k + 1)) = ⟨1, by omega⟩ :=
          Fin.ext (by change i.val + 1 = 1; omega)
        rw [he, hcell1]
      exact hc ▸ hsource
    clear := by
      intro i
      apply hclear
      · exact (hl _).trans hfirst.lane.symm
      · have hp := hp ⟨1 + i.val + 1, by omega⟩
        have hfirst := hfirst.position
        change d.position (cell ⟨1 + i.val + 1, by omega⟩) =
          d.position s.player + (1 + i.val + 1 : ℕ) at hp
        omega
      · have hp := hp ⟨1 + i.val + 1, by omega⟩
        change d.position (cell ⟨1 + i.val + 1, by omega⟩) =
          d.position s.player + (1 + i.val + 1 : ℕ) at hp
        have := i.isLt
        omega
    stopped := by
      intro q hq
      have he : (⟨1 + k, by omega⟩ : Fin (1 + k + 1)) = Fin.last (1 + k) := rfl
      rw [he, hend] at hq
      exact hq.functional hstop ▸ hoccupied
  }
  have hr1 : r.cell ⟨1, by omega⟩ = source := hcell1
  have hbefore : r.before = {source} := by
    ext p
    simp [Slide.before, hr1]
  have hafter : r.after = {dest} := by
    have he : (⟨k + 1, by omega⟩ : Fin (1 + k + 1)) = Fin.last (1 + k) :=
      Fin.ext (by dsimp; omega)
    ext p
    simp [Slide.after, r, he, hend]
  apply Finite.Move.push hvalid (by omega) (by omega) hk r hr1.symm
  simp only [Slide.boxes, hbefore, hafter, Finset.union_singleton]
  congr 1
  ext p
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
  exact and_comm

/-- The first occupied cell after a run determines its full maximum-slide distance. -/
theorem slide_distance_eq {d : Direction} {s : State w h} {n k : ℕ}
    (r : Slide d s n k) (stop : Cell w h) (distance : ℕ)
    (hlane : d.lane stop = d.lane s.player)
    (hpos : d.position stop = d.position s.player + (n + distance + 1 : ℕ))
    (hoccupied : stop ∈ s.boxes)
    (hclear : ∀ p : Cell w h, d.lane p = d.lane s.player →
      d.position s.player + n < d.position p → d.position p < d.position stop →
      p ∉ s.boxes) : k = distance := by
  have hle : k ≤ distance := by
    by_contra hn
    have hi : distance < k := by omega
    have he : r.cell ⟨n + distance + 1, by omega⟩ = stop := by
      apply d.cell_ext ((r.lane _).trans hlane.symm)
      have hp := r.position ⟨n + distance + 1, by omega⟩
      change d.position (r.cell ⟨n + distance + 1, by omega⟩) =
        d.position s.player + (n + distance + 1 : ℕ) at hp
      omega
    exact r.clear ⟨distance, hi⟩ (he ▸ hoccupied)
  by_contra hne
  have hlt : k < distance := by omega
  obtain ⟨ray, hstart, _, hadj⟩ := straight_ray d s.player stop (n + distance + 1) hlane hpos
  have hp (i : Fin (n + distance + 1 + 1)) :
      d.position (ray i) = d.position s.player + i.val := by
    induction i using Fin.induction with
    | zero => simp only [hstart, Fin.val_zero, Int.natCast_zero, Int.add_zero]
    | succ i ih =>
      have hi := (hadj i).position
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega
  have hl (i : Fin (n + distance + 1 + 1)) : d.lane (ray i) = d.lane s.player := by
    induction i using Fin.induction with
    | zero => rw [hstart]
    | succ i ih => exact (hadj i).lane.trans ih
  let q := ray ⟨n + k + 1, by omega⟩
  have hqpos : d.position q = d.position s.player + (n + k + 1 : ℕ) := hp _
  have hrpos := r.position ⟨n + k, by omega⟩
  change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hrpos
  have hq : Adjacent d (r.cell ⟨n + k, by omega⟩) q := by
    apply (PushFS.adjacent_iff_coordinates d _ _).mpr
    exact ⟨(hl _).trans (r.lane _).symm, by omega⟩
  exact hclear q (hl _) (by omega) (by omega) (r.stopped q hq)

/-- An isolated first box forces the complete initial run to have length one. -/
theorem slide_length_one {d : Direction} {s : State w h} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n)
    (hnext : ∀ q, Adjacent d (r.cell ⟨1, by omega⟩) q → q ∉ s.boxes) : n = 1 := by
  by_contra hne
  have ht : 1 < n := by omega
  have ha := r.adjacent ⟨1, by omega⟩
  have ho := r.occupied ⟨1, ht⟩
  change Adjacent d (r.cell ⟨1, by omega⟩) (r.cell ⟨2, by omega⟩) at ha
  exact hnext _ ha ho

/-- The exact unlabelled update of any single-box slide. -/
theorem single_slide_boxes {d : Direction} {s : State w h} {k : ℕ}
    (r : Slide d s 1 k) :
    r.boxes = insert (r.cell ⟨k + 1, by omega⟩) (s.boxes.erase (r.cell ⟨1, by omega⟩)) := by
  have hb : r.before = {r.cell ⟨1, by omega⟩} := by ext p; simp [Slide.before]
  have ha : r.after = {r.cell ⟨k + 1, by omega⟩} := by ext p; simp [Slide.after]
  simp only [Slide.boxes, hb, ha, Finset.union_singleton]
  congr 1
  ext p
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
  exact and_comm

/-- Two adjacent boxes followed by an empty cell form exactly the moving run. -/
theorem slide_length_two {d : Direction} {s : State w h} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (next : Cell w h)
    (hnext : Adjacent d (r.cell ⟨1, by omega⟩) next) (hbox : next ∈ s.boxes)
    (hthird : ∀ q, Adjacent d next q → q ∉ s.boxes) : n = 2 := by
  have hcell : r.cell ⟨2, by omega⟩ = next := by
    have ha := r.adjacent ⟨1, by omega⟩
    change Adjacent d (r.cell ⟨1, by omega⟩) (r.cell ⟨2, by omega⟩) at ha
    exact ha.functional hnext
  have hn1 : n ≠ 1 := by
    intro he
    subst n
    have hc := r.clear ⟨0, hk⟩
    change r.cell ⟨2, by omega⟩ ∉ s.boxes at hc
    exact hc (hcell ▸ hbox)
  by_contra hne
  have hn3 : 2 < n := by omega
  have ha := r.adjacent ⟨2, by omega⟩
  change Adjacent d (r.cell ⟨2, by omega⟩) (r.cell ⟨3, by omega⟩) at ha
  rw [hcell] at ha
  exact hthird _ ha (r.occupied ⟨2, hn3⟩)

end PushPuzzle.PushPush.Doors
