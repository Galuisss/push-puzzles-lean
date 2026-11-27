/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Tile

/-! Exact wall and physical-slot geometry of overlapping 40/59 wire tiles. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain


set_option maxRecDepth 4096
set_option maxHeartbeats 500000

abbrev blockCount (n : ℕ) := Spans.shortCount n + Spans.longCount n
abbrev Block (n : ℕ) := Fin (blockCount n)
abbrev C (n : ℕ) := Cell (n + 5) 21
abbrev offset := Spans.offset

def kind (n : ℕ) (i : Block n) : Bool := Spans.kindAt n i.val

theorem blockCount_pos (n : ℕ) (hn : 2301 ≤ n) : 0 < blockCount n := by
  have hh := Spans.exact_span n hn
  unfold blockCount
  omega

theorem offset_mono (n i j : ℕ) (hij : i ≤ j) : offset n i ≤ offset n j := by
  unfold offset Spans.offset
  split_ifs <;> omega

theorem offset_gap (n i j : ℕ) (hij : i ≤ j) : offset n i + 40 * (j - i) ≤ offset n j := by
  unfold offset Spans.offset
  split_ifs <;> omega

theorem offset_next (n i : ℕ) : offset n (i+1) = offset n i + Tile.span (Spans.kindAt n i) :=
  Spans.offset_next n i

theorem fit (n : ℕ) (hn : 2301 ≤ n) (i : Block n) : offset n i.val + Tile.width (kind n i) ≤ n + 5 := by
  have hnext := offset_next n i.val
  have hbound := Spans.offset_le n (i.val+1) hn (by change i.val+1 ≤ blockCount n; have := i.isLt; omega)
  change offset n (i.val+1) ≤ n at hbound
  rw [Tile.width_eq]
  change offset n i.val + (Tile.span (Spans.kindAt n i.val) + 5) ≤ n+5
  omega

def placement (n : ℕ) (hn : 2301 ≤ n) (i : Block n) : GridEmbedding (Tile.width (kind n i)) 21 (n+5) 21 :=
  GridEmbedding.translate (offset n i.val) 0 (fit n hn i) (by omega)

def embed (n : ℕ) (hn : 2301 ≤ n) (i : Block n) : Tile.C (kind n i) ↪ C n :=
  (placement n hn i).cells

@[simp] theorem embed_x (n : ℕ) (hn : 2301 ≤ n) (i : Block n) (p : Tile.C (kind n i)) :
    (embed n hn i p).1.val = offset n i.val + p.1.val := rfl
@[simp] theorem embed_y (n : ℕ) (hn : 2301 ≤ n) (i : Block n) (p : Tile.C (kind n i)) :
    (embed n hn i p).2.val = p.2.val := by
  change 0 + p.2.val = p.2.val
  omega

theorem overlap_adjacent (n : ℕ) (hn : 2301 ≤ n) {i j : Block n} (hij : i ≠ j)
    (p : Tile.C (kind n i)) (q : Tile.C (kind n j)) (he : embed n hn i p = embed n hn j q) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hx := congrArg (fun p : C n => p.1.val) he
  simp only [embed_x] at hx
  have hp := p.1.isLt
  have hq := q.1.isLt
  have hi : Tile.width (kind n i) ≤ 64 := by cases kind n i <;> decide
  have hj : Tile.width (kind n j) ≤ 64 := by cases kind n j <;> decide
  have hnidx : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
  rcases le_total i.val j.val with h | h
  · have hgap := offset_gap n i.val j.val h
    omega
  · have hgap := offset_gap n j.val i.val h
    omega

private theorem walls_overlap_next (n : ℕ) (hn : 2301 ≤ n) {i j : Block n}
    (hij : i.val + 1 = j.val) (p : Tile.C (kind n i)) (q : Tile.C (kind n j))
    (he : embed n hn i p = embed n hn j q) : p ∈ Tile.walls (kind n i) ↔ q ∈ Tile.walls (kind n j) := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [embed_x] at hx
  simp only [embed_y] at hy
  have hnext := offset_next n i.val
  rw [hij] at hnext
  have hp : p.1.val < Tile.span (kind n i) + 5 := by simpa only [Tile.width_eq] using p.1.isLt
  change offset n j.val = offset n i.val + Tile.span (kind n i) at hnext
  have hpx : Tile.span (kind n i) ≤ p.1.val := by omega
  have hqx : q.1.val < 5 := by omega
  rw [Tile.collar_walls _ p (Or.inr hpx), Tile.collar_walls _ q (Or.inl hqx), hy]

private theorem walls_overlap (n : ℕ) (hn : 2301 ≤ n) (i j : Block n)
    (p : Tile.C (kind n i)) (q : Tile.C (kind n j)) (he : embed n hn i p = embed n hn j q) :
    p ∈ Tile.walls (kind n i) ↔ q ∈ Tile.walls (kind n j) := by
  by_cases hij : i = j
  · subst j
    have hpq := (embed n hn i).injective he
    subst q
    rfl
  · rcases overlap_adjacent n hn hij p q he with h | h
    · exact walls_overlap_next n hn h p q he
    · exact (walls_overlap_next n hn h q p he.symm).symm

def walls (n : ℕ) (hn : 2301 ≤ n) : Finset (C n) :=
  Finset.univ.biUnion fun i : Block n => (Tile.walls (kind n i)).map (embed n hn i)

theorem walls_exact (n : ℕ) (hn : 2301 ≤ n) (i : Block n) (p : Tile.C (kind n i)) :
    embed n hn i p ∈ walls n hn ↔ p ∈ Tile.walls (kind n i) := by
  constructor
  · intro hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hj
    exact (walls_overlap n hn i j p q he.symm).mpr hq
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_map.mpr ⟨p,hp,rfl⟩⟩

theorem walls_rows (n : ℕ) (hn : 2301 ≤ n) (p : C n) (hp : p ∈ walls n hn) :
    p.2.val = 8 ∨ p.2.val = 9 ∨ p.2.val = 11 ∨ p.2.val = 12 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hi
  simpa only [embed_y] using Tile.wall_rows (kind n i) q hq

abbrev Phases (n : ℕ) := Block n → Bool
abbrev Label (n : ℕ) := (i : Block n) × Fin (Tile.count (kind n i))

def position (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (l : Label n) : C n :=
  embed n hn l.1 (Tile.position (kind n l.1) (a l.1) l.2)

theorem position_row (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (l : Label n) :
    (position n hn a l).2.val = 10 := by
  simpa only [position, embed_y] using (Tile.position_bounds (kind n l.1) (a l.1) l.2).1

theorem position_block_order (n : ℕ) (hn : 2301 ≤ n) (a : Phases n)
    (i j : Block n) (hij : i < j) (u : Fin (Tile.count (kind n i))) (v : Fin (Tile.count (kind n j))) :
    (position n hn a ⟨i,u⟩).1.val < (position n hn a ⟨j,v⟩).1.val := by
  have hbound := offset_mono n (i.val+1) j.val (by exact hij)
  rw [offset_next] at hbound
  have hu := Tile.position_bounds (kind n i) (a i) u
  have hv := Tile.position_bounds (kind n j) (a j) v
  change offset n i.val + (Tile.position (kind n i) (a i) u).1.val <
    offset n j.val + (Tile.position (kind n j) (a j) v).1.val
  change offset n i.val + Tile.span (kind n i) ≤ offset n j.val at hbound
  omega

theorem position_injective (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) : Function.Injective (position n hn a) := by
  rintro ⟨i,u⟩ ⟨j,v⟩ he
  by_cases hij : i = j
  · subst j
    change embed n hn i (Tile.position (kind n i) (a i) u) = embed n hn i (Tile.position (kind n i) (a i) v) at he
    have huv : u = v := (Tile.position_injective (kind n i) (a i)) ((embed n hn i).injective he)
    subst v
    rfl
  · have hx := congrArg (fun p : C n => p.1.val) he
    rcases lt_or_gt_of_ne hij with h | h
    · have hh := position_block_order n hn a i j h u v
      omega
    · have hh := position_block_order n hn a j i h v u
      omega

def blockBoxes (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) : Finset (C n) :=
  (Tile.boxes (kind n i) (a i)).map (embed n hn i)

def boxes (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) : Finset (C n) :=
  Finset.univ.biUnion fun i : Block n => blockBoxes n hn a i

theorem boxes_image (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) :
    boxes n hn a = Finset.univ.image (position n hn a) := by
  ext p
  simp only [boxes, blockBoxes, Tile.boxes, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_map, Finset.mem_image, Sigma.exists, position]
  constructor
  · rintro ⟨i,q,⟨u,hu⟩,he⟩
    exact ⟨i,u,hu ▸ he⟩
  · rintro ⟨i,u,he⟩
    exact ⟨i,_,⟨u,rfl⟩,he⟩

theorem boxes_row (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) {p : C n} (hp : p ∈ boxes n hn a) : p.2.val = 10 := by
  rw [boxes_image] at hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact position_row n hn a l

theorem boxes_floor (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) : Disjoint (boxes n hn a) (walls n hn) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hi
  exact Finset.disjoint_left.mp (Tile.boxes_floor (kind n i) (a i)) hq ((walls_exact n hn i q).mp hw)

end PushPuzzle.PushFS.Gadgets.Wires.Chain
