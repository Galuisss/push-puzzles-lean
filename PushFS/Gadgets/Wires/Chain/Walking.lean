/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Placement

/-! Corner access is available with either phase of either neighboring piece,
including its second endpoint box when it enters the last collar column.
Only transition macros require the narrower two-slot frontier condition. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Chain

set_option maxRecDepth 4096

def allNeighbors (n : ℕ) : Finset (C n) :=
  {(⟨0,by omega⟩,10),(⟨1,by omega⟩,10),(⟨n+2,by omega⟩,10),(⟨n+3,by omega⟩,10),(⟨n+4,by omega⟩,10)}

theorem allNeighbors_bounds (n : ℕ) {p : C n} (hp : p ∈ allNeighbors n) :
    p.2.val = 10 ∧ (p.1.val ≤ 1 ∨ n+2 ≤ p.1.val) := by
  simp only [allNeighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem allNeighbors_floor (n : ℕ) (hn : 2301 ≤ n) : Disjoint (allNeighbors n)
    (walls n hn) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  have hy := (allNeighbors_bounds n hp).1
  have hh := walls_rows n hn p hw
  omega

private theorem allNeighbors_local (n : ℕ) (hn : 2301 ≤ n) (i : Block n) (p : Tile.C (kind n i))
    (hp : embed n hn i p ∈ allNeighbors n) : p ∈ Tile.reserved (kind n i) := by
  have hh := allNeighbors_bounds n hp
  simp only [embed_x,embed_y] at hh
  have hb := Spans.offset_le n (i.val+1) hn i.isLt
  change offset n (i.val+1) ≤ n at hb
  rw [offset_next] at hb
  have hs : 40 ≤ Tile.span (kind n i) := by cases kind n i <;> decide
  apply (Tile.mem_reserved (kind n i) p).mpr
  change offset n i.val + Tile.span (kind n i) ≤ n at hb
  omega

namespace Frame
variable (n : ℕ) (hn : 2301 ≤ n) (fixed : Finset (C n)) (hf : fixed ⊆ allNeighbors n)

include hf in
 private theorem external_floor_allNeighbors (a : Phases n) (i : Block n) :
    Disjoint (external n hn fixed a i) (walls n hn) :=
  Finset.disjoint_union_left.mpr ⟨Chain.external_floor n hn a i,(allNeighbors_floor n hn).mono_left hf⟩

include hf in
 private theorem localFixed_reserved_allNeighbors (a : Phases n) (i : Block n) :
    localFixed n hn fixed a i ⊆ Tile.reserved (kind n i) := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_localFixed n hn fixed a i p).mp hp) with he | he
  · exact fixed_reserved n hn a i ((mem_fixed n hn a i p).mpr he)
  · exact allNeighbors_local n hn i p (hf he)

include hf in
 private theorem localFixed_floor_allNeighbors (a : Phases n) (i : Block n) :
    Disjoint (localFixed n hn fixed a i) (Tile.walls (kind n i)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  exact Finset.disjoint_left.mp (external_floor_allNeighbors n hn fixed hf a i)
    ((mem_localFixed n hn fixed a i p).mp hp) ((walls_exact n hn i p).mpr hw)

include hf in
private theorem walk_row_allNeighbors (goals : Finset (C n)) (a : Phases n) (p q : C n)
    (hp : p.2.val = 3) (hq : q.2.val = 3) :
    Reachable (board n hn goals) (some 1) ⟨p,boxes n hn a ∪ fixed⟩ ⟨q,boxes n hn a ∪ fixed⟩ := by
  have hp' : p = (p.1,(3 : Fin 21)) := Prod.ext rfl (Fin.ext hp)
  have hq' : q = (q.1,(3 : Fin 21)) := Prod.ext rfl (Fin.ext hq)
  rw [hp',hq']
  apply walk_horizontal (Finset.disjoint_union_left.mpr ⟨boxes_floor n hn a,(allNeighbors_floor n hn).mono_left hf⟩)
  intro x _ _
  constructor
  · intro hw
    have hh := walls_rows n hn (x,3) hw
    norm_num at hh
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · have hh := boxes_row n hn a hb
      norm_num at hh
    · have hh := (allNeighbors_bounds n (hf hb)).1
      norm_num at hh

include hf in
private theorem hub_to_block_allNeighbors (goals : Finset (C n)) (a : Phases n) (i : Block n) :
    Reachable (board n hn goals) (some 1) (state n hn fixed a) (stateAt n hn fixed a i) :=
  walk_row_allNeighbors n hn fixed hf goals a (hub n hn) (embed n hn i (Tile.hub (kind n i))) rfl (by simp only [embed_y,Tile.hub_y])

include hf in
private theorem block_to_hub_allNeighbors (goals : Finset (C n)) (a : Phases n) (i : Block n) :
    Reachable (board n hn goals) (some 1) (stateAt n hn fixed a i) (state n hn fixed a) :=
  walk_row_allNeighbors n hn fixed hf goals a (embed n hn i (Tile.hub (kind n i))) (hub n hn) (by simp only [embed_y,Tile.hub_y]) rfl

include hf in
private theorem corner_at_allNeighbors (goals : Finset (C n)) (a : Phases n) (i : Block n)
    (j : Fin 4) :
    Reachable (board n hn goals) (some 1) (stateAt n hn fixed a i)
        ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a ∪ fixed⟩ ∧
      Reachable (board n hn goals) (some 1) ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a ∪ fixed⟩
        (stateAt n hn fixed a i) := by
  have hh := Tile.corners_placed (kind n i) (a i) j (localFixed n hn fixed a i)
    (localFixed_reserved_allNeighbors n hn fixed hf a i) (localFixed_floor_allNeighbors n hn fixed hf a i)
    (placement n hn i) (B := board n hn goals) (external := external n hn fixed a i)
    (walls_exact n hn i) (fun p hp => (mem_localFixed n hn fixed a i p).mpr hp)
    (fun p hp => (mem_localFixed n hn fixed a i p).mp hp) (external_floor_allNeighbors n hn fixed hf a i)
  simpa only [place_state,place_corner] using hh

include hf in
private theorem corners_allNeighbors (goals : Finset (C n)) (a : Phases n) (i : Fin 4) :
    Reachable (board n hn goals) (some 1) (state n hn fixed a) ⟨corner n i,boxes n hn a ∪ fixed⟩ ∧
      Reachable (board n hn goals) (some 1) ⟨corner n i,boxes n hn a ∪ fixed⟩ (state n hn fixed a) := by
  have hh := corner_at_allNeighbors n hn fixed hf goals a (cornerBlock n hn i) i
  rw [embed_cornerBlock] at hh
  exact ⟨(hub_to_block_allNeighbors n hn fixed hf goals a _).trans hh.1,
    hh.2.trans (block_to_hub_allNeighbors n hn fixed hf goals a _)⟩
end Frame

/-- Placed corner access with arbitrary mixed endpoint phases and all five collar slots. -/
theorem corners_placed_allNeighbors {W H : ℕ} (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Fin 4)
    (fixed : Finset (C n)) (hf : fixed ⊆ allNeighbors n) (e : GridEmbedding (n+5) 21 W H)
    {B : Board W H} {external : Finset (Cell W H)}
    (hwalls : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀ p, e.cells p ∈ external → p ∈ fixed)
    (hfixed : ∀ p ∈ fixed, e.cells p ∈ external)
    (hfree : Disjoint external B.walls) :
    Reachable B (some 1) ((state n hn a).place e external)
      ((⟨corner n i,boxes n hn a⟩ : State (n+5) 21).place e external) ∧
    Reachable B (some 1) ((⟨corner n i,boxes n hn a⟩ : State (n+5) 21).place e external)
      ((state n hn a).place e external) := by
  have hh := Frame.corners_allNeighbors n hn fixed hf ∅ a i
  exact ⟨e.reachable_withFixed hwalls hinside hfixed hfree hh.1,
    e.reachable_withFixed hwalls hinside hfixed hfree hh.2⟩

end PushPuzzle.PushFS.Gadgets.Wires.Chain
