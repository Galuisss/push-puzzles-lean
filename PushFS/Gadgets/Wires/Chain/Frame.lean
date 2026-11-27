/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Corners

/-! The entire unbounded connector permits fixed physical boxes at its two
outside-neighbor slots. Every local update discharges its collar condition
from the actual global end positions and phase frontier. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def neighbors (n : ℕ) : Finset (C n) := {(⟨0,by omega⟩,10),(⟨n+3,by omega⟩,10)}

private theorem neighbors_row (n : ℕ) {p : C n} (hp : p ∈ neighbors n) : p.2.val = 10 := by
  simp only [neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> rfl

private theorem neighbors_floor (n : ℕ) (hn : 2301 ≤ n) : Disjoint (neighbors n) (walls n hn) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  have hy := neighbors_row n hp
  have hh := walls_rows n hn p hw
  omega

/-- A connector-end neighbor can appear inside a local tile only at that
same tile's checked neighbor slot. -/
private theorem neighbors_local (n : ℕ) (hn : 2301 ≤ n) (i : Block n) (p : Tile.C (kind n i))
    (hp : embed n hn i p ∈ neighbors n) : p ∈ Tile.neighbors (kind n i) := by
  have hy := neighbors_row n hp
  rw [embed_y] at hy
  apply (Tile.mem_neighbors (kind n i) p).mpr
  refine ⟨hy,?_⟩
  simp only [neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with hp | hp
  · left
    have hx := congrArg (fun p : C n => p.1.val) hp
    simp only [embed_x] at hx
    change offset n i.val + p.1.val = 0 at hx
    omega
  · right
    have hx := congrArg (fun p : C n => p.1.val) hp
    simp only [embed_x] at hx
    change offset n i.val + p.1.val = n+3 at hx
    have hi : i.val+1 ≤ blockCount n := i.isLt
    have hg := offset_gap n (i.val+1) (blockCount n) hi
    have hf : offset n (blockCount n) = n := Spans.offset_finish n hn
    rw [hf,offset_next] at hg
    change offset n i.val + Tile.span (kind n i) + 40 * (blockCount n-(i.val+1)) ≤ n at hg
    have hb : p.1.val < Tile.span (kind n i)+5 := by simpa only [Tile.width_eq] using p.1.isLt
    have hlast : i.val+1 = blockCount n := by omega
    have hnext := offset_next n i.val
    rw [hlast,hf] at hnext
    change n = offset n i.val + Tile.span (kind n i) at hnext
    omega

private theorem tile_neighbors_reserved (b : Bool) : Tile.neighbors b ⊆ Tile.reserved b := by
  intro p hp
  have hh := (Tile.mem_neighbors b p).mp hp
  have hs : 40 ≤ Tile.span b := by cases b <;> decide
  apply (Tile.mem_reserved b p).mpr
  omega

namespace Frame

variable (n : ℕ) (hn : 2301 ≤ n) (fixed : Finset (C n)) (hf : fixed ⊆ neighbors n)

def state (a : Phases n) : State (n+5) 21 := Gates.withFixed fixed (Chain.state n hn a)
def stateAt (a : Phases n) (i : Block n) : State (n+5) 21 := Gates.withFixed fixed (Chain.stateAt n hn a i)
def external (a : Phases n) (i : Block n) : Finset (C n) := Chain.external n hn a i ∪ fixed

def localFixed (a : Phases n) (i : Block n) : Finset (Tile.C (kind n i)) :=
  Finset.univ.filter fun p => embed n hn i p ∈ external n hn fixed a i

@[simp] theorem mem_localFixed (a : Phases n) (i : Block n) (p : Tile.C (kind n i)) :
    p ∈ localFixed n hn fixed a i ↔ embed n hn i p ∈ external n hn fixed a i := by simp [localFixed]

include hf in
theorem external_floor (a : Phases n) (i : Block n) : Disjoint (external n hn fixed a i) (walls n hn) :=
  Finset.disjoint_union_left.mpr ⟨Chain.external_floor n hn a i,(neighbors_floor n hn).mono_left hf⟩

include hf in
private theorem localFixed_neighbors (a : Phases n) (i : Block n) (ha : Frontier n a i) :
    localFixed n hn fixed a i ⊆ Tile.neighbors (kind n i) := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_localFixed n hn fixed a i p).mp hp) with he | he
  · exact fixed_neighbors n hn a i ha ((mem_fixed n hn a i p).mpr he)
  · exact neighbors_local n hn i p (hf he)

include hf in
theorem localFixed_reserved (a : Phases n) (i : Block n) :
    localFixed n hn fixed a i ⊆ Tile.reserved (kind n i) := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_localFixed n hn fixed a i p).mp hp) with he | he
  · exact fixed_reserved n hn a i ((mem_fixed n hn a i p).mpr he)
  · exact tile_neighbors_reserved _ (neighbors_local n hn i p (hf he))

include hf in
theorem localFixed_floor (a : Phases n) (i : Block n) : Disjoint (localFixed n hn fixed a i) (Tile.walls (kind n i)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  exact Finset.disjoint_left.mp (external_floor n hn fixed hf a i)
    ((mem_localFixed n hn fixed a i p).mp hp) ((walls_exact n hn i p).mpr hw)

theorem place_state (a : Phases n) (i : Block n) :
    (Tile.state (kind n i) (a i)).place (placement n hn i) (external n hn fixed a i) = stateAt n hn fixed a i := by
  apply State.ext
  · rfl
  · change blockBoxes n hn a i ∪ (Chain.external n hn a i ∪ fixed) = boxes n hn a ∪ fixed
    rw [← Finset.union_assoc,boxes_split]

private theorem external_update (a : Phases n) (i : Block n) (b : Bool) :
    external n hn fixed (Function.update a i b) i = external n hn fixed a i := by
  unfold external
  rw [Chain.external_update]

private theorem place_update_state (a : Phases n) (i : Block n) (b : Bool) :
    (Tile.state (kind n i) b).place (placement n hn i) (external n hn fixed a i) =
      stateAt n hn fixed (Function.update a i b) i := by
  rw [← external_update n hn fixed a i b]
  simpa only [Function.update_self] using place_state n hn fixed (Function.update a i b) i

include hf in
private theorem walk_row (goals : Finset (C n)) (a : Phases n) (p q : C n) (hp : p.2.val = 3)
    (hq : q.2.val = 3) :
    Reachable (board n hn goals) (some 1) ⟨p,boxes n hn a ∪ fixed⟩ ⟨q,boxes n hn a ∪ fixed⟩ := by
  have hp' : p = (p.1,(3 : Fin 21)) := Prod.ext rfl (Fin.ext hp)
  have hq' : q = (q.1,(3 : Fin 21)) := Prod.ext rfl (Fin.ext hq)
  rw [hp',hq']
  apply walk_horizontal (Finset.disjoint_union_left.mpr ⟨boxes_floor n hn a,(neighbors_floor n hn).mono_left hf⟩)
  intro x _ _
  constructor
  · intro hw
    have hh := walls_rows n hn (x,3) hw
    norm_num at hh
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · have hh := boxes_row n hn a hb
      norm_num at hh
    · have hh := neighbors_row n (hf hb)
      norm_num at hh

include hf in
theorem hub_to_block (goals : Finset (C n)) (a : Phases n) (i : Block n) :
    Reachable (board n hn goals) (some 1) (state n hn fixed a) (stateAt n hn fixed a i) :=
  walk_row n hn fixed hf goals a (hub n hn) (embed n hn i (Tile.hub (kind n i))) rfl (by simp only [embed_y,Tile.hub_y])

include hf in
theorem block_to_hub (goals : Finset (C n)) (a : Phases n) (i : Block n) :
    Reachable (board n hn goals) (some 1) (stateAt n hn fixed a i) (state n hn fixed a) :=
  walk_row n hn fixed hf goals a (embed n hn i (Tile.hub (kind n i))) (hub n hn) (by simp only [embed_y,Tile.hub_y]) rfl

include hf in
private theorem update_at (goals : Finset (C n)) (a : Phases n) (i : Block n) (ha : Frontier n a i)
    (b : Bool) :
    Reachable (board n hn goals) (some 1) (stateAt n hn fixed a i) (stateAt n hn fixed (Function.update a i b) i) := by
  have hh := Tile.transition_placed (kind n i) (a i) b (localFixed n hn fixed a i)
    (localFixed_neighbors n hn fixed hf a i ha) (placement n hn i)
    (B := board n hn goals) (external := external n hn fixed a i) (walls_exact n hn i)
    (fun p hp => (mem_localFixed n hn fixed a i p).mpr hp)
    (fun p hp => (mem_localFixed n hn fixed a i p).mp hp) (external_floor n hn fixed hf a i)
  change Reachable (board n hn goals) (some 1)
    ((Tile.state (kind n i) (a i)).place (placement n hn i) (external n hn fixed a i))
    ((Tile.state (kind n i) b).place (placement n hn i) (external n hn fixed a i)) at hh
  simpa only [place_state,place_update_state] using hh

include hf in
private theorem update (goals : Finset (C n)) (a : Phases n) (i : Block n) (ha : Frontier n a i)
    (b : Bool) :
    Reachable (board n hn goals) (some 1) (state n hn fixed a) (state n hn fixed (Function.update a i b)) :=
  (hub_to_block n hn fixed hf goals a i).trans ((update_at n hn fixed hf goals a i ha b).trans
    (block_to_hub n hn fixed hf goals (Function.update a i b) i))

include hf in
theorem transition (goals : Finset (C n)) (a b : Bool) :
    Reachable (board n hn goals) (some 1) (state n hn fixed (uniform n a)) (state n hn fixed (uniform n b)) := by
  have hp (t : Fin (blockCount n+1)) :
      Reachable (board n hn goals) (some 1) (state n hn fixed (cut n 0)) (state n hn fixed (cut n t.val)) ∧
      Reachable (board n hn goals) (some 1) (state n hn fixed (cut n t.val)) (state n hn fixed (cut n 0)) := by
    induction t using Fin.induction with
    | zero => exact ⟨.refl,.refl⟩
    | succ i ih =>
      have hforward := update n hn fixed hf goals (cut n i.val) i (cut_frontier n i) false
      rw [update_cut_false] at hforward
      have hback := update n hn fixed hf goals (cut n (i.val+1)) i (cut_next_frontier n i) true
      rw [update_cut_true] at hback
      exact ⟨ih.1.trans hforward,hback.trans ih.2⟩
  have hh := hp (Fin.last (blockCount n))
  simp only [Fin.val_last,cut_zero,cut_finish] at hh
  cases a <;> cases b
  · exact .refl
  · exact hh.2
  · exact hh.1
  · exact .refl

end Frame
end PushPuzzle.PushFS.Gadgets.Wires.Chain
