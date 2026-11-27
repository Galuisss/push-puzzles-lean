/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Geometry

/-! Exact neighboring-box occupancy inside every placed wire block. The phase
frontier derives the permissive neighbor set from the actual adjacent boxes. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def external (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) : Finset (C n) :=
  (Finset.univ.erase i).biUnion fun j => blockBoxes n hn a j

def fixed (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) : Finset (Tile.C (kind n i)) :=
  Finset.univ.filter fun p => embed n hn i p ∈ external n hn a i

@[simp] theorem mem_fixed (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) (p : Tile.C (kind n i)) :
    p ∈ fixed n hn a i ↔ embed n hn i p ∈ external n hn a i := by simp [fixed]

private theorem external_subset (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) :
    external n hn a i ⊆ boxes n hn a := by
  intro p hp
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩

theorem external_floor (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) :
    Disjoint (external n hn a i) (walls n hn) :=
  (boxes_floor n hn a).mono_left (external_subset n hn a i)

theorem boxes_split (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) :
    blockBoxes n hn a i ∪ external n hn a i = boxes n hn a := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩
    · exact external_subset n hn a i hp
  · intro hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    by_cases hji : j = i
    · subst j; exact Finset.mem_union_left _ hj
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,by simp [hji],hj⟩)

theorem external_update (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) (b : Bool) :
    external n hn (Function.update a i b) i = external n hn a i := by
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [blockBoxes, Function.update_of_ne hji]

/-- At a local update, all preceding blocks are low and all following blocks
are high. This is the actual update order, in either direction. -/
def Frontier (n : ℕ) (a : Phases n) (i : Block n) : Prop :=
  (∀ j, j < i → a j = false) ∧ (∀ j, i < j → a j = true)

theorem fixed_neighbors (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) (ha : Frontier n a i) :
    fixed n hn a i ⊆ Tile.neighbors (kind n i) := by
  intro p hp
  obtain ⟨j,hj,hq⟩ := Finset.mem_biUnion.mp ((mem_fixed n hn a i p).mp hp)
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hq
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hq
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [embed_x] at hx
  simp only [embed_y] at hy
  have hb := Tile.position_bounds (kind n j) (a j) u
  apply (Tile.mem_neighbors (kind n i) p).mpr
  refine ⟨by omega, ?_⟩
  rcases overlap_adjacent n hn hji (Tile.position (kind n j) (a j) u) p he with hnext | hnext
  · have hphase : a j = false := ha.1 j (by change j.val < i.val; omega)
    have ho := offset_next n j.val
    rw [hnext] at ho
    change offset n i.val = offset n j.val + Tile.span (kind n j) at ho
    have hlo : Tile.span (kind n j) ≤ (Tile.position (kind n j) false u).1.val := by rw [hphase] at hx; omega
    have hlast := Tile.right_low (kind n j) u hlo
    left
    rw [hphase] at hx
    omega
  · have hphase : a j = true := ha.2 j (by change i.val < j.val; omega)
    have ho := offset_next n i.val
    rw [hnext] at ho
    change offset n j.val = offset n i.val + Tile.span (kind n i) at ho
    have hpbound : p.1.val < Tile.span (kind n i) + 5 := by simpa only [Tile.width_eq] using p.1.isLt
    have hhi : (Tile.position (kind n j) true u).1.val ≤ 4 := by rw [hphase] at hx; omega
    have hfirst := Tile.left_high (kind n j) u hhi
    right
    rw [hphase] at hx
    omega

/-- Corner walks tolerate all phases of every neighboring block, including the
second low box in the right-hand collar. -/
theorem fixed_reserved (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) :
    fixed n hn a i ⊆ Tile.reserved (kind n i) := by
  intro p hp
  obtain ⟨j,hj,hq⟩ := Finset.mem_biUnion.mp ((mem_fixed n hn a i p).mp hp)
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hq
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hq
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [embed_x] at hx
  simp only [embed_y] at hy
  have hb := Tile.position_bounds (kind n j) (a j) u
  have hloc : p.1.val ≤ 1 ∨ Tile.span (kind n i) + 2 ≤ p.1.val := by
    rcases overlap_adjacent n hn hji (Tile.position (kind n j) (a j) u) p he with hnext | hnext
    · have ho := offset_next n j.val
      rw [hnext] at ho
      change offset n i.val = offset n j.val + Tile.span (kind n j) at ho
      left; omega
    · have ho := offset_next n i.val
      rw [hnext] at ho
      change offset n j.val = offset n i.val + Tile.span (kind n i) at ho
      right; omega
  have hs : 40 ≤ Tile.span (kind n i) := by cases kind n i <;> decide
  apply (Tile.mem_reserved (kind n i) p).mpr
  omega

theorem fixed_floor (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) :
    Disjoint (fixed n hn a i) (Tile.walls (kind n i)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  exact Finset.disjoint_left.mp (external_floor n hn a i) ((mem_fixed n hn a i p).mp hp)
    ((walls_exact n hn i p).mpr hw)

end PushPuzzle.PushFS.Gadgets.Wires.Chain
