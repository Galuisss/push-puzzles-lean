/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Targets
public import Mathlib.Data.Fin.VecNotation

/-! The common hub and all four external corners are connected by actual
walks, with every physical box fixed in any independently selected phase. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096
set_option maxHeartbeats 500000

theorem place_corner (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) (j : Fin 4) :
    (⟨Tile.corner (kind n i) j,Tile.boxes (kind n i) (a i)⟩ : State (Tile.width (kind n i)) 21).place
      (placement n hn i) (external n hn a i) = ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a⟩ := by
  apply State.ext
  · rfl
  · exact boxes_split n hn a i

theorem corner_at (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a : Phases n)
    (i : Block n) (j : Fin 4) :
    Reachable (board n hn goals) (some 1) (stateAt n hn a i) ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a⟩ ∧
      Reachable (board n hn goals) (some 1) ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a⟩ (stateAt n hn a i) := by
  have hh := Tile.corners_placed (kind n i) (a i) j (fixed n hn a i)
    (fixed_reserved n hn a i) (fixed_floor n hn a i) (placement n hn i)
    (B := board n hn goals) (external := external n hn a i)
    (walls_exact n hn i) (fun p hp => (mem_fixed n hn a i p).mpr hp)
    (fun p hp => (mem_fixed n hn a i p).mp hp) (external_floor n hn a i)
  simpa only [place_state, place_corner] using hh

def firstBlock (n : ℕ) (hn : 2301 ≤ n) : Block n := ⟨0,blockCount_pos n hn⟩
def lastBlock (n : ℕ) (hn : 2301 ≤ n) : Block n := ⟨blockCount n-1,by have := blockCount_pos n hn; omega⟩

theorem first_offset (n : ℕ) (hn : 2301 ≤ n) : offset n (firstBlock n hn).val = 0 :=
  Spans.offset_zero n

theorem last_finish (n : ℕ) (hn : 2301 ≤ n) :
    offset n (lastBlock n hn).val + Tile.span (kind n (lastBlock n hn)) = n := by
  have hh := offset_next n (lastBlock n hn).val
  have he : (lastBlock n hn).val + 1 = blockCount n := by have := blockCount_pos n hn; dsimp [lastBlock]; omega
  rw [he] at hh
  have hf : offset n (blockCount n) = n := Spans.offset_finish n hn
  rw [hf] at hh
  exact hh.symm

def corner (n : ℕ) (i : Fin 4) : C n :=
  ![(⟨1,by omega⟩,1),(⟨n+3,by omega⟩,1),(⟨1,by omega⟩,19),(⟨n+3,by omega⟩,19)] i

def cornerBlock (n : ℕ) (hn : 2301 ≤ n) (i : Fin 4) : Block n :=
  if i = 0 ∨ i = 2 then firstBlock n hn else lastBlock n hn

private theorem tile_corner_xy (b : Bool) (i : Fin 4) :
    (Tile.corner b i).1.val = (if i = 0 ∨ i = 2 then 1 else Tile.span b + 3) ∧
      (Tile.corner b i).2.val = (if i.val < 2 then 1 else 19) := by
  have hh : ∀ b i, (Tile.corner b i).1.val = (if i = 0 ∨ i = 2 then 1 else Tile.span b + 3) ∧
      (Tile.corner b i).2.val = (if i.val < 2 then 1 else 19) := by decide +kernel
  exact hh b i

theorem embed_cornerBlock (n : ℕ) (hn : 2301 ≤ n) (i : Fin 4) :
    embed n hn (cornerBlock n hn i) (Tile.corner (kind n (cornerBlock n hn i)) i) = corner n i := by
  have hc := tile_corner_xy (kind n (cornerBlock n hn i)) i
  have hf := first_offset n hn
  have hl := last_finish n hn
  apply Prod.ext <;> apply Fin.ext
  · rw [embed_x]
    fin_cases i <;> simp [cornerBlock,corner] at hc ⊢ <;> omega
  · rw [embed_y]
    fin_cases i <;> simp [corner] at hc ⊢ <;> omega

/-- All four outer corners are genuinely connected to the common hub in both
ways for every phase assignment, with the entire box set unchanged. -/
theorem corners (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a : Phases n) (i : Fin 4) :
    Reachable (board n hn goals) (some 1) (state n hn a) ⟨corner n i,boxes n hn a⟩ ∧
      Reachable (board n hn goals) (some 1) ⟨corner n i,boxes n hn a⟩ (state n hn a) := by
  have hh := corner_at n hn goals a (cornerBlock n hn i) i
  rw [embed_cornerBlock] at hh
  exact ⟨(hub_to_block n hn goals a _).trans hh.1,hh.2.trans (block_to_hub n hn goals a _)⟩

end PushPuzzle.PushFS.Gadgets.Wires.Chain
