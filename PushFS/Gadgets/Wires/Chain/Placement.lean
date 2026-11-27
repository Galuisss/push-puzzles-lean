/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Frame

/-! Whole-chain macros and corner walks survive placement into arbitrary boards
with the exact wall stencil and the two permissive connector-neighbor slots. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096

namespace Frame
variable (n : ℕ) (hn : 2301 ≤ n) (fixed : Finset (C n)) (hf : fixed ⊆ neighbors n)

theorem place_corner (a : Phases n) (i : Block n) (j : Fin 4) :
    (⟨Tile.corner (kind n i) j,Tile.boxes (kind n i) (a i)⟩ : State (Tile.width (kind n i)) 21).place
      (placement n hn i) (external n hn fixed a i) = ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a ∪ fixed⟩ := by
  apply State.ext
  · rfl
  · change blockBoxes n hn a i ∪ (Chain.external n hn a i ∪ fixed) = boxes n hn a ∪ fixed
    rw [← Finset.union_assoc,boxes_split]

include hf in
private theorem corner_at (goals : Finset (C n)) (a : Phases n) (i : Block n) (j : Fin 4) :
    Reachable (board n hn goals) (some 1) (stateAt n hn fixed a i)
        ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a ∪ fixed⟩ ∧
      Reachable (board n hn goals) (some 1) ⟨embed n hn i (Tile.corner (kind n i) j),boxes n hn a ∪ fixed⟩
        (stateAt n hn fixed a i) := by
  have hh := Tile.corners_placed (kind n i) (a i) j (localFixed n hn fixed a i)
    (localFixed_reserved n hn fixed hf a i) (localFixed_floor n hn fixed hf a i)
    (placement n hn i) (B := board n hn goals) (external := external n hn fixed a i)
    (walls_exact n hn i) (fun p hp => (mem_localFixed n hn fixed a i p).mpr hp)
    (fun p hp => (mem_localFixed n hn fixed a i p).mp hp) (external_floor n hn fixed hf a i)
  simpa only [place_state,place_corner] using hh

include hf in
private theorem corners (goals : Finset (C n)) (a : Phases n) (i : Fin 4) :
    Reachable (board n hn goals) (some 1) (state n hn fixed a) ⟨corner n i,boxes n hn a ∪ fixed⟩ ∧
      Reachable (board n hn goals) (some 1) ⟨corner n i,boxes n hn a ∪ fixed⟩ (state n hn fixed a) := by
  have hh := corner_at n hn fixed hf goals a (cornerBlock n hn i) i
  rw [embed_cornerBlock] at hh
  exact ⟨(hub_to_block n hn fixed hf goals a _).trans hh.1,
    hh.2.trans (block_to_hub n hn fixed hf goals a _)⟩
end Frame

/-- Place both full phase macros, preserving all actual external neighbor boxes. -/
theorem transition_placed {W H : ℕ} (n : ℕ) (hn : 2301 ≤ n) (a b : Bool)
    (fixed : Finset (C n)) (hf : fixed ⊆ neighbors n) (e : GridEmbedding (n+5) 21 W H)
    {B : Board W H} {external : Finset (Cell W H)}
    (hwalls : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀ p, e.cells p ∈ external → p ∈ fixed)
    (hfixed : ∀ p ∈ fixed, e.cells p ∈ external)
    (hfree : Disjoint external B.walls) :
    Reachable B (some 1) ((state n hn (uniform n a)).place e external)
      ((state n hn (uniform n b)).place e external) :=
  e.reachable_withFixed hwalls hinside hfixed hfree (Frame.transition n hn fixed hf ∅ a b)

/-- Four real corner walks with the transition collar occupied. -/
theorem corners_placed {W H : ℕ} (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Fin 4)
    (fixed : Finset (C n)) (hf : fixed ⊆ neighbors n) (e : GridEmbedding (n+5) 21 W H)
    {B : Board W H} {external : Finset (Cell W H)}
    (hwalls : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀ p, e.cells p ∈ external → p ∈ fixed)
    (hfixed : ∀ p ∈ fixed, e.cells p ∈ external)
    (hfree : Disjoint external B.walls) :
    Reachable B (some 1) ((state n hn a).place e external)
      ((⟨corner n i,boxes n hn a⟩ : State (n+5) 21).place e external) ∧
    Reachable B (some 1) ((⟨corner n i,boxes n hn a⟩ : State (n+5) 21).place e external)
      ((state n hn a).place e external) := by
  have hh := Frame.corners n hn fixed hf ∅ a i
  exact ⟨e.reachable_withFixed hwalls hinside hfixed hfree hh.1,
    e.reachable_withFixed hwalls hinside hfixed hfree hh.2⟩

end PushPuzzle.PushFS.Gadgets.Wires.Chain
