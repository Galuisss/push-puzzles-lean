/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.AxisGeometry
public import PushFS.LabelOrder

/-! Compiler-side order of every physical source and target slot in a wire chain. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Chain


private theorem tile_ordered (k phase : Bool) : StrictMono fun i : Fin (Tile.count k) =>
    (Tile.position k phase i).1.val := by
  cases k
  · exact Straight.ordered_slots phase
  · exact Parity.ordered_slots phase

/-- Every independent phase assignment preserves the same global physical label order. -/
theorem position_order (n : ℕ) (hn : 2301 ≤ n) (a b : Phases n) (i j : Label n)
    (hij : (position n hn a i).1.val < (position n hn a j).1.val) :
    (position n hn b i).1.val < (position n hn b j).1.val := by
  rcases i with ⟨i,u⟩
  rcases j with ⟨j,v⟩
  by_cases he : i = j
  · subst j
    change offset n i.val+(Tile.position (kind n i) (a i) u).1.val <
      offset n i.val+(Tile.position (kind n i) (a i) v).1.val at hij
    have huv : u < v := (tile_ordered (kind n i) (a i)).lt_iff_lt.mp (by omega)
    have hh := tile_ordered (kind n i) (b i) huv
    change offset n i.val+(Tile.position (kind n i) (b i) u).1.val <
      offset n i.val+(Tile.position (kind n i) (b i) v).1.val
    exact Nat.add_lt_add_left hh _
  · rcases lt_or_gt_of_ne he with he | he
    · exact position_block_order n hn b i j he u v
    · have hh := position_block_order n hn a j i he v u
      omega

end PushPuzzle.PushFS.Gadgets.Wires.Chain
