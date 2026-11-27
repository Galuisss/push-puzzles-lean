/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.Collars

/-! Exact canonical-phase bounds used to discharge all real joint neighbor conditions. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem tile_phase_bounds (kind phase : Bool) (i : Fin (Chain.Tile.count kind)) :
    2+phase.toNat ≤ (Chain.Tile.position kind phase i).1.val ∧
      (Chain.Tile.position kind phase i).1.val ≤ Chain.Tile.span kind+phase.toNat := by
  have hh : ∀ (kind phase : Bool) (i : Fin (Chain.Tile.count kind)),
      2+phase.toNat ≤ (Chain.Tile.position kind phase i).1.val ∧
      (Chain.Tile.position kind phase i).1.val ≤ Chain.Tile.span kind+phase.toNat := by decide +kernel
  exact hh kind phase i

theorem chain_phase_bounds (n : ℕ) (hn : 2301 ≤ n) (phase : Bool) (l : Chain.Label n) :
    2+phase.toNat ≤ (Chain.position n hn (Chain.uniform n phase) l).1.val ∧
      (Chain.position n hn (Chain.uniform n phase) l).1.val ≤ n+phase.toNat := by
  have hp := tile_phase_bounds (Chain.kind n l.1) phase l.2
  have hf := Chain.fit n hn l.1
  rw [Chain.Tile.width_eq] at hf
  change 2+phase.toNat ≤ Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) phase l.2).1.val ∧
    Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) phase l.2).1.val ≤ n+phase.toNat
  omega

/-- The two low-phase boxes visible in the last three occupied rail columns are exactly the last train pair. -/
theorem chain_right_low (n : ℕ) (hn : 2301 ≤ n) (l : Chain.Label n)
    (hx : n ≤ (Chain.position n hn (Chain.uniform n false) l).1.val+2) :
    (Chain.position n hn (Chain.uniform n false) l).1.val=n ∨
      (Chain.position n hn (Chain.uniform n false) l).1.val+2=n := by
  have check : ∀ (kind : Bool) (i : Fin (Chain.Tile.count kind)),
      Chain.Tile.span kind ≤ (Chain.Tile.position kind false i).1.val+2 →
      (Chain.Tile.position kind false i).1.val=Chain.Tile.span kind ∨
        (Chain.Tile.position kind false i).1.val+2=Chain.Tile.span kind := by decide +kernel
  have hp := tile_phase_bounds (Chain.kind n l.1) false l.2
  have hg := Chain.offset_gap n (l.1.val+1) (Chain.blockCount n) l.1.isLt
  have hf : Chain.offset n (Chain.blockCount n)=n := Chain.Spans.offset_finish n hn
  rw [hf,Chain.offset_next] at hg
  change Chain.offset n l.1.val+Chain.Tile.span (Chain.kind n l.1)+
    40*(Chain.blockCount n-(l.1.val+1)) ≤ n at hg
  have hval : Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) false l.2).1.val+2 ≥ n := hx
  have he : l.1.val+1=Chain.blockCount n := by have := l.1.isLt; simp only [Bool.toNat_false,Nat.add_zero] at hp; omega
  have hend := Chain.offset_next n l.1.val
  rw [he,hf] at hend
  change n=Chain.offset n l.1.val+Chain.Tile.span (Chain.kind n l.1) at hend
  have hh := check (Chain.kind n l.1) l.2 (by omega)
  change Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) false l.2).1.val=n ∨
    Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) false l.2).1.val+2=n
  omega

theorem turn_east_high : ∀ i : Fin 29, 38 ≤ (Turn.template.position true i).1.val →
    Turn.template.position true i=(39,9) := by decide +kernel

theorem turn_south_low : ∀ i : Fin 29, 38 ≤ (Turn.template.position false i).2.val →
    Turn.template.position false i=(10,38) := by decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.Polyline
