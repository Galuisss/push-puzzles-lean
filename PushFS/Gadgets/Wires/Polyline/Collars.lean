/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain
public import PushFS.Gadgets.Wires.Turn
public import PushFS.Isometry

/-! Exact wider collar stencils used by physical straight/turn joints. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every chain slot stays two cells inside its declared span collar. -/
theorem chain_slot_bounds (n : ℕ) (hn : 2301 ≤ n) (phase : Chain.Phases n) (l : Chain.Label n) :
    2 ≤ (Chain.position n hn phase l).1.val ∧ (Chain.position n hn phase l).1.val ≤ n+1 := by
  have hp := Chain.Tile.position_bounds (Chain.kind n l.1) (phase l.1) l.2
  have hf := Chain.fit n hn l.1
  rw [Chain.Tile.width_eq] at hf
  change 2 ≤ Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) (phase l.1) l.2).1.val ∧
    Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) (phase l.1) l.2).1.val ≤ n+1
  omega

private theorem tile_right7 (kind : Bool) (p : Chain.Tile.C kind) (hx : Chain.Tile.span kind ≤ p.1.val+2) :
    p ∈ Chain.Tile.walls kind ↔ p.2.val=11 ∨ p.2.val=12 := by
  have hh : ∀ (kind : Bool) (p : Chain.Tile.C kind), Chain.Tile.span kind ≤ p.1.val+2 →
      (Chain.Tile.template kind).wall p = decide (p.2.val=11 ∨ p.2.val=12) := by decide +kernel
  rw [← Chain.Tile.template_walls,Template.mem_walls,hh kind p hx,decide_eq_true_eq]

/-- The complete first five columns of an arbitrary real chain have the common lower wall guard. -/
theorem chain_left5 (n : ℕ) (hn : 2301 ≤ n) (p : Chain.C n) (hx : p.1.val < 5) :
    p ∈ Chain.walls n hn ↔ p.2.val=11 ∨ p.2.val=12 := by
  let i := Chain.firstBlock n hn
  have hw : 5 ≤ Chain.Tile.width (Chain.kind n i) := by cases Chain.kind n i <;> decide
  let q : Chain.Tile.C (Chain.kind n i) := (⟨p.1.val,by omega⟩,p.2)
  have he : Chain.embed n hn i q = p := by
    apply Prod.ext <;> apply Fin.ext
    · rw [Chain.embed_x,Chain.first_offset]
      simp [q]
    · exact Chain.embed_y n hn i q
  rw [← he,Chain.walls_exact,Chain.embed_y]
  exact Chain.Tile.collar_walls _ q (Or.inl hx)

/-- The complete last seven columns agree with the long eastern turn collar. -/
theorem chain_right7 (n : ℕ) (hn : 2301 ≤ n) (p : Chain.C n) (hx : n ≤ p.1.val+2) :
    p ∈ Chain.walls n hn ↔ p.2.val=11 ∨ p.2.val=12 := by
  let i := Chain.lastBlock n hn
  have hf := Chain.last_finish n hn
  have hs : 40 ≤ Chain.Tile.span (Chain.kind n i) := by cases Chain.kind n i <;> decide
  have hp := p.1.isLt
  let q : Chain.Tile.C (Chain.kind n i) := (⟨p.1.val-Chain.offset n i.val,by
    rw [Chain.Tile.width_eq]
    change Chain.offset n i.val+Chain.Tile.span (Chain.kind n i)=n at hf
    omega⟩,p.2)
  have hlo : Chain.offset n i.val ≤ p.1.val := by
    change Chain.offset n i.val+Chain.Tile.span (Chain.kind n i)=n at hf
    omega
  have he : Chain.embed n hn i q = p := by
    apply Prod.ext <;> apply Fin.ext
    · change Chain.offset n i.val+(p.1.val-Chain.offset n i.val)=p.1.val
      omega
    · exact Chain.embed_y n hn i q
  rw [← he,Chain.walls_exact,Chain.embed_y]
  apply tile_right7
  change Chain.Tile.span (Chain.kind n i) ≤ p.1.val-Chain.offset n i.val+2
  change Chain.offset n i.val+Chain.Tile.span (Chain.kind n i)=n at hf
  omega

/-- All seven eastern collar columns of the actual turn have the lower guard wall. -/
theorem turn_east7 (p : Turn.C) (hx : 38 ≤ p.1.val) :
    p ∈ Turn.template.walls ↔ p.2.val=10 ∨ p.2.val=11 := by
  have hh : ∀ p : Turn.C, 38 ≤ p.1.val → Turn.wallTest p = decide (p.2.val=10 ∨ p.2.val=11) := by decide +kernel
  rw [Template.mem_walls]
  change Turn.wallTest p=true ↔ _
  rw [hh p hx,decide_eq_true_eq]

/-- Every physical turn slot is confined to its two open arms, away from the shared corner. -/
theorem turn_slot_bounds : ∀ (phase : Bool) (i : Fin 29),
    ((Turn.template.position phase i).2.val=9 ∧ 11 ≤ (Turn.template.position phase i).1.val ∧
      (Turn.template.position phase i).1.val ≤ 40) ∨
    ((Turn.template.position phase i).1.val=10 ∧ 10 ≤ (Turn.template.position phase i).2.val ∧
      (Turn.template.position phase i).2.val ≤ 39) := by decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.Polyline
