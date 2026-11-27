/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain
public import PushFS.Gadgets.Wires.Soundness.Horizontal
public import PushFS.Gadgets.Wires.Soundness.Line

/-! Static geometry and canonical labels of physical 40/59 chains. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness

namespace ChainGeometry

def horizontalKind (b : Bool) : HorizontalKind := if b then .parity else .straight

theorem width (b : Bool) : (horizontalKind b).width = Chain.Tile.width b := by cases b <;> rfl
theorem count (b : Bool) : (horizontalKind b).count = Chain.Tile.count b := by cases b <;> rfl

def index (b : Bool) (i : Fin (horizontalKind b).count) : Fin (Chain.Tile.count b) := Fin.cast (count b) i
def cell (b : Bool) (p : Cell (horizontalKind b).width 21) : Chain.Tile.C b := (Fin.cast (width b) p.1,p.2)

theorem walls (b : Bool) (p : Cell (horizontalKind b).width 21) :
    cell b p ∈ Chain.Tile.walls b ↔ p ∈ (horizontalKind b).template.walls := by cases b <;> rfl

theorem position (b phase : Bool) (i : Fin (horizontalKind b).count) :
    (Chain.Tile.position b phase (index b i)).1.val = ((horizontalKind b).template.position phase i).1.val ∧
    (Chain.Tile.position b phase (index b i)).2.val = ((horizontalKind b).template.position phase i).2.val := by
  cases b <;> exact ⟨rfl,rfl⟩

theorem span (b : Bool) : (horizontalKind b).span = Chain.Tile.span b := by cases b <;> rfl

/-- The arbitrary chain's rail has no horizontal floor gaps. -/
theorem row_floor (n : ℕ) (hn : 2301 ≤ n) (x : Fin (n+5)) : (x,10) ∉ Chain.walls n hn := by
  intro hw
  have hh := Chain.walls_rows n hn (x,10) hw
  norm_num at hh

/-- All canonical physical labels, including across every seam, lie in one real static SCC. -/
theorem slots_component (n : ℕ) (hn : 2301 ≤ n) (phase : Bool) (i j : Chain.Label n) :
    SameComponent (Chain.board n hn ∅) (Chain.position n hn (Chain.uniform n phase) i)
      (Chain.position n hn (Chain.uniform n phase) j) := by
  have bounds (l : Chain.Label n) :
      0 < (Chain.position n hn (Chain.uniform n phase) l).1.val ∧
      (Chain.position n hn (Chain.uniform n phase) l).1.val+1 < n+5 := by
    have hh := Chain.Tile.position_bounds (Chain.kind n l.1) phase l.2
    have hfit := Chain.fit n hn l.1
    rw [Chain.Tile.width_eq] at hfit
    change 0 < Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) phase l.2).1.val ∧
      Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) phase l.2).1.val+1 < n+5
    omega
  have hrowi := Chain.position_row n hn (Chain.uniform n phase) i
  have hrowj := Chain.position_row n hn (Chain.uniform n phase) j
  have hi : Chain.position n hn (Chain.uniform n phase) i =
      ((Chain.position n hn (Chain.uniform n phase) i).1,10) := Prod.ext rfl (Fin.ext hrowi)
  have hj : Chain.position n hn (Chain.uniform n phase) j =
      ((Chain.position n hn (Chain.uniform n phase) j).1,10) := Prod.ext rfl (Fin.ext hrowj)
  rw [hi,hj]
  exact horizontal_component 10 (row_floor n hn) _ _ (bounds i) (bounds j)

def firstLabel (n : ℕ) (i : Chain.Block n) : Chain.Label n :=
  ⟨i,index (Chain.kind n i) (horizontalKind (Chain.kind n i)).first⟩
def lastLabel (n : ℕ) (i : Chain.Block n) : Chain.Label n :=
  ⟨i,index (Chain.kind n i) (horizontalKind (Chain.kind n i)).last⟩

end ChainGeometry

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
