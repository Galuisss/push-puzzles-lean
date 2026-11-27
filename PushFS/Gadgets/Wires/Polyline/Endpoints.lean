/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Chain
public import PushFS.Gadgets.Wires.Polyline.LOrder

/-! Exact physical identities at the exposed ends and both staggered seams. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


open Soundness

namespace ChainEnds

private theorem tile_first (b phase : Bool) :
    (Chain.Tile.position b phase (ChainGeometry.index b (ChainGeometry.horizontalKind b).first)).1.val=2+phase.toNat := by
  cases b <;> cases phase <;> rfl
private theorem tile_last (b phase : Bool) :
    (Chain.Tile.position b phase (ChainGeometry.index b (ChainGeometry.horizontalKind b).last)).1.val=Chain.Tile.span b+phase.toNat := by
  cases b <;> cases phase <;> rfl

def first (n : ℕ) (hn : 2301≤n) : Chain.Label n := ChainGeometry.firstLabel n (Chain.firstBlock n hn)
def last (n : ℕ) (hn : 2301≤n) : Chain.Label n := ChainGeometry.lastLabel n (Chain.lastBlock n hn)

theorem first_x (n : ℕ) (hn : 2301≤n) (phase : Bool) :
    (Chain.position n hn (Chain.uniform n phase) (first n hn)).1.val=2+phase.toNat := by
  change Chain.offset n (Chain.firstBlock n hn).val+_=2+phase.toNat
  dsimp only [first,ChainGeometry.firstLabel,Chain.uniform]
  rw [Chain.first_offset]
  simpa only [Nat.zero_add] using tile_first (Chain.kind n (Chain.firstBlock n hn)) phase

theorem last_x (n : ℕ) (hn : 2301≤n) (phase : Bool) :
    (Chain.position n hn (Chain.uniform n phase) (last n hn)).1.val=n+phase.toNat := by
  change Chain.offset n (Chain.lastBlock n hn).val+_=n+phase.toNat
  dsimp only [last,ChainGeometry.lastLabel,Chain.uniform]
  rw [tile_last]
  have hh := Chain.last_finish n hn
  omega

end ChainEnds
namespace L

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n)

def inLabels : Chain.Label m ↪ Label m n := ⟨fun l=>⟨0,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
def turnLabels : Fin 29 ↪ Label m n := ⟨fun l=>⟨1,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
def outLabels : Chain.Label n ↪ Label m n := ⟨fun l=>⟨2,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩

def inputLabel : Label m n := inLabels m n (ChainEnds.first m hm)
def inSeamLabel : Label m n := inLabels m n (ChainEnds.last m hm)
def outSeamLabel : Label m n := outLabels m n (ChainEnds.first n hn)
def outputLabel : Label m n := outLabels m n (ChainEnds.last n hn)

theorem in_seam_x (a : Bool) : (position m n hm hn a (inSeamLabel m n hm)).1.val+a.toNat=42 := by
  change (position m n hm hn a ⟨0,ChainEnds.last m hm⟩).1.val+a.toNat=42
  rw [position0 m n hm hn a (ChainEnds.last m hm),in_x,ChainEnds.last_x]
  have ha : a.toNat≤1 := by cases a <;> decide
  omega

theorem out_seam_y (a : Bool) : (position m n hm hn a (outSeamLabel m n hn)).2.val=41+a.toNat := by
  change (position m n hm hn a ⟨2,ChainEnds.first n hn⟩).2.val=41+a.toNat
  rw [position2 m n hm hn a (ChainEnds.first n hn),out_y,ChainEnds.first_x]
  omega

end L
end PushPuzzle.PushFS.Gadgets.Wires.Polyline
