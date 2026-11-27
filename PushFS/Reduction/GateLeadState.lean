/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadAtlas
public import PushFS.Gadgets.Wires.Chain.CoveredPlacement

/-! Independent gate and lead phases on the one actual four-piece wall board. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

def zero : Gates.Signals := ⟨false,false,false⟩

def gateBoxes (n : ℕ) (kind : Bool) (a : Gates.Signals) : Finset (C n) :=
  (Gates.canonicalBoxes kind a).map (gate n).cells

def westBoxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Bool) : Finset (C n) :=
  (Chain.boxes n hn (Chain.uniform n a)).map (west kind n).cells

def northBoxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Bool) : Finset (C n) :=
  (Chain.boxes n hn (Chain.uniform n a)).map (north kind n).cells

def eastBoxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Bool) : Finset (C n) :=
  (Chain.boxes n hn (Chain.uniform n a)).map (east kind n).cells

/-- The lead phase triple uses the gate's left/upper/right flag convention. -/
def leadBoxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (c : Gates.Signals) : Finset (C n) :=
  westBoxes kind n hn c.left ∪ northBoxes kind n hn c.upper ∪ eastBoxes kind n hn (!c.right)

/-- Every auxiliary box remains present while the gate and its leads propagate independently. -/
def boxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : Finset (C n) :=
  gateBoxes n kind a ∪ leadBoxes kind n hn c

def state (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : State (2*n+101) (2*n+137) :=
  ⟨player n,boxes kind n hn a c⟩

/-- The exact local preimage of real external boxes. -/
def fixed {w h W H : ℕ} (e : GridEmbedding w h W H) (xs : Finset (Cell W H)) : Finset (Cell w h) :=
  Finset.univ.filter fun p => e.cells p ∈ xs

@[simp] theorem mem_fixed {w h W H : ℕ} (e : GridEmbedding w h W H) (xs : Finset (Cell W H)) (p : Cell w h) :
    p ∈ fixed e xs ↔ e.cells p ∈ xs := by simp [fixed]

/-- Actual chain inventories discharge the gate's complete collar condition. -/
theorem gate_fixed_neighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (c : Gates.Signals) :
    fixed (gate n) (leadBoxes kind n hn c) ⊆ Gates.boundaryNeighbors kind c := by
  intro p hp
  have hp' := (mem_fixed _ _ p).mp hp
  rcases Finset.mem_union.mp hp' with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact west_box_neighbor kind n hn c q p hq he
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact north_box_neighbor kind n hn c q p hq he
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    exact east_box_neighbor kind n hn c q p hq he

theorem place_gate (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) :
    (gate n).extend (leadBoxes kind n hn c) (Gates.canonical kind a)=state kind n hn a c := rfl

end PushPuzzle.PushFS.Reduction.GateLead
