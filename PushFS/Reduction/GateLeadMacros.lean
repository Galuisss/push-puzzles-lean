/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadState

/-! Whole real lead updates in the complete independently phased gate-plus-leads board. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires

def westExternal (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : Finset (C n) :=
  gateBoxes n kind a ∪ northBoxes kind n hn c.upper ∪ eastBoxes kind n hn (!c.right)

def northExternal (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : Finset (C n) :=
  gateBoxes n kind a ∪ westBoxes kind n hn c.left ∪ eastBoxes kind n hn (!c.right)

def eastExternal (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : Finset (C n) :=
  gateBoxes n kind a ∪ westBoxes kind n hn c.left ∪ northBoxes kind n hn c.upper

theorem west_fixed_neighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) (ha : a.left=false) :
    fixed (west kind n) (westExternal kind n hn a c) ⊆ Chain.neighbors n := by
  intro p hp
  have hp' := (mem_fixed _ _ p).mp hp
  rcases Finset.mem_union.mp hp' with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact west_gate_neighbor kind n a ha p q hq he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
      exact False.elim (west_ne_north kind n p q he.symm)
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (west_ne_east kind n p q he.symm)

theorem north_fixed_neighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) (ha : a.upper=false) :
    fixed (north kind n) (northExternal kind n hn a c) ⊆ Chain.neighbors n := by
  intro p hp
  have hp' := (mem_fixed _ _ p).mp hp
  rcases Finset.mem_union.mp hp' with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact north_gate_neighbor kind n a ha p q hq he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
      exact False.elim (west_ne_north kind n q p he)
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (north_ne_east kind n p q he.symm)

theorem east_fixed_neighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) (ha : a.right=true) :
    fixed (east kind n) (eastExternal kind n hn a c) ⊆ Chain.neighbors n := by
  intro p hp
  have hp' := (mem_fixed _ _ p).mp hp
  rcases Finset.mem_union.mp hp' with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact east_gate_neighbor kind n a ha p q hq he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
      exact False.elim (west_ne_east kind n q p he)
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (north_ne_east kind n q p he)

def atWest (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : State (2*n+101) (2*n+137) :=
  ⟨(west kind n).cells (Chain.hub n hn),boxes kind n hn a c⟩

def atNorth (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : State (2*n+101) (2*n+137) :=
  ⟨(north kind n).cells (Chain.hub n hn),boxes kind n hn a c⟩

def atEast (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : State (2*n+101) (2*n+137) :=
  ⟨(east kind n).cells (Chain.hub n hn),boxes kind n hn a c⟩

theorem place_west (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) (p : Chain.C n) :
    (west kind n).extend (westExternal kind n hn a c) ⟨p,Chain.boxes n hn (Chain.uniform n c.left)⟩=
      ⟨(west kind n).cells p,boxes kind n hn a c⟩ := by
  apply State.ext
  · rfl
  change westBoxes kind n hn c.left ∪
    ((gateBoxes n kind a ∪ northBoxes kind n hn c.upper) ∪ eastBoxes kind n hn (!c.right))=
      gateBoxes n kind a ∪ ((westBoxes kind n hn c.left ∪ northBoxes kind n hn c.upper) ∪ eastBoxes kind n hn (!c.right))
  ac_rfl

theorem place_north (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) (p : Chain.C n) :
    (north kind n).extend (northExternal kind n hn a c) ⟨p,Chain.boxes n hn (Chain.uniform n c.upper)⟩=
      ⟨(north kind n).cells p,boxes kind n hn a c⟩ := by
  apply State.ext
  · rfl
  change northBoxes kind n hn c.upper ∪
    ((gateBoxes n kind a ∪ westBoxes kind n hn c.left) ∪ eastBoxes kind n hn (!c.right))=
      gateBoxes n kind a ∪ ((westBoxes kind n hn c.left ∪ northBoxes kind n hn c.upper) ∪ eastBoxes kind n hn (!c.right))
  ac_rfl

theorem place_east (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) (p : Chain.C n) :
    (east kind n).extend (eastExternal kind n hn a c) ⟨p,Chain.boxes n hn (Chain.uniform n (!c.right))⟩=
      ⟨(east kind n).cells p,boxes kind n hn a c⟩ := by
  apply State.ext
  · rfl
  change eastBoxes kind n hn (!c.right) ∪
    ((gateBoxes n kind a ∪ westBoxes kind n hn c.left) ∪ northBoxes kind n hn c.upper)=
      gateBoxes n kind a ∪ ((westBoxes kind n hn c.left ∪ northBoxes kind n hn c.upper) ∪ eastBoxes kind n hn (!c.right))
  ac_rfl

end PushPuzzle.PushFS.Reduction.GateLead
