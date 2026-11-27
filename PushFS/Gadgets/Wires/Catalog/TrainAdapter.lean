/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RawEndpoints

/-! The real arbitrary terminal-flipped train exposes the same complete physical replay interface as a plain train. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Tail


abbrev C:=FlippedChain.C
abbrev Label:=FlippedChain.Label
def uniform (_n : ℕ) (a : Bool):=a
abbrev walls:=FlippedChain.walls
abbrev board:=FlippedChain.board
abbrev position:=FlippedChain.position
def boxes (n : ℕ) (hn : 2301≤n) (a : Bool):=FlippedChain.boxes n hn (FlippedChain.uniform a)
def state (n : ℕ) (hn : 2301≤n) (a : Bool):=FlippedChain.state n hn (FlippedChain.uniform a)
def hub (n : ℕ) (_hn : 2301≤n):=FlippedChain.player n
abbrev corner:=FlippedChain.corner
abbrev neighbors:=FlippedChain.neighbors
abbrev allNeighbors:=FlippedChain.allNeighbors

theorem position_row (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Label n) : (position n hn a l).2.val=10 :=
  FlippedChain.position_row n hn a l

theorem slot_bounds (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Label n) :
    2≤(position n hn a l).1.val ∧ (position n hn a l).1.val≤n+21 := by
  change 2≤(FlippedChain.position n hn a l).1.val ∧ (FlippedChain.position n hn a l).1.val≤n+21
  have hh:=FlippedChain.position_bounds n hn a l
  have ha : a.toNat≤1 := by cases a <;> decide
  omega

theorem phase_bounds (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Label n) :
    2+a.toNat≤(position n hn (uniform n a) l).1.val ∧ (position n hn (uniform n a) l).1.val≤n+20+a.toNat :=
  FlippedChain.position_bounds n hn a l

theorem boxes_image (n : ℕ) (hn : 2301≤n) (a : Bool) : boxes n hn a=Finset.univ.image (position n hn a) := by
  change FlippedChain.boxes n hn (FlippedChain.uniform a)=_
  rw [←FlippedChain.initial_boxes n hn (FlippedChain.uniform a) (FlippedChain.uniform a)]
  change Finset.univ.map (FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform a)).source=_
  rw [Finset.map_eq_image]
  rfl

theorem boxes_floor (n : ℕ) (hn : 2301≤n) (a : Bool) : Disjoint (boxes n hn a) (walls n hn) :=
  FlippedChain.boxes_floor n hn (FlippedChain.uniform a) ∅

theorem walls_rows (n : ℕ) (hn : 2301≤n) (p : C n) (hp : p∈walls n hn) :
    p.2.val=8∨p.2.val=9∨p.2.val=11∨p.2.val=12 := FlippedChain.walls_rows n hn hp

theorem rail_guard (n : ℕ) (hn : 2301≤n) (x : Fin (n+25)) : (x,9)∈walls n hn ∨(x,11)∈walls n hn :=
  FlippedChain.rail_guard n hn x

theorem position_order (n : ℕ) (hn : 2301≤n) (a b : Bool) (i j : Label n)
    (h : (position n hn a i).1.val<(position n hn a j).1.val) :
    (position n hn b i).1.val<(position n hn b j).1.val := FlippedChain.position_order n hn a b i j h

theorem sparse_targets (n : ℕ) (hn : 2301≤n) (a : Bool) (i j : Label n) (d : Direction) :
    ¬Adjacent d (position n hn a i) (position n hn a j) := by
  have hi : position n hn a i∈FlippedChain.boxes n hn (FlippedChain.uniform a) := by
    change position n hn a i∈boxes n hn a
    rw [boxes_image]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hj : position n hn a j∈FlippedChain.boxes n hn (FlippedChain.uniform a) := by
    change position n hn a j∈boxes n hn a
    rw [boxes_image]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  exact FlippedChain.sparse_targets n hn a hi hj d

/-- Complete actual arbitrary-length FlippedChain replay with its real two endpoint neighbor slots. -/
theorem transition_placed {W H : ℕ} (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (fixed : Finset (C n)) (hf : fixed⊆neighbors n) (e : GridEmbedding (n+25) 21 W H)
    {B : Board W H} {outside : Finset (PushFS.Cell W H)} (hw : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀p,e.cells p∈outside →p∈fixed) (hfixed : ∀p∈fixed,e.cells p∈outside) (he : Disjoint outside B.walls) :
    Reachable B (some 1) ((state n hn a).place e outside) ((state n hn b).place e outside) :=
  FlippedChain.transition_placed n hn a b fixed hf e hw hinside hfixed he

/-- All actual corner walks retain every physical box and all five permitted walking-collar slots. -/
theorem corners_placed_allNeighbors {W H : ℕ} (n : ℕ) (hn : 2301≤n) (a : Bool) (i : Fin 4)
    (fixed : Finset (C n)) (hf : fixed⊆allNeighbors n) (e : GridEmbedding (n+25) 21 W H)
    {B : Board W H} {outside : Finset (PushFS.Cell W H)} (hw : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀p,e.cells p∈outside →p∈fixed) (hfixed : ∀p∈fixed,e.cells p∈outside) (he : Disjoint outside B.walls) :
    Reachable B (some 1) ((state n hn a).place e outside) ((⟨corner n i,boxes n hn a⟩ : State (n+25) 21).place e outside) ∧
    Reachable B (some 1) ((⟨corner n i,boxes n hn a⟩ : State (n+25) 21).place e outside) ((state n hn a).place e outside) :=
  FlippedChain.corners_placed n hn (FlippedChain.uniform a) i fixed hf e hw hinside hfixed he

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Tail
