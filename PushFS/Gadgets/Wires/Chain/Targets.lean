/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Phase
public import PushFS.StaticTracks

/-! The actual chain has an injective physical box labelling and a static
component-preserving goal assignment for every pair of canonical phases. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096

theorem state_valid (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a : Phases n) :
    (state n hn a).Valid (board n hn goals) := by
  refine ⟨?_,boxes_floor n hn a,?_⟩
  · intro hp
    have hh := walls_rows n hn (hub n hn) hp
    change 3 = 8 ∨ 3 = 9 ∨ 3 = 11 ∨ 3 = 12 at hh
    omega
  · intro hp
    have hh := boxes_row n hn a hp
    change 3 = 10 at hh
    omega

theorem position_component (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a b : Phases n) (l : Label n) :
    SameComponent (board n hn goals) (position n hn a l) (position n hn b l) :=
  Tile.position_component_placed (kind n l.1) (a l.1) (b l.1) l.2
    (placement n hn l.1) (walls_exact n hn l.1)

theorem boxes_card (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) : (boxes n hn a).card = Fintype.card (Label n) := by
  rw [boxes_image,Finset.card_image_of_injective _ (position_injective n hn a),Finset.card_univ]

/-- A fully formed finite Push-1FS instance, with every box and goal physically present. -/
def puzzle (n : ℕ) (hn : 2301 ≤ n) (a b : Bool) : Instance where
  width := n+5
  height := 21
  board := board n hn (boxes n hn (uniform n b))
  initial := state n hn (uniform n a)
  goals_floor := (boxes_floor n hn (uniform n b)).symm
  initial_valid := state_valid n hn _ _
  boxes_eq_goals := (boxes_card n hn (uniform n a)).trans (boxes_card n hn (uniform n b)).symm

/-- Every source and target physical slot follows its actual static component. -/
def slotMatching (n : ℕ) (hn : 2301 ≤ n) (a b : Bool) : SlotMatching (puzzle n hn a b) (Label n) where
  source := ⟨position n hn (uniform n a), position_injective n hn _⟩
  target := ⟨position n hn (uniform n b), position_injective n hn _⟩
  source_image := by rw [Finset.map_eq_image]; exact (boxes_image n hn _).symm
  target_image := by rw [Finset.map_eq_image]; exact (boxes_image n hn _).symm
  connected := position_component n hn _ _ _

end PushPuzzle.PushFS.Gadgets.Wires.Chain
