/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Basic
public import PushFS.Placement

/-! Complete physical indexing, exact storage targets and placement of certified wire tiles. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Template


variable {w h count W H : ℕ} {T : Template w h count}

theorem Checked.state_valid (hc : T.Checked) (phase : Bool) (goals : Finset (Cell w h)) :
    (T.state phase).Valid (T.board goals) := by
  have hs := hc.state_valid_guard phase
  exact ⟨fun h => hs.1 (Finset.mem_union_left _ h), hc.boxes_floor phase, hs.2.2⟩

/-- Exact unlabelled storage between two complete canonical phases. -/
def Checked.storageInstance (hc : T.Checked) (a b : Bool) : Instance where
  width := w
  height := h
  board := T.board (T.boxes b)
  initial := T.state a
  goals_floor := (hc.boxes_floor b).symm
  initial_valid := hc.state_valid a _
  boxes_eq_goals := (hc.boxes_card a).trans (hc.boxes_card b).symm

/-- All source and goal boxes are paired by their verified physical slot paths. -/
def Checked.slotMatching (hc : T.Checked) (a b : Bool) :
    SlotMatching (hc.storageInstance a b) (Fin count) where
  source := ⟨T.position a, hc.injective a⟩
  target := ⟨T.position b, hc.injective b⟩
  source_image := by rw [Finset.map_eq_image]; rfl
  target_image := by rw [Finset.map_eq_image]; rfl
  connected := hc.position_component a b _

/-- Both static paths of a physical slot survive the same placement. -/
theorem Checked.position_component_placed (hc : T.Checked) (a b : Bool) (i : Fin count)
    (e : GridEmbedding w h W H) {B : Board W H} (hw : e.WallsAgree (T.board ∅) B) :
    SameComponent B (e.cells (T.position a i)) (e.cells (T.position b i)) := by
  have hs := hc.position_component a b ∅ i
  exact ⟨GridEmbedding.staticReach hw hs.1, GridEmbedding.staticReach hw hs.2⟩

end PushPuzzle.PushFS.Gadgets.Wires.Template
