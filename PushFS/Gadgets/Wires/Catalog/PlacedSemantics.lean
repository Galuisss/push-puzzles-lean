/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Placed

/-! Exact semantic padding of one complete real glyph, preserving its player, boxes, goals and genuine solutions. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


variable {I : Instance} {L : Type} [Fintype L] {W H : ℕ}
    (M : SlotMatching I L) (dx dy : ℕ) (hx : dx+I.width≤W) (hy : dy+I.height≤H)

theorem placed_walls : (GridEmbedding.translate dx dy hx hy).WallsAgree I.board (placedAtlas M dx dy hx hy).board :=
  (placedAtlas M dx dy hx hy).walls_agree 0

theorem placed_initial : (placedAtlas M dx dy hx hy).initial=
    (GridEmbedding.translate dx dy hx hy).extend ∅ I.initial := by
  apply State.ext
  · rfl
  change Finset.univ.map (placedAtlas M dx dy hx hy).source=I.initial.boxes.map _∪∅
  rw [Finset.union_empty]
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩,_,rfl⟩:=Finset.mem_map.mp hp
    apply Finset.mem_map.mpr
    refine ⟨M.source l,?_,rfl⟩
    rw [←M.source_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  · intro hp
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    rw [←M.source_image] at hq
    obtain ⟨l,_,rfl⟩:=Finset.mem_map.mp hq
    exact Finset.mem_map.mpr ⟨⟨0,l⟩,Finset.mem_univ _,rfl⟩

theorem placed_goals : (placedAtlas M dx dy hx hy).board.goals=
    I.board.goals.map (GridEmbedding.translate dx dy hx hy).cells := by
  change Finset.univ.map (placedAtlas M dx dy hx hy).target=_
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩,_,rfl⟩:=Finset.mem_map.mp hp
    apply Finset.mem_map.mpr
    refine ⟨M.target l,?_,rfl⟩
    rw [←M.target_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  · intro hp
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    rw [←M.target_image] at hq
    obtain ⟨l,_,rfl⟩:=Finset.mem_map.mp hq
    exact Finset.mem_map.mpr ⟨⟨0,l⟩,Finset.mem_univ _,rfl⟩

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
