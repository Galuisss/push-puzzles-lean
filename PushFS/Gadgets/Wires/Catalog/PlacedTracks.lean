/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.StrongTracks
public import PushFS.Gadgets.Wires.Catalog.PlacedSemantics

/-! Actual complete storage certificates after padding an aligned finite physical glyph. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


variable {I : Instance} {L : Type} [Fintype L] {W H : ℕ}

noncomputable def placedAxisTracks (M : SlotMatching I L) (A : StrongTracks I)
    (dx dy : ℕ) (hx : dx+I.width≤W) (hy : dy+I.height≤H)
    (ha : ∀p, A.axes.name p≠.outside→BoundaryAligned (W:=W) (H:=H) dx dy p) :
    AxisTracks (placedAtlas M dx dy hx hy).puzzle where
  name:=paddedName dx dy hx hy A.axes.name
  supported:=(paddedClassifier dx dy hx hy (Polyline.axisClassifier A.axes) (placed_walls M dx dy hx hy) ha).supported
  displacement:=(paddedClassifier dx dy hx hy (Polyline.axisClassifier A.axes) (placed_walls M dx dy hx hy) ha).displacement
  active p hp:=by
    change p∈Finset.univ.map (placedAtlas M dx dy hx hy).source at hp
    obtain ⟨⟨i,l⟩,_,rfl⟩:=Finset.mem_map.mp hp
    change paddedName dx dy hx hy A.axes.name ((GridEmbedding.translate dx dy hx hy).cells (M.source l))≠.outside
    rw [paddedName_apply]
    intro he
    apply A.axes.active (M.source l)
    · rw [←M.source_image]
      exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
    · have hh : AxisTrack.shift dx dy .outside=.outside := rfl
      exact AxisTrack.shift_injective dx dy (he.trans hh.symm)
  separated p hp q hq _ d:=by
    change p∈Finset.univ.map (placedAtlas M dx dy hx hy).target at hp
    change q∈Finset.univ.map (placedAtlas M dx dy hx hy).target at hq
    obtain ⟨⟨i,l⟩,_,rfl⟩:=Finset.mem_map.mp hp
    obtain ⟨⟨j,k⟩,_,rfl⟩:=Finset.mem_map.mp hq
    intro hadj
    have hl : M.target l∈I.board.goals := by
      rw [←M.target_image]
      exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
    have hk : M.target k∈I.board.goals := by
      rw [←M.target_image]
      exact Finset.mem_map.mpr ⟨k,Finset.mem_univ _,rfl⟩
    exact A.sparse (M.target l) hl (M.target k) hk d
      ((Polyline.translate_adjacent_iff dx dy hx hy d _ _).mp hadj)

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
