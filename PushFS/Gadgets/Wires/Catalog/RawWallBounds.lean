/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Collars

/-! Actual complete wall supports of the seven finite-cell bitmaps. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The literal turn walls lie on its two protective arm strips. -/
private theorem turn_wall_bounds : ∀p : Turn.C, Turn.wallTest p=true→
    (8≤p.1.val ∧7≤p.2.val ∧p.2.val≤11) ∨ (8≤p.1.val ∧p.1.val≤12 ∧7≤p.2.val) := by decide +kernel

/-- Only these two thin positive arms can contain a wall in a native long L. -/
def RawWallRegion {w h : ℕ} (p : PushFS.Cell w h) : Prop :=
  (8≤p.1.val ∧8≤p.2.val ∧p.2.val≤12) ∨ (8≤p.1.val ∧p.1.val≤12 ∧8≤p.2.val)

theorem normal_wall_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {p : Polyline.L.C m n}
    (hp : p∈Polyline.L.walls m n hm hn) : RawWallRegion p := by
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      have hh:=Chain.walls_rows m hm q hq
      unfold RawWallRegion
      rw [Polyline.L.in_x,Polyline.L.in_y]
      omega
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      have hh:=turn_wall_bounds q ((Turn.template.mem_walls q).mp hq)
      unfold RawWallRegion
      rw [Polyline.L.turn_x,Polyline.L.turn_y]
      omega
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    have hh:=Chain.walls_rows n hn q hq
    have hy:=q.2.isLt
    unfold RawWallRegion
    rw [Polyline.L.out_x,Polyline.L.out_y]
    omega

theorem out_wall_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {p : Out.C m n}
    (hp : p∈Out.walls m n hm hn) : RawWallRegion p := by
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      have hh:=Chain.walls_rows m hm q hq
      unfold RawWallRegion
      rw [Out.in_x,Out.in_y]
      omega
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      have hh:=turn_wall_bounds q ((Turn.template.mem_walls q).mp hq)
      unfold RawWallRegion
      rw [Out.turn_x,Out.turn_y]
      omega
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    have hh:=Tail.walls_rows n hn q hq
    have hy:=q.2.isLt
    unfold RawWallRegion
    rw [Out.out_x,Out.out_y]
    omega

theorem in_wall_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {p : In.C m n}
    (hp : p∈In.walls m n hm hn) : RawWallRegion p := by
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      have hh:=Head.walls_rows m hm q hq
      unfold RawWallRegion
      rw [In.in_x,In.in_y]
      omega
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      have hh:=turn_wall_bounds q ((Turn.template.mem_walls q).mp hq)
      unfold RawWallRegion
      rw [In.turn_x,In.turn_y]
      omega
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    have hh:=Chain.walls_rows n hn q hq
    have hy:=q.2.isLt
    unfold RawWallRegion
    rw [In.out_x,In.out_y]
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
