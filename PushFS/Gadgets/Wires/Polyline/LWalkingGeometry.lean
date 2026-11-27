/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.LState
public import PushFS.Walking

/-! Literal free exterior corridors connecting the actual piece corners of the L board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline.L


set_option maxRecDepth 65536

variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

/-- Exact occupied incoming region, in every complete canonical phase. -/
theorem inBoxes_region (a : Bool) {p : C m n} (hp : p∈inBoxes m n hm hn a) : p.2.val=10 ∧ 41≤p.1.val := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [Chain.boxes_image] at hq
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
  have hx := chain_slot_bounds m hm (Chain.uniform m a) l
  rw [in_x,in_y,Chain.position_row]
  omega

/-- Exact occupied turn arms, retaining their real gap from the protected corner. -/
theorem turnBoxes_region (a : Bool) {p : C m n} (hp : p∈turnBoxes m n hm hn a) :
    (p.2.val=10 ∧ 11≤p.1.val ∧ p.1.val≤40) ∨ (p.1.val=10 ∧ 11≤p.2.val ∧ p.2.val≤40) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  have hh := turn_slot_bounds a i
  rw [turn_x,turn_y]
  omega

/-- Exact occupied outgoing region in every phase. -/
theorem outBoxes_region (a : Bool) {p : C m n} (hp : p∈outBoxes m n hm hn a) : p.1.val=10 ∧ 41≤p.2.val := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [Chain.boxes_image] at hq
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
  have hx := chain_slot_bounds n hn (Chain.uniform n a) l
  rw [out_x,out_y,Chain.position_row]
  omega

end PushPuzzle.PushFS.Gadgets.Wires.Polyline.L
