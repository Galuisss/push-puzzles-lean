/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadWalking
public import PushFS.Reduction.GatePropagation
public import PushFS.Reduction.GateBinding

/-! Full all-box storage semantics and the finite physical buffered-gate catalog. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead

open Gadgets Gadgets.Wires Turing.MultiTapeTM ComputableInPolyTime

set_option maxRecDepth 65536

private theorem chain_position_mem (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Chain.Label n) :
    Chain.position n hn (Chain.uniform n a) l ∈ Chain.boxes n hn (Chain.uniform n a) := by
  rw [Chain.boxes_image]
  exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩

theorem initial_boxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) :
    (atlas kind n hn a b).initial.boxes=boxes kind n hn a a := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩,_,rfl⟩ := Finset.mem_map.mp hp
    fin_cases i
    · apply Finset.mem_union_left
      apply Finset.mem_map.mpr
      refine ⟨Gates.position kind a l,?_,rfl⟩
      rw [← Gates.position_image]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_map.mpr ⟨_,chain_position_mem n hn a.left l,rfl⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨_,chain_position_mem n hn a.upper l,rfl⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨_,chain_position_mem n hn (!a.right) l,rfl⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
      rw [← Gates.position_image] at hq
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_map.mpr ⟨⟨0,l⟩,Finset.mem_univ _,rfl⟩
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
          rw [Chain.boxes_image] at hq
          obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
          exact Finset.mem_map.mpr ⟨⟨1,l⟩,Finset.mem_univ _,rfl⟩
        · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
          rw [Chain.boxes_image] at hq
          obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
          exact Finset.mem_map.mpr ⟨⟨2,l⟩,Finset.mem_univ _,rfl⟩
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
        rw [Chain.boxes_image] at hq
        obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_map.mpr ⟨⟨3,l⟩,Finset.mem_univ _,rfl⟩

theorem initial_state (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) :
    (atlas kind n hn a b).initial=state kind n hn a a :=
  State.ext rfl (initial_boxes kind n hn a b)

end PushPuzzle.PushFS.Reduction.GateLead
