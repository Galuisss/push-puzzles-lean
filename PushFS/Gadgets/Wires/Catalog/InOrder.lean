/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.InSparse
public import PushFS.Gadgets.Wires.Soundness.Local

/-! Every prescribed physical L target preserves the exact coordinate order of its source identity. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.In


abbrev Label (m n : ℕ) := (i : Fin 3) × Labels m n i

variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

def position (phase : Bool) (l : Label m n) : C m n := (atlas m n hm hn (uniform phase) (uniform phase)).source l

theorem source_position (a b : Bool) (l : Label m n) :
    (atlas m n hm hn (uniform a) (uniform b)).source l=position m n hm hn a l := by
  rcases l with ⟨i,l⟩
  have cases3 (i : Fin 3) : i=0∨i=1∨i=2 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases3 i with rfl|rfl|rfl
  · change (atlas m n hm hn (uniform a) (uniform b)).source ⟨0,l⟩=(atlas m n hm hn (uniform a) (uniform a)).source ⟨0,l⟩
    rw [source0 m n hm hn _ _ l,source0 m n hm hn _ _ l]
  · rfl
  · rfl

theorem target_position (a b : Bool) (l : Label m n) :
    (atlas m n hm hn (uniform a) (uniform b)).target l=position m n hm hn b l := by
  rw [target_source_global]
  exact source_position m n hm hn b a l

theorem position0 (phase : Bool) (l : Tail.Label m) : position m n hm hn phase ⟨0,l⟩=
    (inEmbed m n hm hn).cells (Tail.position m hm (Tail.uniform m phase) l) := source0 m n hm hn _ _ l

theorem position1 (phase : Bool) (l : Fin 29) : position m n hm hn phase ⟨1,l⟩=
    (turnRect m n hm hn).cells (Turn.template.position phase l) := rfl

theorem position2 (phase : Bool) (l : Chain.Label n) : position m n hm hn phase ⟨2,l⟩=
    (outEmbed m n hm hn).cells (Chain.position n hn (Chain.uniform n phase) l) := rfl

private theorem position0_region (phase : Bool) (l : Tail.Label m) :
    (position m n hm hn phase ⟨0,l⟩).2.val=10 ∧ 41≤(position m n hm hn phase ⟨0,l⟩).1.val := by
  rw [position0]
  have hb := Tail.slot_bounds m hm (Tail.uniform m phase) l
  rw [in_x,in_y,Tail.position_row m hm (Tail.uniform m phase) l]
  omega

private theorem position1_region (phase : Bool) (l : Fin 29) :
    10≤(position m n hm hn phase ⟨1,l⟩).1.val ∧ (position m n hm hn phase ⟨1,l⟩).1.val≤40 ∧
    10≤(position m n hm hn phase ⟨1,l⟩).2.val ∧ (position m n hm hn phase ⟨1,l⟩).2.val≤40 := by
  rw [position1,turn_x,turn_y]
  have hb := Polyline.turn_slot_bounds phase l
  omega

private theorem position2_region (phase : Bool) (l : Chain.Label n) :
    (position m n hm hn phase ⟨2,l⟩).1.val=10 ∧ 41≤(position m n hm hn phase ⟨2,l⟩).2.val := by
  rw [position2]
  have hb := Polyline.chain_slot_bounds n hn (Chain.uniform n phase) l
  rw [out_x,out_y,Chain.position_row]
  omega

private theorem turn_col_anchor (a : Bool) : (Turn.template.position a 14).1.val=10 := by cases a <;> rfl
private theorem turn_row_anchor (a : Bool) : (Turn.template.position a 0).2.val=9 := by cases a <;> rfl

/-- All physical source/target x-order relations are preserved, including across the staggered L seams. -/
theorem position_order_x (a b : Bool) (l k : Label m n)
    (h : (position m n hm hn a l).1.val<(position m n hm hn a k).1.val) :
    (position m n hm hn b l).1.val<(position m n hm hn b k).1.val := by
  rcases l with ⟨i,l⟩
  rcases k with ⟨j,k⟩
  have cases3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases3 i with rfl|rfl|rfl <;> rcases cases3 j with rfl|rfl|rfl
  · rw [position0 m n hm hn a l,position0 m n hm hn a k,in_x,in_x] at h
    rw [position0 m n hm hn b l,position0 m n hm hn b k,in_x,in_x]
    have hla := Tail.slot_bounds m hm (Tail.uniform m a) l
    have hka := Tail.slot_bounds m hm (Tail.uniform m a) k
    have hlb := Tail.slot_bounds m hm (Tail.uniform m b) l
    have hkb := Tail.slot_bounds m hm (Tail.uniform m b) k
    have hraw : (Tail.position m hm (Tail.uniform m a) k).1.val<(Tail.position m hm (Tail.uniform m a) l).1.val := by omega
    have hb := Tail.position_order m hm (Tail.uniform m a) (Tail.uniform m b) k l hraw
    omega
  · have hl := position0_region m n hm hn a l; have hk := position1_region m n hm hn a k; omega
  · have hl := position0_region m n hm hn a l; have hk := position2_region m n hm hn a k; omega
  · have hl := position1_region m n hm hn b l; have hk := position0_region m n hm hn b k; omega
  · rw [position1 m n hm hn a l,position1 m n hm hn a k,turn_x,turn_x] at h
    rw [position1 m n hm hn b l,position1 m n hm hn b k,turn_x,turn_x]
    exact Soundness.slots_order_x .turn a b l k h
  · have hl := position1_region m n hm hn a l; have hk := position2_region m n hm hn a k; omega
  · have hl := position2_region m n hm hn b l; have hk := position0_region m n hm hn b k; omega
  · rw [position2 m n hm hn a l,position1 m n hm hn a k,out_x,turn_x,Chain.position_row n hn (Chain.uniform n a) l] at h
    rw [position2 m n hm hn b l,position1 m n hm hn b k,out_x,turn_x,Chain.position_row n hn (Chain.uniform n b) l]
    have hraw : (Turn.template.position a 14).1.val<(Turn.template.position a k).1.val := by rw [turn_col_anchor]; omega
    have hb := Soundness.slots_order_x .turn a b (14 : Fin 29) k hraw
    change (Turn.template.position b 14).1.val < (Turn.template.position b k).1.val at hb
    rw [turn_col_anchor] at hb
    omega
  · have hl := position2_region m n hm hn a l; have hk := position2_region m n hm hn a k; omega

/-- The same static fact holds for y-order, including every turn/tail joint. -/
theorem position_order_y (a b : Bool) (l k : Label m n)
    (h : (position m n hm hn a l).2.val<(position m n hm hn a k).2.val) :
    (position m n hm hn b l).2.val<(position m n hm hn b k).2.val := by
  rcases l with ⟨i,l⟩
  rcases k with ⟨j,k⟩
  have cases3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases3 i with rfl|rfl|rfl <;> rcases cases3 j with rfl|rfl|rfl
  · have hl := position0_region m n hm hn a l; have hk := position0_region m n hm hn a k; omega
  · rw [position0 m n hm hn a l,position1 m n hm hn a k,in_y,turn_y,Tail.position_row m hm (Tail.uniform m a) l] at h
    rw [position0 m n hm hn b l,position1 m n hm hn b k,in_y,turn_y,Tail.position_row m hm (Tail.uniform m b) l]
    have hraw : (Turn.template.position a 0).2.val<(Turn.template.position a k).2.val := by rw [turn_row_anchor]; omega
    have hb := Soundness.slots_order_y .turn a b (0 : Fin 29) k hraw
    change (Turn.template.position b 0).2.val < (Turn.template.position b k).2.val at hb
    rw [turn_row_anchor] at hb
    omega
  · have hl := position0_region m n hm hn b l; have hk := position2_region m n hm hn b k; omega
  · have hl := position1_region m n hm hn a l; have hk := position0_region m n hm hn a k; omega
  · rw [position1 m n hm hn a l,position1 m n hm hn a k,turn_y,turn_y] at h
    rw [position1 m n hm hn b l,position1 m n hm hn b k,turn_y,turn_y]
    have hraw : (Turn.template.position a l).2.val<(Turn.template.position a k).2.val := by omega
    have hb := Soundness.slots_order_y .turn a b l k hraw
    change (Turn.template.position b l).2.val<(Turn.template.position b k).2.val at hb
    omega
  · have hl := position1_region m n hm hn b l; have hk := position2_region m n hm hn b k; omega
  · have hl := position2_region m n hm hn a l; have hk := position0_region m n hm hn a k; omega
  · have hl := position2_region m n hm hn a l; have hk := position1_region m n hm hn a k; omega
  · rw [position2 m n hm hn a l,position2 m n hm hn a k,out_y,out_y] at h
    rw [position2 m n hm hn b l,position2 m n hm hn b k,out_y,out_y]
    have hraw : (Chain.position n hn (Chain.uniform n a) l).1.val<(Chain.position n hn (Chain.uniform n a) k).1.val := by omega
    have hb := Chain.position_order n hn (Chain.uniform n a) (Chain.uniform n b) l k hraw
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
