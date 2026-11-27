/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.LState
public import PushFS.Gadgets.Wires.Polyline.Bounds

/-! Every actual foreign box visible at each L joint, in all phase assignments. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline.L


set_option maxHeartbeats 1000000

def inExternal (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset (C m n) :=
  turnBoxes m n hm hn (a 1) ∪ outBoxes m n hm hn (a 2)
def turnExternal (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset (C m n) :=
  inBoxes m n hm hn (a 0) ∪ outBoxes m n hm hn (a 2)
def outExternal (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset (C m n) :=
  inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1)

def inFixed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset (Chain.C m) :=
  Finset.univ.filter fun p => (inEmbed m n hm hn).cells p ∈ inExternal m n hm hn a
def turnFixed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset Turn.C :=
  Finset.univ.filter fun p => (turnRect m n hm hn).cells p ∈ turnExternal m n hm hn a
def outFixed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset (Chain.C n) :=
  Finset.univ.filter fun p => (outEmbed m n hm hn).cells p ∈ outExternal m n hm hn a

@[simp] theorem mem_inFixed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) (p : Chain.C m) :
    p∈inFixed m n hm hn a ↔ (inEmbed m n hm hn).cells p∈inExternal m n hm hn a := by simp [inFixed]
@[simp] theorem mem_turnFixed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) (p : Turn.C) :
    p∈turnFixed m n hm hn a ↔ (turnRect m n hm hn).cells p∈turnExternal m n hm hn a := by simp [turnFixed]
@[simp] theorem mem_outFixed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) (p : Chain.C n) :
    p∈outFixed m n hm hn a ↔ (outEmbed m n hm hn).cells p∈outExternal m n hm hn a := by simp [outFixed]

theorem external_floor (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (goals : Finset (C m n)) (a : Phases) :
    Disjoint (inExternal m n hm hn a) (board m n hm hn goals).walls ∧
    Disjoint (turnExternal m n hm hn a) (board m n hm hn goals).walls ∧
    Disjoint (outExternal m n hm hn a) (board m n hm hn goals).walls := by
  have hf := boxes_floor m n hm hn goals a
  change Disjoint ((inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1)) ∪ outBoxes m n hm hn (a 2))
    (board m n hm hn goals).walls at hf
  have hout := (Finset.disjoint_union_left.mp hf).2
  have hleft := (Finset.disjoint_union_left.mp hf).1
  have hin := (Finset.disjoint_union_left.mp hleft).1
  have hturn := (Finset.disjoint_union_left.mp hleft).2
  exact ⟨Finset.disjoint_union_left.mpr ⟨hturn,hout⟩,
    Finset.disjoint_union_left.mpr ⟨hin,hout⟩,hleft⟩

/-- With the turn high, its only box inside the incoming chain is that chain's real permitted neighbor. -/
theorem inFixed_neighbors (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) (ha : a 1=true) :
    inFixed m n hm hn a ⊆ Chain.neighbors m := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_inFixed m n hm hn a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [turn_x,in_x] at hx
    simp only [turn_y,in_y] at hy
    rw [ha] at hx hy
    have hi := turn_east_high i (by omega)
    rw [hi] at hx hy
    have hpx : p.1.val=m+3 := by have := p.1.isLt; change 39=38+(m+4-p.1.val) at hx; omega
    have hpy : p.2.val=10 := by change 1+9=p.2.val at hy; omega
    have heq : p=(⟨m+3,by omega⟩,10) := Prod.ext (Fin.ext hpx) (Fin.ext hpy)
    rw [heq]
    simp [Chain.neighbors]
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (in_out_disjoint m n hm hn p q he.symm)

/-- With the turn low, its southern endpoint is the outgoing chain's exact input neighbor. -/
theorem outFixed_neighbors (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) (ha : a 1=false) :
    outFixed m n hm hn a ⊆ Chain.neighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_outFixed m n hm hn a p).mp hp) with hp|hp
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (in_out_disjoint m n hm hn q p he)
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [turn_x,out_x] at hx
    simp only [turn_y,out_y] at hy
    rw [ha] at hx hy
    have hi := turn_south_low i (by omega)
    rw [hi] at hx hy
    have hpx : p.1.val=0 := by change 1+38=39+p.1.val at hy; omega
    have hpy : p.2.val=10 := by have := p.2.isLt; change 10=20-p.2.val at hx; omega
    have heq : p=(0,10) := Prod.ext (Fin.ext hpx) (Fin.ext hpy)
    rw [heq]
    simp [Chain.neighbors]

/-- The joint's two visible eastern low-phase boxes are precisely the full turn's allowed collar. -/
theorem turnFixed_neighbors (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases)
    (hi : a 0=false) (ho : a 2=true) : turnFixed m n hm hn a ⊆ Turn.template.neighbors := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_turnFixed m n hm hn a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    rw [hi,Chain.boxes_image] at hq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [in_x,turn_x] at hx
    simp only [in_y,turn_y,Chain.position_row] at hy
    have hbound := (Chain.position m hm (Chain.uniform m false) l).1.isLt
    have hlast := chain_right_low m hm l (by have := p.1.isLt; omega)
    change p ∈ {(42,9),(44,9)}
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hlast with hh|hh
    · left; apply Prod.ext <;> apply Fin.ext
      · change p.1.val=42; omega
      · change p.2.val=9; omega
    · right; apply Prod.ext <;> apply Fin.ext
      · change p.1.val=44; omega
      · change p.2.val=9; omega
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    rw [ho,Chain.boxes_image] at hq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [out_y,turn_y] at hy
    have hb := chain_phase_bounds n hn true l
    have hp := p.2.isLt
    simp only [Bool.toNat_true] at hb
    omega

/-- Arbitrary turn phases use only the incoming chain's five genuine walking collar slots. -/
theorem inFixed_allNeighbors (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) :
    inFixed m n hm hn a ⊆ Chain.allNeighbors m := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_inFixed m n hm hn a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [turn_x,in_x] at hx
    simp only [turn_y,in_y] at hy
    have hb := turn_slot_bounds (a 1) i
    have hpy : p.2.val=10 := by omega
    have hpx : m+2 ≤ p.1.val := by have := p.1.isLt; omega
    have hpbound := p.1.isLt
    simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
    omega
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (in_out_disjoint m n hm hn p q he.symm)

/-- Arbitrary turn phases use only the outgoing chain's two near walking collar slots. -/
theorem outFixed_allNeighbors (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) :
    outFixed m n hm hn a ⊆ Chain.allNeighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_outFixed m n hm hn a p).mp hp) with hp|hp
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (in_out_disjoint m n hm hn q p he)
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [turn_x,out_x] at hx
    simp only [turn_y,out_y] at hy
    have hb := turn_slot_bounds (a 1) i
    have hpy : p.2.val=10 := by have := p.2.isLt; omega
    have hpx : p.1.val≤1 := by omega
    simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
    omega

/-- Every mixed-phase foreign box in the turn's rectangle is on its genuine reserved rail set. -/
theorem turnFixed_reserved (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) :
    turnFixed m n hm hn a ⊆ Turn.template.reservedCells := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_turnFixed m n hm hn a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    rw [Chain.boxes_image] at hq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [in_x,turn_x] at hx
    simp only [in_y,turn_y,Chain.position_row] at hy
    have hb := chain_slot_bounds m hm (Chain.uniform m (a 0)) l
    have hpy : p.2.val=9 := by omega
    have hpx : 41 ≤ p.1.val := by have := (Chain.position m hm (Chain.uniform m (a 0)) l).1.isLt; omega
    rw [Template.mem_reserved]
    change Turn.reservedTest p=true
    unfold Turn.reservedTest
    rw [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨?_,?_,?_⟩
    · simp only [Turn.trackTest,decide_eq_true_eq]
      exact Or.inl ⟨hpy,by omega⟩
    · intro heq
      have heqX := congrArg (fun r : Turn.C => r.1.val) heq
      change p.1.val=32 at heqX
      omega
    · intro heq
      have heqX := congrArg (fun r : Turn.C => r.1.val) heq
      change p.1.val=33 at heqX
      omega
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    rw [Chain.boxes_image] at hq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun p : C m n => p.1.val) he
    have hy := congrArg (fun p : C m n => p.2.val) he
    simp only [out_x,turn_x,Chain.position_row] at hx
    simp only [out_y,turn_y] at hy
    have hb := chain_slot_bounds n hn (Chain.uniform n (a 2)) l
    have hpx : p.1.val=10 := by omega
    have hpy : 40 ≤ p.2.val := by omega
    rw [Template.mem_reserved]
    change Turn.reservedTest p=true
    unfold Turn.reservedTest
    rw [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨?_,?_,?_⟩
    · simp only [Turn.trackTest,decide_eq_true_eq]
      exact Or.inr ⟨hpx,by omega⟩
    · intro heq
      have heqX := congrArg (fun r : Turn.C => r.1.val) heq
      change p.1.val=32 at heqX
      omega
    · intro heq
      have heqX := congrArg (fun r : Turn.C => r.1.val) heq
      change p.1.val=33 at heqX
      omega

end PushPuzzle.PushFS.Gadgets.Wires.Polyline.L
