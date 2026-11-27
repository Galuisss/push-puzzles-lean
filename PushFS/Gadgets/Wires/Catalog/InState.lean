/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.HeadAdapter
public import Mathlib.Data.Fin.VecNotation

/-! All actual independently phased box sets of the assembled physical L connector. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.In


set_option maxHeartbeats 1000000

/-- Incoming, turn and outgoing phase, respectively. -/
def phases (i t o : Bool) : Phases := ![i,t,o]
def uniform (a : Bool) : Phases := fun _ => a

def inBoxes (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Bool) : Finset (C m n) :=
  (Head.boxes m hm (Head.uniform m a)).map (inEmbed m n hm hn).cells

def turnBoxes (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Bool) : Finset (C m n) :=
  (Turn.template.boxes a).map (turnRect m n hm hn).cells

def outBoxes (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Bool) : Finset (C m n) :=
  (Chain.boxes n hn (Chain.uniform n a)).map (outEmbed m n hm hn).cells

def boxes (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : Finset (C m n) :=
  inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1) ∪ outBoxes m n hm hn (a 2)

def state (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a : Phases) : State (m+63) (n+44) :=
  ⟨player m n,boxes m n hm hn a⟩

theorem source1 (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Phases) (l : Fin 29) :
    (atlas m n hm hn a b).source ⟨1,l⟩=(turnRect m n hm hn).cells (Turn.template.position (a 1) l) := rfl

/-- Atlas ownership enumerates exactly the concrete union of all three complete physical box sets. -/
theorem initial_boxes (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) :
    (atlas m n hm hn a b).initial.boxes=boxes m n hm hn a := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩,_,rfl⟩ := Finset.mem_map.mp hp
    have cases3 (i : Fin 3) : i=0∨i=1∨i=2 := by have := i.isLt; simp only [Fin.ext_iff]; omega
    rcases cases3 i with rfl|rfl|rfl
    · rw [source0 m n hm hn a b l]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_map.mpr
      refine ⟨_,?_,rfl⟩
      change FlippedChain.position m hm (a 0) l∈Tail.boxes m hm (a 0)
      rw [Tail.boxes_image m hm (a 0)]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
    · change (turnRect m n hm hn).cells (Turn.template.position (a 1) l) ∈ _
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨_,Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩,rfl⟩
    · change (outEmbed m n hm hn).cells (Chain.position n hn (Chain.uniform n (a 2)) l) ∈ _
      apply Finset.mem_union_right
      apply Finset.mem_map.mpr
      refine ⟨_,?_,rfl⟩
      rw [Chain.boxes_image]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
        change q∈Tail.boxes m hm (a 0) at hq
        rw [Tail.boxes_image m hm (a 0)] at hq
        obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_map.mpr ⟨⟨0,l⟩,Finset.mem_univ _,source0 m n hm hn a b l⟩
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
        obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_map.mpr ⟨⟨1,l⟩,Finset.mem_univ _,source1 m n hm hn a b l⟩
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
      rw [Chain.boxes_image] at hq
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_map.mpr ⟨⟨2,l⟩,Finset.mem_univ _,source2 m n hm hn a b l⟩

theorem initial_state (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) :
    (atlas m n hm hn a b).initial=state m n hm hn a := State.ext rfl (initial_boxes m n hm hn a b)

/-- The literal union of the two long chains and the guarded turn. -/
def walls (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) : Finset (C m n) :=
  (Head.walls m hm).map (inEmbed m n hm hn).cells ∪
    Turn.template.walls.map (turnRect m n hm hn).cells ∪
    (Chain.walls n hn).map (outEmbed m n hm hn).cells

/-- The atlas has exactly the literal wall union, independently of endpoint phases. -/
theorem atlas_walls (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) :
    (atlas m n hm hn a b).walls=walls m n hm hn := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    fin_cases i
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨r,rfl⟩ := (inIso m).cells.surjective q
      change (inEmbed m n hm hn).cells r ∈ _
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_map.mpr ⟨r,(in_walls m n hm hn a b r).mp hq,rfl⟩))
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hi
      change (turnRect m n hm hn).cells q ∈ _
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨q,hq,rfl⟩))
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨r,rfl⟩ := (outIso n).cells.surjective q
      change (outEmbed m n hm hn).cells r ∈ _
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨r,(out_walls m n hm hn a b r).mp hq,rfl⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hp with hp|hp
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
        exact Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,Finset.mem_map.mpr
          ⟨(inIso m).cells q,(in_walls m n hm hn a b q).mpr hq,rfl⟩⟩
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
        exact Finset.mem_biUnion.mpr ⟨1,Finset.mem_univ _,Finset.mem_map.mpr ⟨q,hq,rfl⟩⟩
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
      exact Finset.mem_biUnion.mpr ⟨2,Finset.mem_univ _,Finset.mem_map.mpr
        ⟨(outIso n).cells q,(out_walls m n hm hn a b q).mpr hq,rfl⟩⟩

/-- Actual walls do not depend on the endpoint phase assignment. -/
theorem walls_eq (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b c d : Phases) :
    (atlas m n hm hn a b).walls=(atlas m n hm hn c d).walls :=
  (atlas_walls m n hm hn a b).trans (atlas_walls m n hm hn c d).symm

/-- A fixed board carries the true three-piece wall union and an arbitrary complete goal set. -/
def board (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (goals : Finset (C m n)) : Board (m+63) (n+44) :=
  ⟨walls m n hm hn,goals⟩

/-- Exact original-coordinate wall agreement for the reflected incoming chain. -/
theorem in_walls_agree (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (goals : Finset (C m n)) :
    (inEmbed m n hm hn).WallsAgree (Head.board m hm ∅) (board m n hm hn goals) := by
  intro p
  have hh := (atlas m n hm hn (uniform false) (uniform false)).walls_agree 0 ((inIso m).cells p)
  change (inEmbed m n hm hn).cells p ∈ (atlas m n hm hn (uniform false) (uniform false)).walls ↔
    (inIso m).cells p ∈ (piece m n hm hn (uniform false) (uniform false) 0).board.walls at hh
  rw [atlas_walls] at hh
  exact hh.trans (in_walls m n hm hn _ _ p)

/-- Exact original-coordinate wall agreement for the guarded turn. -/
theorem turn_walls_agree (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (goals : Finset (C m n)) :
    (turnRect m n hm hn).WallsAgree (Turn.template.board ∅) (board m n hm hn goals) := by
  intro p
  have hh := (atlas m n hm hn (uniform false) (uniform false)).walls_agree 1 p
  change (turnRect m n hm hn).cells p ∈ (atlas m n hm hn (uniform false) (uniform false)).walls ↔ p∈Turn.template.walls at hh
  rw [atlas_walls] at hh
  exact hh

/-- Exact original-coordinate wall agreement for the clockwise outgoing chain. -/
theorem out_walls_agree (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (goals : Finset (C m n)) :
    (outEmbed m n hm hn).WallsAgree (Chain.board n hn ∅) (board m n hm hn goals) := by
  intro p
  have hh := (atlas m n hm hn (uniform false) (uniform false)).walls_agree 2 ((outIso n).cells p)
  change (outEmbed m n hm hn).cells p ∈ (atlas m n hm hn (uniform false) (uniform false)).walls ↔
    (outIso n).cells p ∈ (piece m n hm hn (uniform false) (uniform false) 2).board.walls at hh
  rw [atlas_walls] at hh
  exact hh.trans (out_walls m n hm hn _ _ p)

/-- All independently phased physical boxes remain actual floor boxes on the fixed union board. -/
theorem boxes_floor (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (goals : Finset (C m n)) (a : Phases) :
    Disjoint (boxes m n hm hn a) (board m n hm hn goals).walls := by
  have hh := (atlas m n hm hn a (uniform false)).initial_valid.2.1
  rw [initial_boxes] at hh
  change Disjoint (boxes m n hm hn a) (atlas m n hm hn a (uniform false)).walls at hh
  rw [atlas_walls] at hh
  exact hh

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
