/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Data

/-! Exact physical endpoint identities in the three actual L variants before their complete-board D4 placement. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace Out

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n)

theorem source0 (a b : Phases) (l : Chain.Label m) : (atlas m n hm hn a b).source ⟨0,l⟩=
    (inEmbed m n hm hn).cells (Chain.position m hm (Chain.uniform m (a 0)) l) := rfl

theorem source2 (a b : Phases) (l : FlippedChain.Label n) : (atlas m n hm hn a b).source ⟨2,l⟩=
    (outEmbed m n hm hn).cells (FlippedChain.position n hn (a 2) l) := by
  change (outRect m n hm hn).cells ((outIso n).cells ((FlippedChain.slotMatching n hn (a 2) (b 2)).source l))=_
  rw [FlippedChain.source_position n hn (a 2) (b 2) l]
  rfl

def firstLabel : (i : Fin 3)×Labels m n i := ⟨0,Polyline.ChainEnds.first m hm⟩
def lastLabel : (i : Fin 3)×Labels m n i := ⟨2,FlippedChain.lastLabel n⟩

theorem first_coordinates (a b : Bool) :
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (firstLabel m n hm)).1.val+a.toNat=m+40 ∧
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (firstLabel m n hm)).2.val=10 := by
  change ((atlas m n hm hn _ _).source ⟨0,Polyline.ChainEnds.first m hm⟩).1.val+a.toNat=m+40 ∧ _
  rw [source0 m n hm hn _ _ _,in_x]
  change 38+(m+4-(Chain.position m hm (Chain.uniform m a) (Polyline.ChainEnds.first m hm)).1.val)+a.toNat=m+40 ∧ _
  rw [Polyline.ChainEnds.first_x]
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · omega
  · change ((atlas m n hm hn _ _).source ⟨0,Polyline.ChainEnds.first m hm⟩).2.val=10
    rw [source0 m n hm hn _ _ _,in_y,Chain.position_row]

theorem last_coordinates (a b : Bool) :
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (lastLabel m n)).1.val=10 ∧
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (lastLabel m n)).2.val=n+59+a.toNat := by
  change ((atlas m n hm hn _ _).source ⟨2,FlippedChain.lastLabel n⟩).1.val=10 ∧ _
  rw [source2 m n hm hn _ _ _,out_x]
  have hy:=FlippedChain.position_row n hn a (FlippedChain.lastLabel n)
  have hx:=(FlippedChain.endpoints n hn a).2
  constructor
  · change 20-(FlippedChain.position n hn a (FlippedChain.lastLabel n)).2.val=10
    omega
  · change ((atlas m n hm hn _ _).source ⟨2,FlippedChain.lastLabel n⟩).2.val=_
    rw [source2 m n hm hn _ _ _,out_y]
    change 39+(FlippedChain.position n hn a (FlippedChain.lastLabel n)).1.val=_
    omega

end Out
namespace In

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n)

theorem source0 (a b : Phases) (l : FlippedChain.Label m) : (atlas m n hm hn a b).source ⟨0,l⟩=
    (inEmbed m n hm hn).cells (FlippedChain.position m hm (a 0) l) := by
  change (inRect m n hm hn).cells ((inIso m).cells ((FlippedChain.slotMatching m hm (a 0) (b 0)).source l))=_
  rw [FlippedChain.source_position m hm (a 0) (b 0) l]
  rfl

theorem source2 (a b : Phases) (l : Chain.Label n) : (atlas m n hm hn a b).source ⟨2,l⟩=
    (outEmbed m n hm hn).cells (Chain.position n hn (Chain.uniform n (a 2)) l) := rfl

def firstLabel : (i : Fin 3)×Labels m n i := ⟨0,FlippedChain.firstLabel m hm⟩
def lastLabel : (i : Fin 3)×Labels m n i := ⟨2,Polyline.ChainEnds.last n hn⟩

theorem first_coordinates (a b : Bool) :
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (firstLabel m n hm)).1.val+a.toNat=m+60 ∧
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (firstLabel m n hm)).2.val=10 := by
  have hx:=(FlippedChain.endpoints m hm a).1
  have hy:=FlippedChain.position_row m hm a (FlippedChain.firstLabel m hm)
  have ha : a.toNat≤1 := by cases a <;> decide
  change ((atlas m n hm hn _ _).source ⟨0,FlippedChain.firstLabel m hm⟩).1.val+a.toNat=m+60 ∧ _
  rw [source0 m n hm hn _ _ _,in_x]
  constructor
  · change 38+(m+24-(FlippedChain.position m hm a (FlippedChain.firstLabel m hm)).1.val)+a.toNat=m+60
    omega
  · change ((atlas m n hm hn _ _).source ⟨0,FlippedChain.firstLabel m hm⟩).2.val=10
    rw [source0 m n hm hn _ _ _,in_y]
    change 20-(FlippedChain.position m hm a (FlippedChain.firstLabel m hm)).2.val=10
    omega

theorem last_coordinates (a b : Bool) :
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (lastLabel m n hn)).1.val=10 ∧
    ((atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (lastLabel m n hn)).2.val=n+39+a.toNat := by
  have hx:=Polyline.ChainEnds.last_x n hn a
  have hy:=Chain.position_row n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)
  change ((atlas m n hm hn _ _).source ⟨2,Polyline.ChainEnds.last n hn⟩).1.val=10 ∧ _
  rw [source2 m n hm hn _ _ _,out_x]
  constructor
  · change 20-(Chain.position n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)).2.val=10
    omega
  · change ((atlas m n hm hn _ _).source ⟨2,Polyline.ChainEnds.last n hn⟩).2.val=_
    rw [source2 m n hm hn _ _ _,out_y]
    change 39+(Chain.position n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)).1.val=_
    omega

end In

/-- The unchanged true complete L has the same exact raw endpoint identity convention. -/
theorem normal_first_coordinates (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (Polyline.L.inputLabel m n hm)).1.val+a.toNat=m+40 ∧
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (Polyline.L.inputLabel m n hm)).2.val=10 := by
  have hx:=Polyline.ChainEnds.first_x m hm a
  have hy:=Chain.position_row m hm (Chain.uniform m a) (Polyline.ChainEnds.first m hm)
  have ha : a.toNat≤1 := by cases a <;> decide
  change ((Polyline.L.atlas m n hm hn _ _).source ⟨0,Polyline.ChainEnds.first m hm⟩).1.val+a.toNat=m+40 ∧ _
  rw [Polyline.L.source0 m n hm hn _ _ _,Polyline.L.in_x]
  constructor
  · change 38+(m+4-(Chain.position m hm (Chain.uniform m a) (Polyline.ChainEnds.first m hm)).1.val)+a.toNat=m+40
    omega
  · change ((Polyline.L.atlas m n hm hn _ _).source ⟨0,Polyline.ChainEnds.first m hm⟩).2.val=10
    rw [Polyline.L.source0 m n hm hn _ _ _,Polyline.L.in_y]
    exact hy

theorem normal_last_coordinates (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (Polyline.L.outputLabel m n hn)).1.val=10 ∧
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (Polyline.L.outputLabel m n hn)).2.val=n+39+a.toNat := by
  have hx:=Polyline.ChainEnds.last_x n hn a
  have hy:=Chain.position_row n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)
  change ((Polyline.L.atlas m n hm hn _ _).source ⟨2,Polyline.ChainEnds.last n hn⟩).1.val=10 ∧ _
  rw [Polyline.L.source2 m n hm hn _ _ _,Polyline.L.out_x]
  constructor
  · change 20-(Chain.position n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)).2.val=10
    omega
  · change ((Polyline.L.atlas m n hm hn _ _).source ⟨2,Polyline.ChainEnds.last n hn⟩).2.val=_
    rw [Polyline.L.source2 m n hm hn _ _ _,Polyline.L.out_y]
    change 39+(Chain.position n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)).1.val=_
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
