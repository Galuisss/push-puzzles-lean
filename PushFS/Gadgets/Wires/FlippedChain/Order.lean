/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Statics
public import PushFS.Gadgets.Wires.Soundness.Line

/-! Static physical source/target order, complete rail SCC and exact endpoint identities. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

variable (n : ℕ) (hn : 2301≤n)

def position (a : Bool) (l : Label n) : C n := (atlas n hn (uniform a) (uniform a)).source l

theorem position0 (a : Bool) (l : Chain.Label n) : position n hn a ⟨0,l⟩=
    (chainPlacement n).cells (Chain.position n hn (Chain.uniform n a) l) := rfl

theorem position1 (a : Bool) (i : Fin 9) : position n hn a ⟨1,i⟩=
    (flipPlacement n).cells (Flip.template.position a i) := rfl

theorem source_position (a b : Bool) (l : Label n) : (slotMatching n hn a b).source l=position n hn a l := by
  rcases l with ⟨i,l⟩
  have cases2 (i : Fin 2) : i=0∨i=1 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases2 i with rfl|rfl <;> rfl

theorem target_position (a b : Bool) (l : Label n) : (slotMatching n hn a b).target l=position n hn b l := by
  change (atlas n hn (uniform a) (uniform b)).target l=_
  rw [target_source_global]
  exact source_position n hn b a l

theorem position_row (a : Bool) (l : Label n) : (position n hn a l).2.val=10 := by
  rcases l with ⟨i,l⟩
  have cases2 (i : Fin 2) : i=0∨i=1 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases2 i with rfl|rfl
  · rw [position0 n hn a l,chain_y,Chain.position_row n hn (Chain.uniform n a) l]
  · rw [position1 n hn a l,flip_y]
    exact (flip_bounds a l).1

theorem position_bounds (a : Bool) (l : Label n) :
    2+a.toNat≤(position n hn a l).1.val ∧ (position n hn a l).1.val≤n+20+a.toNat := by
  rcases l with ⟨i,l⟩
  have cases2 (i : Fin 2) : i=0∨i=1 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases2 i with rfl|rfl
  · rw [position0 n hn a l,chain_x]
    have hh:=Polyline.chain_phase_bounds n hn a l
    omega
  · rw [position1 n hn a l,flip_x]
    have hh:=flip_bounds a l
    omega

/-- The actual complete source/goal correspondence preserves every strict x-order. -/
theorem position_order (a b : Bool) (l k : Label n)
    (h : (position n hn a l).1.val<(position n hn a k).1.val) :
    (position n hn b l).1.val<(position n hn b k).1.val := by
  rcases l with ⟨i,l⟩
  rcases k with ⟨j,k⟩
  have cases2 (i : Fin 2) : i=0∨i=1 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases2 i with rfl|rfl <;> rcases cases2 j with rfl|rfl
  · rw [position0 n hn a l,position0 n hn a k,chain_x,chain_x] at h
    rw [position0 n hn b l,position0 n hn b k,chain_x,chain_x]
    exact Chain.position_order n hn (Chain.uniform n a) (Chain.uniform n b) l k h
  · rw [position0 n hn b l,position1 n hn b k,chain_x,flip_x]
    have hl:=Polyline.chain_phase_bounds n hn b l
    have hk:=flip_bounds b k
    omega
  · rw [position1 n hn a l,position0 n hn a k,flip_x,chain_x] at h
    have hl:=flip_bounds a l
    have hk:=Polyline.chain_phase_bounds n hn a k
    omega
  · rw [position1 n hn a l,position1 n hn a k,flip_x,flip_x] at h
    rw [position1 n hn b l,position1 n hn b k,flip_x,flip_x]
    have ha : (Flip.template.position a l).1.val<(Flip.template.position a k).1.val := by omega
    have hb:=Soundness.slots_order_x .flip a b l k ha
    change (Flip.template.position b l).1.val<(Flip.template.position b k).1.val at hb
    omega

theorem row_floor (x : Fin (n+25)) : (x,10)∉walls n hn := by
  intro hw
  have hh:=walls_rows n hn hw
  change 10=8∨10=9∨10=11∨10=12 at hh
  omega

/-- All actual complete canonical labels, across the real five-column seam, lie in one true static SCC. -/
theorem slots_component (a : Bool) (l k : Label n) :
    SameComponent (board n hn ∅) (position n hn a l) (position n hn a k) := by
  have hp (l : Label n) : 0<(position n hn a l).1.val ∧ (position n hn a l).1.val+1<n+25 := by
    have hh:=position_bounds n hn a l
    have ha : a.toNat≤1 := by cases a <;> decide
    omega
  have he (l : Label n) : position n hn a l=((position n hn a l).1,10) :=
    Prod.ext rfl (Fin.ext (position_row n hn a l))
  rw [he l,he k]
  exact Soundness.horizontal_component 10 (row_floor n hn) _ _ (hp l) (hp k)

def chainLabels : Chain.Label n↪Label n := ⟨fun l=>⟨0,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
def flipLabels : Fin 9↪Label n := ⟨fun i=>⟨1,i⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
def firstLabel : Label n := chainLabels n (Polyline.ChainEnds.first n hn)
def lastChainLabel : Label n := chainLabels n (Polyline.ChainEnds.last n hn)
def firstFlipLabel : Label n := flipLabels n 0
def lastLabel : Label n := flipLabels n 8

theorem endpoints (a : Bool) : (position n hn a (firstLabel n hn)).1.val=2+a.toNat ∧
    (position n hn a (lastLabel n)).1.val=n+20+a.toNat := by
  constructor
  · change (position n hn a ⟨0,Polyline.ChainEnds.first n hn⟩).1.val=_
    rw [position0 n hn a _,chain_x,Polyline.ChainEnds.first_x]
  · change (position n hn a ⟨1,(8 : Fin 9)⟩).1.val=_
    rw [position1 n hn a _,flip_x,(Flip.endpoint_slots a).2]
    simp only [Flip.span,Nat.add_assoc]

/-- Total physical translation distance of the near and far seam anchors. -/
def span := n+20

def port (i : Fin 2) : C n := if i=0 then (⟨2,by omega⟩,10) else (⟨n+22,by omega⟩,10)

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
