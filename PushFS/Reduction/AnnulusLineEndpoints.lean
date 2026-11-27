/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusLineCollars
public import PushFS.Gadgets.Wires.Polyline.Endpoints

/-! Complete actual endpoint identities and canonical slot bounds for both long-line families. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def lineFirst (flip : Bool) (n : ℕ) (hn : 2301≤n) : lineLabels flip n :=
  match flip with
  | false => Polyline.ChainEnds.first n hn
  | true => FlippedChain.firstLabel n hn

def lineLast (flip : Bool) (n : ℕ) (hn : 2301≤n) : lineLabels flip n :=
  match flip with
  | false => Polyline.ChainEnds.last n hn
  | true => FlippedChain.lastLabel n

theorem line_first_position (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    ((lineMatching flip n hn a b).source (lineFirst flip n hn)).1.val=2+a.toNat ∧
    ((lineMatching flip n hn a b).source (lineFirst flip n hn)).2.val=10 := by
  cases flip
  · exact ⟨Polyline.ChainEnds.first_x n hn a,Chain.position_row n hn _ _⟩
  · change ((FlippedChain.slotMatching n hn a b).source (FlippedChain.firstLabel n hn)).1.val=_ ∧
      ((FlippedChain.slotMatching n hn a b).source (FlippedChain.firstLabel n hn)).2.val=_
    rw [FlippedChain.source_position]
    exact ⟨(FlippedChain.endpoints n hn a).1,FlippedChain.position_row n hn _ _⟩

theorem line_last_position (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    ((lineMatching flip n hn a b).source (lineLast flip n hn)).1.val=n+(if flip then 20 else 0)+a.toNat ∧
    ((lineMatching flip n hn a b).source (lineLast flip n hn)).2.val=10 := by
  cases flip
  · exact ⟨Polyline.ChainEnds.last_x n hn a,Chain.position_row n hn _ _⟩
  · change ((FlippedChain.slotMatching n hn a b).source (FlippedChain.lastLabel n)).1.val=_ ∧
      ((FlippedChain.slotMatching n hn a b).source (FlippedChain.lastLabel n)).2.val=_
    rw [FlippedChain.source_position]
    exact ⟨(FlippedChain.endpoints n hn a).2,FlippedChain.position_row n hn _ _⟩

/-- Every genuine line label lies on the one physical rail, two cells inside its false-phase end anchors. -/
theorem line_source_bounds (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (l : lineLabels flip n) :
    2+a.toNat≤((lineMatching flip n hn a b).source l).1.val ∧
      ((lineMatching flip n hn a b).source l).1.val≤n+(if flip then 20 else 0)+a.toNat ∧
      ((lineMatching flip n hn a b).source l).2.val=10 := by
  cases flip
  · have hh := Polyline.chain_phase_bounds n hn a l
    exact ⟨hh.1,hh.2,Chain.position_row n hn _ _⟩
  · change FlippedChain.Label n at l
    change 2+a.toNat≤((FlippedChain.slotMatching n hn a b).source l).1.val ∧
      ((FlippedChain.slotMatching n hn a b).source l).1.val≤n+20+a.toNat ∧
      ((FlippedChain.slotMatching n hn a b).source l).2.val=10
    rw [FlippedChain.source_position]
    exact ⟨(FlippedChain.position_bounds n hn a l).1,(FlippedChain.position_bounds n hn a l).2,
      FlippedChain.position_row n hn _ _⟩

private theorem line_target_source (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (l : lineLabels flip n) :
    (((lineMatching flip n hn a b).target l).1.val,((lineMatching flip n hn a b).target l).2.val)=
      (((lineMatching flip n hn b a).source l).1.val,((lineMatching flip n hn b a).source l).2.val) := by
  cases flip
  · rfl
  · change FlippedChain.Label n at l
    change (((FlippedChain.slotMatching n hn a b).target l).1.val,
      ((FlippedChain.slotMatching n hn a b).target l).2.val)=
      (((FlippedChain.slotMatching n hn b a).source l).1.val,
      ((FlippedChain.slotMatching n hn b a).source l).2.val)
    rw [FlippedChain.target_position n hn a b l,FlippedChain.source_position n hn b a l]

theorem line_target_bounds (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (l : lineLabels flip n) :
    2+b.toNat≤((lineMatching flip n hn a b).target l).1.val ∧
      ((lineMatching flip n hn a b).target l).1.val≤n+(if flip then 20 else 0)+b.toNat ∧
      ((lineMatching flip n hn a b).target l).2.val=10 := by
  have hx := congrArg Prod.fst (line_target_source flip n hn a b l)
  have hy := congrArg Prod.snd (line_target_source flip n hn a b l)
  have hb := line_source_bounds flip n hn b a l
  dsimp only at hx hy
  omega

end PushPuzzle.PushFS.Reduction.GateTileRouting
