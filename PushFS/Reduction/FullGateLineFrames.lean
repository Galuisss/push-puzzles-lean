/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateSelectedSlots
public import PushFS.Reduction.AnnulusShortFrames

/-! Every actual independently mixed foreign inventory meets an annular long line only in its checked walking collar. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside

def lineAllNeighbors (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Finset (Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height) :=
  match flip with
  | false=>Chain.allNeighbors n
  | true=>FlippedChain.allNeighbors n

private theorem chainMask_complete (n : ℕ) (p : Chain.C n)
    (hp : p.2.val=10 ∧(p.1.val≤1 ∨n+2≤p.1.val)) : p∈Chain.allNeighbors n := by
  have hx:=p.1.isLt
  rcases p with ⟨x,y⟩
  dsimp only at hp hx
  simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega

private theorem flippedMask_complete (n : ℕ) (p : FlippedChain.C n)
    (hp : p.2.val=10 ∧(p.1.val≤1 ∨n+22≤p.1.val)) : p∈FlippedChain.allNeighbors n := by
  have hx:=p.1.isLt
  rcases p with ⟨x,y⟩
  dsimp only at hp hx
  simp only [FlippedChain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega

theorem lineAllNeighbors_iff (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height) :
    p∈lineAllNeighbors flip n hn a b ↔p.2.val=10 ∧(p.1.val≤1 ∨n+(if flip then 20 else 0)+2≤p.1.val) := by
  cases flip
  · exact ⟨Chain.allNeighbors_bounds n,chainMask_complete n p⟩
  · exact ⟨FlippedChain.allNeighbors_bounds n,flippedMask_complete n p⟩

private theorem corner_succ_lt {n : ℕ} (k : Fin (n-1)) : k.val+1<n := by
  have :=k.isLt
  omega

theorem line_profile_collar (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) :
    Polyline.Frame.fixed (lineEmbedding g r j) (profileOutside g f (lineIndex g r j))⊆
      lineAllNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) := by
  intro p hp
  obtain ⟨i,hij,q,hq,he⟩:=(mem_profileOutside g f (lineIndex g r j) _).mp ((Polyline.Frame.mem_fixed _ _ p).mp hp)
  have hpoint : (primitiveEmbedding g (lineIndex g r j)).cells
      ((lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).cells p)=
      (primitiveEmbedding g i).cells q := he.symm
  have hc : Inventory.contact g (lineIndex g r j) i=true := by
    by_contra hc
    have hf : Inventory.contact g (lineIndex g r j) i=false := Bool.eq_false_iff.mpr hc
    exact Inventory.no_coincident g _ i (Ne.symm hij) hf
      ((lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).cells p) q
      (congrArg (fun p : C=>(p.1.val,p.2.val)) hpoint)
  apply (lineAllNeighbors_iff _ _ _ _ _ p).mpr
  rcases i with i | (⟨s,k|k⟩|s)
  · simp only [lineIndex,Inventory.contact,decide_eq_true_eq] at hc
    have hi : i=frontierBufferIndex r := Fin.ext hc.1
    subst i
    have hj : j=⟨0,frontier_first_valid (key g r)⟩ := Fin.ext hc.2
    subst j
    obtain ⟨l,hl⟩:=selected_buffer_coordinates g f r q hq
    have he':=congrArg (fun p : C=>(p.1.val,p.2.val)) he
    have hs:=hl.symm.trans (he'.trans (line_coordinates g r ⟨0,frontier_first_valid _⟩ p))
    rw [frontier_first_orientation] at hs
    let k:=key g r
    let phase:=armPhase g f r (.inl (frontierBufferIndex r))
    have hrel:=frontier_relative (fillerFlip k 0) (Inventory.initialPhase g r) (Inventory.targetPhase g r)
      (frontierOrientation g.core.isAND r) (frontierBufferOffset g r).1 (frontierBufferOffset g r).2
      (lineOffset k 0).1 (lineOffset k 0).2 (Chain.position 2301 (by omega) (Chain.uniform 2301 phase) l) p
      hs (frontier_shared_anchor g r _ _)
    have hb:=Polyline.chain_phase_bounds 2301 (by omega) phase l
    have hphase : phase.toNat≤1 := by cases phase <;> decide
    have hy:=Chain.position_row 2301 (by omega) (Chain.uniform 2301 phase) l
    exact ⟨hrel.2.symm.trans hy,Or.inl (by omega)⟩
  · simp only [lineIndex,Inventory.contact,Bool.false_eq_true] at hc
  · simp only [lineIndex,Inventory.contact,decide_eq_true_eq] at hc
    have hrs : s=r := hc.1.symm
    subst s
    obtain ⟨l,hl⟩:=selected_corner_coordinates g f r k q hq
    have he':=congrArg (fun p : C=>(p.1.val,p.2.val)) he
    have hs:=(line_coordinates g r j p).symm.trans (he'.symm.trans hl)
    rcases hc.2 with hj|hj
    · have hj' : j=⟨k.val,lt_trans (Nat.lt_succ_self _) (corner_succ_lt k)⟩ := Fin.ext hj
      subst j
      have hm:=short_near_line_slots (turn_perpendicular (key g r) k.val (by have :=k.isLt; omega))
        (fillerFlip (key g r) k.val) (armPhase g f r (cornerIndex g r k)) (fillerSpan (key g r) k.val)
        (filler_shape _ _ (by have :=k.isLt; omega)).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r)
        (lineOffset (key g r) k.val).1 (lineOffset (key g r) k.val).2
        (cornerOffset (key g r) k.val).1 (cornerOffset (key g r) k.val).2 p l hs
        ((line_far_anchor_coordinates (key g r) k.val (by have :=k.isLt; omega) _ _).trans
          (corner_near_anchor_coordinates (key g r) k.val (by have :=k.isLt; omega)).symm)
      dsimp only at hm ⊢
      exact ⟨hm.1,Or.inr (by omega)⟩
    · have hj' : j=⟨k.val+1,corner_succ_lt k⟩ := Fin.ext hj
      subst j
      have hm:=short_far_line_slots_general (turn_perpendicular (key g r) k.val (by have :=k.isLt; omega))
        (fillerFlip (key g r) (k.val+1)) (later_line_unflipped (key g r) k.val)
        (armPhase g f r (cornerIndex g r k)) (fillerSpan (key g r) (k.val+1))
        (filler_shape _ _ (by have :=k.isLt; omega)).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r)
        (lineOffset (key g r) (k.val+1)).1 (lineOffset (key g r) (k.val+1)).2
        (cornerOffset (key g r) k.val).1 (cornerOffset (key g r) k.val).2 p l hs
        ((line_near_anchor_coordinates (key g r) (k.val+1) (by have :=k.isLt; omega) _ _).trans
          (corner_far_anchor_coordinates (key g r) k.val (by have :=k.isLt; omega)).symm)
      dsimp only at hm ⊢
      have hphase : (armPhase g f r (cornerIndex g r k)).toNat≤1 := by cases armPhase g f r (cornerIndex g r k) <;> decide
      exact ⟨hm.1,Or.inl (by omega)⟩
  · simp only [lineIndex,Inventory.contact,Bool.false_eq_true] at hc

end PushPuzzle.PushFS.Reduction.GateTileRouting
