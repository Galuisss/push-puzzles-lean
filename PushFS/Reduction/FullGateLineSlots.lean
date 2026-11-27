/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateLineFrames

/-! Exact actual foreign endpoint slots of every independently mixed annular long line. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside selectedMarks cornerKind cornerOrientation

inductive LineForeignSlot (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) (x : ℕ) : Prop
  | buffer (first : j.val=0) (slot : x=(armPhase g f r (.inl (frontierBufferIndex r))).toNat)
  | previous (k : Fin ((curve (key g r)).length-1)) (index : j.val=k.val+1)
      (slot : x=(armPhase g f r (cornerIndex g r k)).toNat)
  | next (k : Fin ((curve (key g r)).length-1)) (index : j.val=k.val)
      (slot : x=fillerSpan (key g r) j.val+(if fillerFlip (key g r) j.val then 20 else 0)+2+
          (armPhase g f r (cornerIndex g r k)).toNat ∨
        armPhase g f r (cornerIndex g r k)=false ∧
          x=fillerSpan (key g r) j.val+(if fillerFlip (key g r) j.val then 20 else 0)+4)

theorem line_profile_slots (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) (p : Cell (lineInput g r j).width (lineInput g r j).height)
    (hp : (lineEmbedding g r j).cells p∈profileOutside g f (lineIndex g r j)) :
    p.2.val=10 ∧LineForeignSlot g f r j p.1.val := by
  obtain ⟨i,hij,q,hq,he⟩:=(mem_profileOutside g f (lineIndex g r j) _).mp hp
  have hc : Inventory.contact g (lineIndex g r j) i=true := by
    by_contra hc
    have hf : Inventory.contact g (lineIndex g r j) i=false := Bool.eq_false_iff.mpr hc
    apply Inventory.no_coincident g _ i (Ne.symm hij) hf
      ((lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).cells p) q
    exact congrArg (fun p : C=>(p.1.val,p.2.val)) he.symm
  rcases i with i | (⟨s,k|k⟩|s)
  · simp only [lineIndex,Inventory.contact,decide_eq_true_eq] at hc
    have hi : i=frontierBufferIndex r := Fin.ext hc.1
    subst i
    have hj : j=⟨0,frontier_first_valid (key g r)⟩ := Fin.ext hc.2
    subst j
    obtain ⟨l,hl⟩:=selected_buffer_coordinates g f r q hq
    have he':=congrArg (fun p : C=>(p.1.val,p.2.val)) he
    have hs:=hl.symm.trans (he'.trans (line_coordinates g r ⟨0,frontier_first_valid (key g r)⟩ p))
    rw [frontier_first_orientation] at hs
    let k:=key g r
    let phase:=armPhase g f r (.inl (frontierBufferIndex r))
    have hrel:=frontier_relative (fillerFlip k 0) (Inventory.initialPhase g r) (Inventory.targetPhase g r)
      (frontierOrientation g.core.isAND r) (frontierBufferOffset g r).1 (frontierBufferOffset g r).2
      (lineOffset k 0).1 (lineOffset k 0).2 (Chain.position 2301 (le_refl 2301) (Chain.uniform 2301 phase) l) p
      hs (frontier_shared_anchor g r (Inventory.initialPhase g r) (Inventory.targetPhase g r))
    have hmin : 2301≤(Chain.position 2301 (le_refl 2301) (Chain.uniform 2301 phase) l).1.val :=
      hrel.1.symm ▸Nat.le_add_right 2301 p.1.val
    have hx:=Catalog.chain_far_x 2301 (le_refl 2301) phase l hmin
    have hy:=Chain.position_row 2301 (le_refl 2301) (Chain.uniform 2301 phase) l
    exact ⟨hrel.2.symm.trans hy,.buffer rfl (Nat.add_left_cancel (hrel.1.symm.trans hx))⟩
  · simp only [lineIndex,Inventory.contact,Bool.false_eq_true] at hc
  · simp only [lineIndex,Inventory.contact,decide_eq_true_eq] at hc
    have hrs : s=r := hc.1.symm
    subst s
    obtain ⟨l,hl⟩:=selected_corner_coordinates g f r k q hq
    have he':=congrArg (fun p : C=>(p.1.val,p.2.val)) he
    have hs:=(line_coordinates g r j p).symm.trans (he'.symm.trans hl)
    rcases hc.2 with hj|hj
    · have hm:=near_selected_corner_slots (key g r) j.val k.val hj j.isLt (cornerOutLine g r k).isLt
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) (armPhase g f r (cornerIndex g r k)) p l hs
      exact ⟨hm.1,.next k hj hm.2⟩
    · have hm:=far_selected_corner_slots (key g r) j.val k.val hj j.isLt (cornerOutLine g r k).isLt
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) (armPhase g f r (cornerIndex g r k)) p l hs
      exact ⟨hm.1,.previous k hj hm.2⟩
  · simp only [lineIndex,Inventory.contact,Bool.false_eq_true] at hc

end PushPuzzle.PushFS.Reduction.GateTileRouting
