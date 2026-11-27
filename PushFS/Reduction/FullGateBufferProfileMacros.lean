/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBufferProfileWalking
public import PushFS.Reduction.FullGateFrontierWalking

/-! A released first-line phase permits the real buffered-core macro inside any fixed mixed annular inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

private theorem line_high_near (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (l : lineLabels flip n)
    (ha : a=true) (hx : ((lineMatching flip n hn a b).source l).1.val<5) :
    ((lineMatching flip n hn a b).source l).1.val=3 := by
  subst a
  cases flip
  · have hh:=Catalog.chain_near_x n hn true l hx
    exact hh.elim id (fun h=>Bool.noConfusion h.1)
  · change FlippedChain.Label n at l
    change ((FlippedChain.slotMatching n hn true b).source l).1.val=3
    change ((FlippedChain.slotMatching n hn true b).source l).1.val<5 at hx
    rw [FlippedChain.source_position] at hx ⊢
    have hh:=Catalog.flipped_near_x n hn true l hx
    exact hh.elim id (fun h=>Bool.noConfusion h.1)

/-- A selected high first-line phase leaves precisely the strict far neighbor required by the buffered macro. -/
theorem buffer_profile_strict_collar (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (hr : armPhase g f r (lineIndex g r (firstLineIndex g r))=true) :
    GateLead.fixed (bufferLeadEmbedding g r) (annularProfileBoxes g f)⊆Chain.neighbors 2301 := by
  intro p hp
  obtain ⟨i,hi,q,hq,he⟩:=(mem_annularProfileBoxes g f _).mp ((GateLead.mem_fixed _ _ p).mp hp)
  have hpoint : (primitiveEmbedding g (.inl (frontierBufferIndex r))).cells ((bufferLeadIso g r).cells p)=
      (primitiveEmbedding g i).cells q := (buffer_lead_placement g r p).trans he.symm
  have hc : Inventory.contact g (.inl (frontierBufferIndex r)) i=true := by
    by_contra hc
    have hf : Inventory.contact g (.inl (frontierBufferIndex r)) i=false := Bool.eq_false_iff.mpr hc
    have hne : Sum.inl (frontierBufferIndex r)≠i:=by rintro rfl; cases hi
    exact Inventory.no_coincident g _ i hne hf ((bufferLeadIso g r).cells p) q
      (congrArg (fun p : C=>(p.1.val,p.2.val)) hpoint)
  rcases i with i|(⟨s,j|j⟩|s)
  · cases hi
  · simp only [Inventory.contact,decide_eq_true_eq] at hc
    have hrs : s=r:=Fin.ext (by have hh:=hc.1; change r.val+1=s.val+1 at hh; omega)
    subst s
    have hj : j=⟨0,frontier_first_valid (key g r)⟩:=Fin.ext hc.2
    subst j
    obtain ⟨l,hl⟩:=selected_line_coordinates g f r ⟨0,frontier_first_valid _⟩ q hq
    have hcoords:=congrArg (fun p : C=>(p.1.val,p.2.val)) he
    have hs:=hl.symm.trans (hcoords.trans (buffer_lead_coordinates g r p))
    rw [frontier_first_orientation] at hs
    let k:=key g r
    let a:=armPhase g f r (lineIndex g r (firstLineIndex g r))
    let b:=Inventory.targetPhase g r
    have hrel:=frontier_relative (fillerFlip k 0) a b (frontierOrientation g.core.isAND r)
      (frontierBufferOffset g r).1 (frontierBufferOffset g r).2 (lineOffset k 0).1 (lineOffset k 0).2 p
      ((lineMatching (fillerFlip k 0) (fillerSpan k 0) (filler_shape k 0 (frontier_first_valid _)).2.1 a b).source l)
      hs.symm (frontier_shared_anchor g r a b)
    have hy:=line_source_bounds (fillerFlip k 0) (fillerSpan k 0) (filler_shape k 0 (frontier_first_valid _)).2.1 a b l
    have hp':=p.1.isLt
    have hx:=line_high_near (fillerFlip k 0) (fillerSpan k 0) (filler_shape k 0 (frontier_first_valid _)).2.1
      a b l hr (by have h:=hrel.1; omega)
    have hpx : p.1.val=2304:=by
      have h:=hrel.1
      rw [hx] at h
      exact h
    have heq : p=(⟨2304,by decide⟩,10):=Prod.ext (Fin.ext hpx) (Fin.ext (hrel.2.trans hy.2.2))
    rw [heq]
    simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,or_true]
  · simp only [Inventory.contact,Bool.false_eq_true] at hc
  · simp only [Inventory.contact,Bool.false_eq_true] at hc

def commitBuffer (g : GateTileState) (f : Inventory.Index g→Bool) : Inventory.Index g→Bool
  | .inl _=>true
  | .inr i=>f (.inr i)

end PushPuzzle.PushFS.Reduction.GateTileRouting
