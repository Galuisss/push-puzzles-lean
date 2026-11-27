/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBufferProfiles
public import PushFS.Reduction.FullGateBufferTransit
public import PushFS.Reduction.FullGateSelectedSlots

/-! Every independent physical gate profile has literal core-hub access to all real buffered-lead corners. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

private theorem annularProfileBoxes_core_empty (g : GateTileState) (f : Inventory.Index g→Bool)
    (p : Gates.C) :
    (coreEmbedding g).cells p∉annularProfileBoxes g f := by
  intro hp
  obtain ⟨i,hi,q,_,he⟩:=(mem_annularProfileBoxes g f _).mp hp
  cases i with
  | inl i=>cases hi
  | inr i=>
    have hc : Inventory.contact g (.inl 0) (.inr i)=false := by
      rcases i with ⟨r,j|j⟩|r
      · simp only [Inventory.contact,decide_eq_false_iff_not,Fin.val_zero]
        omega
      · rfl
      · rfl
    exact Inventory.no_coincident g (.inl 0) (.inr i) (by simp) hc p q
      (congrArg (fun q : C=>(q.1.val,q.2.val)) he.symm)

private theorem tail_allNeighbors (n : ℕ) (p : Chain.C n) (hx : n+2≤p.1.val) (hy : p.2.val=10) :
    p∈Chain.allNeighbors n := by
  have hp:=p.1.isLt
  rcases p with ⟨x,y⟩
  dsimp only at hx hy hp
  simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega

/-- The actual independently selected annular inventory occupies only the literal buffered tail collar. -/
theorem buffer_profile_collar (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3) :
    GateLead.fixed (bufferLeadEmbedding g r) (annularProfileBoxes g f)⊆Chain.allNeighbors 2301 := by
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
    let a:=armPhase g f r (lineIndex g r ⟨0,frontier_first_valid _⟩)
    let b:=Inventory.targetPhase g r
    have hrel:=frontier_relative (fillerFlip k 0) a b (frontierOrientation g.core.isAND r)
      (frontierBufferOffset g r).1 (frontierBufferOffset g r).2 (lineOffset k 0).1 (lineOffset k 0).2 p
      ((lineMatching (fillerFlip k 0) (fillerSpan k 0) (filler_shape k 0 (frontier_first_valid _)).2.1 a b).source l)
      hs.symm (frontier_shared_anchor g r a b)
    have hb:=line_source_bounds (fillerFlip k 0) (fillerSpan k 0) (filler_shape k 0 (frontier_first_valid _)).2.1 a b l
    exact tail_allNeighbors 2301 p (by have hh:=hrel.1; omega) (hrel.2.trans hb.2.2)
  · simp only [Inventory.contact,Bool.false_eq_true] at hc
  · simp only [Inventory.contact,Bool.false_eq_true] at hc

/-- The full mixed annulus supplies all real walls and the exact empty core of the buffered transit shell. -/
theorem bufferProfileShell (g : GateTileState) (f : Inventory.Index g→Bool) :
    GateLead.ThinShell g.core.isAND 2301 (by omega) (bufferRect g.core.isAND) (fullPuzzle g).board (annularProfileBoxes g f) where
  gate:=(bufferShell g).gate
  west:=(bufferShell g).west
  north:=(bufferShell g).north
  east:=(bufferShell g).east
  outside_floor:=annularProfileBoxes_floor g f
  gate_empty p:=by
    have hh:=annularProfileBoxes_core_empty g f p
    have he:=(GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate_embedding
      (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
      (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND) 0 p
    change (coreEmbedding g).cells p=((GateLead.gate 2301).trans (bufferRect g.core.isAND)).cells p at he
    rw [he] at hh
    exact hh

end PushPuzzle.PushFS.Reduction.GateTileRouting
