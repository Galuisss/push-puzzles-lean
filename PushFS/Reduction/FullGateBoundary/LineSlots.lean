/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.RawSlots

/-! Exact source and target labels and positions of every real exterior terminal line. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def linePenultimate : (flip : Bool)→(n : ℕ)→2301≤n→lineLabels flip n
  | false,n,hn => chainPenultimate n hn
  | true,n,_ => FlippedChain.flipLabels n 7

def lineSourcePoint (k : Key) (j : Fin (curve k).length) (a b : Bool)
    (l : lineLabels (fillerFlip k j.val) (fillerSpan k j.val)) : ℕ×ℕ :=
  ((lineOffset k j.val).1+((lineSlotMatching k j.val j.isLt a b).source l).1.val,
    (lineOffset k j.val).2+((lineSlotMatching k j.val j.isLt a b).source l).2.val)

def lineTargetPoint (k : Key) (j : Fin (curve k).length) (a b : Bool)
    (l : lineLabels (fillerFlip k j.val) (fillerSpan k j.val)) : ℕ×ℕ :=
  ((lineOffset k j.val).1+((lineSlotMatching k j.val j.isLt a b).target l).1.val,
    (lineOffset k j.val).2+((lineSlotMatching k j.val j.isLt a b).target l).2.val)

def lineEndpoint (flip : Bool) (n : ℕ) (hn : 2301≤n) (previous : Bool) : lineLabels flip n :=
  if previous then linePenultimate flip n hn else lineLast flip n hn

theorem last_source_endpoint (k : Key) (j : Fin (curve k).length) (hj : j.val+1=(curve k).length)
    (a b prev : Bool) :
    lineSourcePoint k j a b (lineEndpoint (fillerFlip k j.val) (fillerSpan k j.val)
      (filler_shape k j.val j.isLt).2.1 prev)=endpointPoint (PortAnnulus.outerDirection k.1.2) k.2 a prev := by
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata k j hj
  unfold lineSourcePoint lineSlotMatching linePiece
  generalize_proofs
  rw [hflip,htravel]
  cases prev
  · exact normal_endpoint_coordinates _ k.2 a false _ (filler_shape k j.val j.isLt).2.1
      (lineOffset k j.val).1 (lineOffset k j.val).2 hd _ (Polyline.ChainEnds.last_x _ _ a) (Chain.position_row (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1 _ _)
  · exact normal_endpoint_coordinates _ k.2 a true _ (filler_shape k j.val j.isLt).2.1
      (lineOffset k j.val).1 (lineOffset k j.val).2 hd _ (chain_penultimate_x _ _ a) (Chain.position_row (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1 _ _)

theorem last_source_frame (k : Key) (j : Fin (curve k).length) (hj : j.val+1=(curve k).length) (a b : Bool)
    (l : lineLabels (fillerFlip k j.val) (fillerSpan k j.val))
    (hf : InFrame (PortAnnulus.outerDirection k.1.2) (lineSourcePoint k j a b l)) :
    (l=lineLast (fillerFlip k j.val) (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1 ∧
      lineSourcePoint k j a b l=endpointPoint (PortAnnulus.outerDirection k.1.2) k.2 a false) ∨
    ((k.2=true ∨a=true) ∧l=linePenultimate (fillerFlip k j.val) (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1 ∧
      lineSourcePoint k j a b l=endpointPoint (PortAnnulus.outerDirection k.1.2) k.2 a true) := by
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata k j hj
  revert l
  unfold lineSourcePoint lineSlotMatching linePiece
  generalize_proofs
  rw [hflip,htravel]
  intro l hf
  exact normal_slot_frame _ k.2 _ (filler_shape k j.val j.isLt).2.1 a
    (lineOffset k j.val).1 (lineOffset k j.val).2 hd l _ rfl hf

theorem last_target_frame (k : Key) (j : Fin (curve k).length) (hj : j.val+1=(curve k).length) (a b : Bool)
    (l : lineLabels (fillerFlip k j.val) (fillerSpan k j.val))
    (hf : InFrame (PortAnnulus.outerDirection k.1.2) (lineTargetPoint k j a b l)) :
    (l=lineLast (fillerFlip k j.val) (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1 ∧
      lineTargetPoint k j a b l=endpointPoint (PortAnnulus.outerDirection k.1.2) k.2 b false) ∨
    ((k.2=true ∨b=true) ∧l=linePenultimate (fillerFlip k j.val) (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1 ∧
      lineTargetPoint k j a b l=endpointPoint (PortAnnulus.outerDirection k.1.2) k.2 b true) := by
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata k j hj
  revert l
  unfold lineTargetPoint lineSlotMatching linePiece
  generalize_proofs
  rw [hflip,htravel]
  intro l hf
  exact normal_slot_frame _ k.2 _ (filler_shape k j.val j.isLt).2.1 b
    (lineOffset k j.val).1 (lineOffset k j.val).2 hd l _ rfl hf

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
