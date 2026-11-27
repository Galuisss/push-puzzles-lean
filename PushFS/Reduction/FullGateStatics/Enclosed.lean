/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Envelopes
public import PushFS.Reduction.FullGateRawLabels

/-! Every genuine physical target lies in its explicit finite slot point or complete phase rail interval. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private theorem line_target_enclosed (o : RectOrientation) (flip : Bool) (n : ℕ) (hn : 2301≤n)
    (a b : Bool)
    (dx dy : ℕ) (l : lineLabels flip n) :
    (Envelope.placed o (n+(if flip then 25 else 5)) 21 dx dy (Envelope.rail n flip b)).Contains
      (o.coordinates (lineBase flip n hn a b).width (lineBase flip n hn a b).height dx dy
        ((lineMatching flip n hn a b).target l)) := by
  let p:=((lineMatching flip n hn a b).target l)
  have hb:=line_target_bounds flip n hn a b l
  have hp:(Envelope.rail n flip b).Contains (p.1.val,p.2.val) := by
    dsimp only [Envelope.Contains,Envelope.rail,p]
    omega
  have ht:=Envelope.placed_contains o (n+(if flip then 25 else 5)) 21 dx dy _ _ hp
  have hd:((lineBase flip n hn a b).width,(lineBase flip n hn a b).height)=(n+(if flip then 25 else 5),21) :=
    Prod.ext (line_dimensions flip n hn a b).1 (line_dimensions flip n hn a b).2
  have he:=congrArg (fun wh : ℕ×ℕ=>o.point wh.1 wh.2 (p.1.val,p.2.val)) hd
  rw [RectOrientation.coordinates_point]
  change (Envelope.placed o (n+(if flip then 25 else 5)) 21 dx dy (Envelope.rail n flip b)).Contains
    (dx+(o.point (lineBase flip n hn a b).width (lineBase flip n hn a b).height (p.1.val,p.2.val)).1,
      dy+(o.point (lineBase flip n hn a b).width (lineBase flip n hn a b).height (p.1.val,p.2.val)).2)
  rw [he]
  exact ht

private theorem chain_target_enclosed (o : RectOrientation) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (dx dy : ℕ) (l : Chain.Label n) :
    (Envelope.placed o (n+5) 21 dx dy (Envelope.rail n false b)).Contains
      (o.coordinates (n+5) 21 dx dy ((Chain.slotMatching n hn a b).target l)) :=
  line_target_enclosed o false n hn a b dx dy l

private theorem annular_line_target_enclosed (g : GateTileState) (role : Fin 3) (j : Fin (curve
    (key g role)).length)
    (l : lineLabels (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)) :
    ∃r∈envelopes g (.inr (.inl ⟨role,.inl j⟩)),r.Contains
      ((rawTarget g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩).1.val,(rawTarget g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩).2.val) := by
  let k:=key g role
  let r:=Envelope.placed (lineOrientation (original k j.val).travel (fillerFlip k j.val)) (lineWidth k j.val) 21
    (lineOffset k j.val).1 (lineOffset k j.val).2 (Envelope.rail (fillerSpan k j.val) (fillerFlip k j.val) (targetPhase g role))
  refine ⟨r,?_,?_⟩
  · change r∈[r]
    simp only [List.mem_singleton]
  · have hh:=line_target_enclosed (lineOrientation (original k j.val).travel (fillerFlip k j.val))
      (fillerFlip k j.val) (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1
      (initialPhase g role) (targetPhase g role) (lineOffset k j.val).1 (lineOffset k j.val).2 l
    have he:=line_target_coordinates k j.val j.isLt (initialPhase g role) (targetPhase g role) l
    change r.Contains ((lineOffset k j.val).1+((lineSlotMatching k j.val j.isLt (initialPhase g role) (targetPhase g role)).target l).1.val,
      (lineOffset k j.val).2+((lineSlotMatching k j.val j.isLt (initialPhase g role) (targetPhase g role)).target l).2.val)
    exact he.symm ▸hh

private theorem corner_target_enclosed (g : GateTileState) (role : Fin 3) (j : Fin ((curve
    (key g role)).length-1))
    (l : Fin (ShortCorners.count (cornerKind (key g role) j.val))) :
    ∃r∈envelopes g (.inr (.inl ⟨role,.inr j⟩)),r.Contains
      ((rawTarget g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩).1.val,(rawTarget g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩).2.val) := by
  let k:=key g role
  let p:=(ShortCorners.template (cornerKind k j.val)).position (targetPhase g role) l
  let q:=(cornerOrientation k j.val).point (ShortCorners.width (cornerKind k j.val)) (ShortCorners.height (cornerKind k j.val)) (p.1.val,p.2.val)
  let u:=((cornerOffset k j.val).1+q.1,(cornerOffset k j.val).2+q.2)
  refine ⟨Envelope.point u,?_,?_⟩
  · exact List.mem_map.mpr ⟨l,by simp only [List.mem_finRange],rfl⟩
  · have he:=corner_target_coordinates k j.val (initialPhase g role) (targetPhase g role) l
    rw [RectOrientation.coordinates_point] at he
    change (Envelope.point u).Contains ((cornerOffset k j.val).1+((cornerMatching k j.val (initialPhase g role) (targetPhase g role)).target l).1.val,
      (cornerOffset k j.val).2+((cornerMatching k j.val (initialPhase g role) (targetPhase g role)).target l).2.val)
    exact he.symm ▸Envelope.point_contains u

private theorem buffer_envelopes (g : GateTileState) (role : Fin 3) :
    envelopes g (.inl (frontierBufferIndex role))=
      [Envelope.placed (frontierOrientation g.core.isAND role) 2306 21
        (frontierBufferOffset g role).1 (frontierBufferOffset g role).2
        (Envelope.rail 2301 false (gateClaim g.core.target role))] := by
  fin_cases role <;> rfl

private theorem buffer_target_enclosed (g : GateTileState) (role : Fin 3) (l : Chain.Label 2301) :
    ∃r∈envelopes g (.inl (frontierBufferIndex role)),r.Contains
      ((rawTarget g ⟨.inl (frontierBufferIndex role),l⟩).1.val,(rawTarget g ⟨.inl (frontierBufferIndex role),l⟩).2.val) := by
  let o:=frontierOrientation g.core.isAND role
  let dx:=(frontierBufferOffset g role).1
  let dy:=(frontierBufferOffset g role).2
  let r:=Envelope.placed o 2306 21 dx dy (Envelope.rail 2301 false (gateClaim g.core.target role))
  refine ⟨r,?_,?_⟩
  · rw [buffer_envelopes]
    simp only [List.mem_singleton,r,o,dx,dy]
  · have hh:=chain_target_enclosed o 2301 (by omega) (gateClaim g.core.initial role) (gateClaim g.core.target role) dx dy l
    have he:=frontier_buffer_target_coordinates g role l
    change r.Contains ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).2.val)
    exact he.symm ▸hh

private theorem core_target_enclosed (g : GateTileState) (l : Fin
    (Gates.slots g.core.isAND).length) :
    ∃r∈envelopes g (.inl 0),r.Contains
      ((rawTarget g ⟨.inl 0,l⟩).1.val,(rawTarget g ⟨.inl 0,l⟩).2.val) := by
  let s:=(Gates.slots g.core.isAND)[l.val]
  let u:=((geometricOffset g (.inl 0)).1+(s.position g.core.target).1.val,
    (geometricOffset g (.inl 0)).2+(s.position g.core.target).2.val)
  refine ⟨Envelope.point u,?_,?_⟩
  · change Envelope.point u∈(Gates.slots g.core.isAND).map _
    exact List.mem_map.mpr ⟨s,List.getElem_mem l.isLt,rfl⟩
  · exact Envelope.point_contains u

theorem raw_target_enclosed (g : GateTileState) (i : Inventory.Index g) (l : Inventory.Labels g i) :
    ∃r∈envelopes g i,r.Contains ((rawTarget g ⟨i,l⟩).1.val,(rawTarget g ⟨i,l⟩).2.val) := by
  rcases i with i|(⟨role,j|j⟩|role)
  · fin_cases i
    · exact core_target_enclosed g l
    · exact buffer_target_enclosed g 0 l
    · exact buffer_target_enclosed g 1 l
    · exact buffer_target_enclosed g 2 l
  · exact annular_line_target_enclosed g role j l
  · exact corner_target_enclosed g role j l
  · exact Fin.elim0 l

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
