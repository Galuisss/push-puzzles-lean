/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.MotionEnvelopes
public import PushFS.Reduction.FullGateRawLabels

/-! Every paired source and target lie in one actual primitive motion interval. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem line_motion_point (o : RectOrientation) (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (dx dy : ℕ) (p : Cell (lineBase f n hn a b).width (lineBase f n hn a b).height)
    (hb : 2≤p.1.val ∧p.1.val≤n+(if f then 20 else 0)+1 ∧p.2.val=10) :
    (Envelope.placed o (n+(if f then 25 else 5)) 21 dx dy (Envelope.motionRail n f)).Contains
      (o.coordinates (lineBase f n hn a b).width (lineBase f n hn a b).height dx dy p) := by
  have hp:(Envelope.motionRail n f).Contains (p.1.val,p.2.val):=by
    dsimp only [Envelope.Contains,Envelope.motionRail]
    omega
  have ht:=Envelope.placed_contains o (n+(if f then 25 else 5)) 21 dx dy _ _ hp
  have hd:((lineBase f n hn a b).width,(lineBase f n hn a b).height)=(n+(if f then 25 else 5),21):=
    Prod.ext (line_dimensions f n hn a b).1 (line_dimensions f n hn a b).2
  have he:=congrArg (fun wh : ℕ×ℕ=>o.point wh.1 wh.2 (p.1.val,p.2.val)) hd
  rw [RectOrientation.coordinates_point]
  change (Envelope.placed o (n+(if f then 25 else 5)) 21 dx dy (Envelope.motionRail n f)).Contains
    (dx+(o.point (lineBase f n hn a b).width (lineBase f n hn a b).height (p.1.val,p.2.val)).1,
      dy+(o.point (lineBase f n hn a b).width (lineBase f n hn a b).height (p.1.val,p.2.val)).2)
  rw [he]
  exact ht

private theorem line_motion_enclosed (o : RectOrientation) (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (dx dy : ℕ) (l : lineLabels f n) :
    (Envelope.placed o (n+(if f then 25 else 5)) 21 dx dy (Envelope.motionRail n f)).Contains
      (o.coordinates (lineBase f n hn a b).width (lineBase f n hn a b).height dx dy ((lineMatching f n hn a b).source l)) ∧
    (Envelope.placed o (n+(if f then 25 else 5)) 21 dx dy (Envelope.motionRail n f)).Contains
      (o.coordinates (lineBase f n hn a b).width (lineBase f n hn a b).height dx dy ((lineMatching f n hn a b).target l)) := by
  have ha : a.toNat≤1:=by cases a <;> decide
  have hb : b.toNat≤1:=by cases b <;> decide
  constructor
  · apply line_motion_point
    have hh:=line_source_bounds f n hn a b l
    exact ⟨by omega,by omega,hh.2.2⟩
  · apply line_motion_point
    have hh:=line_target_bounds f n hn a b l
    exact ⟨by omega,by omega,hh.2.2⟩

private theorem annular_motion_enclosed (g : GateTileState) (role : Fin 3) (j : Fin (curve (key g role)).length)
    (l : lineLabels (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)) :
    ∃r∈motionEnvelopes g (.inr (.inl ⟨role,.inl j⟩)),
      r.Contains ((rawSource g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩).1.val,(rawSource g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩).2.val) ∧
      r.Contains ((rawTarget g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩).1.val,(rawTarget g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩).2.val) := by
  let k:=key g role
  let r:=Envelope.placed (lineOrientation (original k j.val).travel (fillerFlip k j.val)) (lineWidth k j.val) 21
    (lineOffset k j.val).1 (lineOffset k j.val).2 (Envelope.motionRail (fillerSpan k j.val) (fillerFlip k j.val))
  refine ⟨r,by change r∈[r]; exact List.mem_singleton_self _,?_,?_⟩
  all_goals
    have hh:=line_motion_enclosed (lineOrientation (original k j.val).travel (fillerFlip k j.val))
      (fillerFlip k j.val) (fillerSpan k j.val) (filler_shape k j.val j.isLt).2.1
      (initialPhase g role) (targetPhase g role) (lineOffset k j.val).1 (lineOffset k j.val).2 l
  · have he:=line_source_coordinates k j.val j.isLt (initialPhase g role) (targetPhase g role) l
    change r.Contains ((lineOffset k j.val).1+((lineSlotMatching k j.val j.isLt (initialPhase g role) (targetPhase g role)).source l).1.val,
      (lineOffset k j.val).2+((lineSlotMatching k j.val j.isLt (initialPhase g role) (targetPhase g role)).source l).2.val)
    exact he.symm ▸hh.1
  · have he:=line_target_coordinates k j.val j.isLt (initialPhase g role) (targetPhase g role) l
    change r.Contains ((lineOffset k j.val).1+((lineSlotMatching k j.val j.isLt (initialPhase g role) (targetPhase g role)).target l).1.val,
      (lineOffset k j.val).2+((lineSlotMatching k j.val j.isLt (initialPhase g role) (targetPhase g role)).target l).2.val)
    exact he.symm ▸hh.2

private theorem slot_motion_contains (s : Gates.Slot) (dx dy : ℕ) (b : Gates.Signals) :
    (Envelope.motionSlot s dx dy).Contains (dx+(s.position b).1.val,dy+(s.position b).2.val) := by
  unfold Gates.Slot.position
  split
  · exact Envelope.join_contains_right _ _ _ (Envelope.point_contains _)
  · exact Envelope.join_contains_left _ _ _ (Envelope.point_contains _)

private theorem core_motion_enclosed (g : GateTileState) (l : Fin (Gates.slots g.core.isAND).length) :
    ∃r∈motionEnvelopes g (.inl 0),
      r.Contains ((rawSource g ⟨.inl 0,l⟩).1.val,(rawSource g ⟨.inl 0,l⟩).2.val) ∧
      r.Contains ((rawTarget g ⟨.inl 0,l⟩).1.val,(rawTarget g ⟨.inl 0,l⟩).2.val) := by
  let s:=(Gates.slots g.core.isAND)[l.val]
  let dx:=(geometricOffset g (.inl 0)).1
  let dy:=(geometricOffset g (.inl 0)).2
  refine ⟨Envelope.motionSlot s dx dy,?_,?_,?_⟩
  · exact List.mem_map.mpr ⟨s,List.getElem_mem l.isLt,rfl⟩
  · exact slot_motion_contains s dx dy g.core.initial
  · exact slot_motion_contains s dx dy g.core.target

private theorem buffer_motion_enclosed (g : GateTileState) (role : Fin 3) (l : Chain.Label 2301) :
    ∃r∈motionEnvelopes g (.inl (frontierBufferIndex role)),
      r.Contains ((rawSource g ⟨.inl (frontierBufferIndex role),l⟩).1.val,(rawSource g ⟨.inl (frontierBufferIndex role),l⟩).2.val) ∧
      r.Contains ((rawTarget g ⟨.inl (frontierBufferIndex role),l⟩).1.val,(rawTarget g ⟨.inl (frontierBufferIndex role),l⟩).2.val) := by
  let o:=frontierOrientation g.core.isAND role
  let dx:=(frontierBufferOffset g role).1
  let dy:=(frontierBufferOffset g role).2
  let r:=Envelope.placed o 2306 21 dx dy (Envelope.motionRail 2301 false)
  refine ⟨r,?_,?_,?_⟩
  · have he : motionEnvelopes g (.inl (frontierBufferIndex role))=[r] := by fin_cases role <;> rfl
    rw [he]
    exact List.mem_singleton_self _
  all_goals
    have hh:=line_motion_enclosed o false 2301 (by omega) (gateClaim g.core.initial role) (gateClaim g.core.target role) dx dy l
  · have he:=frontier_buffer_source_coordinates g role l
    change r.Contains ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).source l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).source l).2.val)
    exact he.symm ▸hh.1
  · have he:=frontier_buffer_target_coordinates g role l
    change r.Contains ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).2.val)
    exact he.symm ▸hh.2

private theorem corner_motion_point (k : Key) (j : ℕ) (l : Fin (ShortCorners.count (cornerKind k j))) (phase : Bool) :
    ((Envelope.point (((ShortCorners.template (cornerKind k j)).position false l).1.val,
      ((ShortCorners.template (cornerKind k j)).position false l).2.val)).join
      (Envelope.point (((ShortCorners.template (cornerKind k j)).position true l).1.val,
        ((ShortCorners.template (cornerKind k j)).position true l).2.val))).Contains
      (((ShortCorners.template (cornerKind k j)).position phase l).1.val,
        ((ShortCorners.template (cornerKind k j)).position phase l).2.val) := by
  cases phase
  · exact Envelope.join_contains_left _ _ _ (Envelope.point_contains _)
  · exact Envelope.join_contains_right _ _ _ (Envelope.point_contains _)

private theorem corner_motion_enclosed (g : GateTileState) (role : Fin 3) (j : Fin ((curve (key g role)).length-1))
    (l : Fin (ShortCorners.count (cornerKind (key g role) j.val))) :
    ∃r∈motionEnvelopes g (.inr (.inl ⟨role,.inr j⟩)),
      r.Contains ((rawSource g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩).1.val,(rawSource g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩).2.val) ∧
      r.Contains ((rawTarget g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩).1.val,(rawTarget g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩).2.val) := by
  let k:=key g role
  let kind:=cornerKind k j.val
  let e:=(Envelope.point (((ShortCorners.template kind).position false l).1.val,
    ((ShortCorners.template kind).position false l).2.val)).join
    (Envelope.point (((ShortCorners.template kind).position true l).1.val,
      ((ShortCorners.template kind).position true l).2.val))
  let r:=Envelope.placed (cornerOrientation k j.val) (ShortCorners.width kind) (ShortCorners.height kind)
    (cornerOffset k j.val).1 (cornerOffset k j.val).2 e
  refine ⟨r,List.mem_map.mpr ⟨l,by simp only [List.mem_finRange],rfl⟩,?_,?_⟩
  · have hh:=Envelope.placed_contains (cornerOrientation k j.val) (ShortCorners.width kind) (ShortCorners.height kind)
      (cornerOffset k j.val).1 (cornerOffset k j.val).2 e _ (corner_motion_point k j.val l (initialPhase g role))
    have he:=corner_source_coordinates k j.val (initialPhase g role) (targetPhase g role) l
    rw [RectOrientation.coordinates_point] at he
    change r.Contains ((cornerOffset k j.val).1+((cornerMatching k j.val (initialPhase g role) (targetPhase g role)).source l).1.val,
      (cornerOffset k j.val).2+((cornerMatching k j.val (initialPhase g role) (targetPhase g role)).source l).2.val)
    exact he.symm ▸hh
  · have hh:=Envelope.placed_contains (cornerOrientation k j.val) (ShortCorners.width kind) (ShortCorners.height kind)
      (cornerOffset k j.val).1 (cornerOffset k j.val).2 e _ (corner_motion_point k j.val l (targetPhase g role))
    have he:=corner_target_coordinates k j.val (initialPhase g role) (targetPhase g role) l
    rw [RectOrientation.coordinates_point] at he
    change r.Contains ((cornerOffset k j.val).1+((cornerMatching k j.val (initialPhase g role) (targetPhase g role)).target l).1.val,
      (cornerOffset k j.val).2+((cornerMatching k j.val (initialPhase g role) (targetPhase g role)).target l).2.val)
    exact he.symm ▸hh

/-- A physical identity's entire canonical movement is covered by one primitive-owned interval. -/
theorem raw_motion_enclosed (g : GateTileState) (i : Inventory.Index g) (l : Inventory.Labels g i) :
    ∃r∈motionEnvelopes g i,
      r.Contains ((rawSource g ⟨i,l⟩).1.val,(rawSource g ⟨i,l⟩).2.val) ∧
      r.Contains ((rawTarget g ⟨i,l⟩).1.val,(rawTarget g ⟨i,l⟩).2.val) := by
  rcases i with i|(⟨role,j|j⟩|role)
  · fin_cases i
    · exact core_motion_enclosed g l
    · exact buffer_motion_enclosed g 0 l
    · exact buffer_motion_enclosed g 1 l
    · exact buffer_motion_enclosed g 2 l
  · exact annular_motion_enclosed g role j l
  · exact corner_motion_enclosed g role j l
  · exact Fin.elim0 l

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
