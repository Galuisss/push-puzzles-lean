/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingJunctions

/-! Adjacent emitted path instructions satisfy the literal turn interface equations. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

def lineCodeAt (segments : List Segment) (initialSide targetSide keepEndpoint initial target : Bool)
    (i : ℕ) : LineCode :=
  ⟨trimmedSegment segments i,entrySide segments initialSide i,false,
    ownsLast segments keepEndpoint i,initial,target,finalSide segments targetSide i⟩

def turnCodeAt (segments : List Segment) (initial target : Bool) (i : ℕ) : TurnCode :=
  ⟨segmentDirection (segmentAt segments i),segmentDirection (segmentAt segments (i+1)),
    (segmentAt segments i).finish,initial,target⟩

theorem perpendicular_ne {d e : Direction} (h : Perpendicular d e) : d ≠ e := by
  cases d <;> cases e <;> simp_all [Perpendicular,rightTurn,Direction.opposite]

theorem trimmedSegment_direction (w : ℕ) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s) (i : ℕ) (hi : i < segments.length) :
    segmentDirection (trimmedSegment segments i) = segmentDirection (segmentAt segments i) := by
  have hmem : segmentAt segments i ∈ segments := by
    rw [segmentAt,List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hs := hg _ hmem
  have hsum : startTrim segments i+finishTrim segments i ≤ segmentLength (segmentAt segments i) := by
    have hf := startTrim_bound segments i
    have hb := finishTrim_bound segments i
    have hl := hs.2.1
    omega
  exact segmentDirection_of_travels _ _ _ _ (trimmed_travels _ hs.1 _ _ hsum)
    (by have hf := startTrim_bound segments i; have hb := finishTrim_bound segments i
        have hl := hs.2.1; omega)

structure JunctionContract (w : ℕ) (c : LineCode) (t : TurnCode) (d : LineCode) : Prop where
  incoming_good : LineGood w c.segment
  outgoing_good : LineGood w d.segment
  perpendicular : Perpendicular t.incoming t.outgoing
  incoming_last : c.last = false
  outgoing_first : d.first = false
  incoming_direction : segmentDirection c.segment = t.incoming
  incoming_finish : c.segment.finish = advance t.incoming.opposite t.corner 2
  outgoing_direction : segmentDirection d.segment = t.outgoing
  outgoing_start : d.segment.start = advance t.outgoing t.corner 1

theorem path_junction_contract (w : ℕ) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s)
    (hj : segments.IsChain (fun s t => s.finish = t.start))
    (initialSide targetSide keepEndpoint initial target : Bool) (i : ℕ) (hi : i+1 < segments.length)
    (hp : Perpendicular (segmentDirection (segmentAt segments i))
      (segmentDirection (segmentAt segments (i+1)))) :
    JunctionContract w (lineCodeAt segments initialSide targetSide keepEndpoint initial target i)
      (turnCodeAt segments initial target i)
      (lineCodeAt segments initialSide targetSide keepEndpoint initial target (i+1)) := by
  have hi' : i < segments.length := by omega
  have hne := perpendicular_ne hp
  have hfinish : finishTrim segments i = 2 := by
    simp only [finishTrim,show i+1 ≠ segments.length by omega,↓reduceIte,hne]
  have hstart : startTrim segments (i+1) = 1 := by
    simp only [startTrim,show i+1 ≠ 0 by omega,↓reduceIte,Nat.add_sub_cancel,hne]
  have hjoin : (segmentAt segments i).finish = (segmentAt segments (i+1)).start := by
    have h := hj.getElem i hi
    simpa only [segmentAt,List.getD_eq_getElem _ _ hi',List.getD_eq_getElem _ _ hi] using h
  refine ⟨trimmedSegment_lineGood w segments hg i hi',trimmedSegment_lineGood w segments hg (i+1) hi,
    hp,?_,rfl,trimmedSegment_direction w segments hg i hi',?_,
    trimmedSegment_direction w segments hg (i+1) hi,?_⟩
  · simp only [lineCodeAt,ownsLast,show i+1 ≠ segments.length by omega,↓reduceIte,hne,decide_false]
  · change (trimmedSegment segments i).finish = _
    simp only [trimmedSegment,trimmed,hfinish,turnCodeAt]
  · change (trimmedSegment segments (i+1)).start = _
    simp only [trimmedSegment,trimmed,hstart,turnCodeAt,hjoin]

theorem pathCodes_singleton (s : Segment) (initialSide targetSide keepEndpoint initial target : Bool) :
    pathCodes [s] initialSide targetSide keepEndpoint initial target =
      [.line (lineCodeAt [s] initialSide targetSide keepEndpoint initial target 0)] := by
  simp [pathCodes,lineCodeAt]

theorem pathCodes_pair (s t : Segment) (initialSide targetSide keepEndpoint initial target : Bool)
    (hne : segmentDirection s ≠ segmentDirection t) :
    pathCodes [s,t] initialSide targetSide keepEndpoint initial target =
      [.line (lineCodeAt [s,t] initialSide targetSide keepEndpoint initial target 0),
       .turn (turnCodeAt [s,t] initial target 0),
       .line (lineCodeAt [s,t] initialSide targetSide keepEndpoint initial target 1)] := by
  simp [pathCodes,lineCodeAt,turnCodeAt,segmentAt,hne,List.range_succ]

theorem advance_zero (d : Direction) (p : ℕ × ℕ) : advance d p 0 = p := by cases d <;> rfl

structure CollinearContract (w : ℕ) (c d : LineCode) : Prop where
  first_good : LineGood w c.segment
  next_good : LineGood w d.segment
  next_first : d.first = false
  directions : segmentDirection c.segment = segmentDirection d.segment
  joined : c.segment.finish = d.segment.start

theorem path_collinear_contract (w : ℕ) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s)
    (hj : segments.IsChain (fun s t => s.finish = t.start))
    (initialSide targetSide keepEndpoint initial target : Bool) (i : ℕ) (hi : i+1 < segments.length)
    (he : segmentDirection (segmentAt segments i) = segmentDirection (segmentAt segments (i+1))) :
    CollinearContract w (lineCodeAt segments initialSide targetSide keepEndpoint initial target i)
      (lineCodeAt segments initialSide targetSide keepEndpoint initial target (i+1)) := by
  have hi' : i < segments.length := by omega
  have hfinish : finishTrim segments i = 0 := by
    simp only [finishTrim,show i+1 ≠ segments.length by omega,↓reduceIte,he]
  have hstart : startTrim segments (i+1) = 0 := by
    simp only [startTrim,show i+1 ≠ 0 by omega,↓reduceIte,Nat.add_sub_cancel,he]
  have hjoin : (segmentAt segments i).finish = (segmentAt segments (i+1)).start := by
    have h := hj.getElem i hi
    simpa only [segmentAt,List.getD_eq_getElem _ _ hi',List.getD_eq_getElem _ _ hi] using h
  refine ⟨trimmedSegment_lineGood w segments hg i hi',trimmedSegment_lineGood w segments hg (i+1) hi,
    rfl,?_,?_⟩
  · change segmentDirection (trimmedSegment segments i) = segmentDirection (trimmedSegment segments (i+1))
    rw [trimmedSegment_direction w segments hg i hi',trimmedSegment_direction w segments hg (i+1) hi,he]
  · change (trimmedSegment segments i).finish = (trimmedSegment segments (i+1)).start
    simp only [trimmedSegment,trimmed,hfinish,hstart,advance_zero,hjoin]

end PushPuzzle.PushS.FiniteRouting
