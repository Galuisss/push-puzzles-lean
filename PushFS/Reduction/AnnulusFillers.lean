/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.RectOrientation
public import PushFS.Reduction.GateTileRouting

/-! Actual annular straight fillers after reserving the short guarded corner arms. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

def Segment.travel (s : Segment) : Direction :=
  if s.start.1=s.finish.1 then if s.start.2<s.finish.2 then .south else .north
  else if s.start.1<s.finish.1 then .east else .west

def Segment.span (s : Segment) : ℕ :=
  (max s.start.1 s.finish.1-min s.start.1 s.finish.1)+
    (max s.start.2 s.finish.2-min s.start.2 s.finish.2)

/-- Literal natural-coordinate travel, used only at the checked long-segment positions below. -/
def advance (d : Direction) (p : GridRouting.Point) (n : ℕ) : GridRouting.Point :=
  match d with
  | .north => (p.1,p.2-n)
  | .east => (p.1+n,p.2)
  | .south => (p.1,p.2+n)
  | .west => (p.1-n,p.2)

namespace GateTileRouting

def original (q : Key) (i : ℕ) : Segment := (curve q).getD i ⟨(0,0),(0,0)⟩
def turnDirections (q : Key) (i : ℕ) : Direction×Direction := ((original q i).travel,(original q (i+1)).travel)

/-- Thirty or fifty real cells from the corner to its input anchor. -/
def nearLength (ds : Direction×Direction) : ℕ := if RectOrientation.nearFlip ds.1 ds.2 then 50 else 30

/-- Thirty-one or fifty-one real cells from the corner to its output anchor. -/
def farLength (ds : Direction×Direction) : ℕ := if RectOrientation.farFlip ds.1 ds.2 then 51 else 31

def fillerStart (q : Key) (i : ℕ) : GridRouting.Point :=
  if i=0 then bufferedEnd q.1
  else advance (original q i).travel ((vertices q).getD i (0,0)) (farLength (turnDirections q (i-1)))

def fillerEnd (q : Key) (i : ℕ) : GridRouting.Point :=
  if i+1=(curve q).length then tail q
  else advance (original q i).travel.opposite ((vertices q).getD (i+1) (0,0)) (nearLength (turnDirections q i))

def filler (q : Key) (i : ℕ) : Segment := ⟨fillerStart q i,fillerEnd q i⟩

/-- The actual OR west lead and both gates' east leads have the opposite near wall side. -/
def firstFlip (q : Key) : Bool :=
  if GateAnnulus.role q.1=2 then true else decide (GateAnnulus.role q.1=0) && !q.1.1

def fillerFlip (q : Key) (i : ℕ) : Bool := decide (i=0) && firstFlip q

/-- The literal 40/59-chain span; a flipped chain contributes its real extra twenty cells. -/
def fillerSpan (q : Key) (i : ℕ) : ℕ := (filler q i).span-(if fillerFlip q i then 20 else 0)

private def fillerTest (q : Key) (i : ℕ) : Bool :=
  decide (PortAnnulus.Runs (original q i).travel (fillerStart q i) (fillerEnd q i) ∧
    2301≤fillerSpan q i ∧
    (if fillerFlip q i then fillerSpan q i+20 else fillerSpan q i)=(filler q i).span ∧
    2≤(fillerStart q i).1 ∧ 2≤(fillerStart q i).2 ∧
    2≤(fillerEnd q i).1 ∧ 2≤(fillerEnd q i).2 ∧
    (fillerStart q i).1≤200004 ∧ (fillerEnd q i).1≤200004 ∧
    (fillerStart q i).2≤198065 ∧ (fillerEnd q i).2≤198065)

private def turnsTest (q : Key) (i : ℕ) : Bool :=
  decide (RectOrientation.Perpendicular (turnDirections q i).1 (turnDirections q i).2)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem fillers_checked : ∀ q : Key,∀ i : Fin (curve q).length,fillerTest q i.val=true := by decide +kernel
private theorem turns_checked : ∀ q : Key,∀ i : Fin ((curve q).length-1),turnsTest q i.val=true := by decide +kernel

/-- Every actual trimmed straight instruction has room for its complete physical 40/59 filler inventory. -/
theorem filler_shape (q : Key) (i : ℕ) (hi : i<(curve q).length) :
    PortAnnulus.Runs (original q i).travel (fillerStart q i) (fillerEnd q i) ∧
      2301≤fillerSpan q i ∧
      (if fillerFlip q i then fillerSpan q i+20 else fillerSpan q i)=(filler q i).span ∧
      2≤(fillerStart q i).1 ∧ 2≤(fillerStart q i).2 ∧
      2≤(fillerEnd q i).1 ∧ 2≤(fillerEnd q i).2 ∧
      (fillerStart q i).1≤200004 ∧ (fillerEnd q i).1≤200004 ∧
      (fillerStart q i).2≤198065 ∧ (fillerEnd q i).2≤198065 :=
  of_decide_eq_true (fillers_checked q ⟨i,hi⟩)

theorem turn_perpendicular (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    RectOrientation.Perpendicular (turnDirections q i).1 (turnDirections q i).2 :=
  of_decide_eq_true (turns_checked q ⟨i,by omega⟩)

end GateTileRouting
end PushPuzzle.PushFS.Reduction
