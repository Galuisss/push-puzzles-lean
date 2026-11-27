/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateMatching
public import PushFS.AxisTracks

/-! Literal coordinate tracks and sparse normal goals of the thick AND/OR cores. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateTracks

open PushFS FiniteGeometry

attribute [local irreducible] side

/-- The physical axis carrying each named AND box in every normal phase. -/
def andTrack (w : ℕ) : AndLabel w → AxisTrack
  | .west _ => .horizontal (origin w-6*w-21)
  | .upper _ | .middle | .lower _ => .vertical (origin w-6*w-9)
  | .branchB _ => .vertical (origin w+3)
  | .guard _ | .triggerA | .branchC _ => .horizontal (origin w)

/-- The physical axis carrying each named OR box in every normal phase. -/
def orTrack (w : ℕ) : OrLabel w → AxisTrack
  | .branchB _ => .vertical (origin w+4)
  | _ => .horizontal (origin w)

theorem andTrack_active (w : ℕ) (l : AndLabel w) : andTrack w l ≠ .outside := by
  cases l <;> simp [andTrack]

theorem orTrack_active (w : ℕ) (l : OrLabel w) : orTrack w l ≠ .outside := by
  cases l <;> simp [orTrack]

-- Check the finitely many pairs of families and directions; all index bounds remain symbolic.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- Normal targets on one actual AND rail have no adjacent pair. -/
theorem andTrack_sparse (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l m : AndLabel w)
    (htrack : andTrack w l = andTrack w m) (d : Direction) :
    ¬Adjacent d (andCell w a b c l) (andCell w a b c m) := by
  intro hadj
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> cases m <;> cases d <;>
    simp [andTrack, andCell, andPoint, origin, Adjacent] at htrack hadj <;> omega

set_option maxRecDepth 8192 in
theorem orTrack_sparse (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l m : OrLabel w)
    (htrack : orTrack w l = orTrack w m) (d : Direction) :
    ¬Adjacent d (orCell w a b c l) (orCell w a b c m) := by
  intro hadj
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> cases m <;> cases d <;>
    simp [orTrack, orCell, orPoint, origin, Adjacent] at htrack hadj <;> omega

end PushPuzzle.PushS.FiniteGateTracks
