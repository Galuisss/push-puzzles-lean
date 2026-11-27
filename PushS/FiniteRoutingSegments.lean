/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPlacement
public import PushFS.Reduction.PlacedBitmap

/-! Executable endpoint trimming and actual primitive bitmaps on routed straight segments. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

def segmentDirection (s : Segment) : Direction :=
  if s.start.1 = s.finish.1 then
    if s.start.2 < s.finish.2 then .south else .north
  else if s.start.1 < s.finish.1 then .east else .west

def segmentLength (s : Segment) : ℕ :=
  max s.start.1 s.finish.1-min s.start.1 s.finish.1 +
    (max s.start.2 s.finish.2-min s.start.2 s.finish.2)

theorem segment_travels (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) :
    Travels (segmentDirection s) s.start s.finish (segmentLength s) := by
  by_cases hx : s.start.1 = s.finish.1
  · by_cases hy : s.start.2 < s.finish.2 <;>
      simp [segmentDirection, hx, hy, segmentLength, Travels] <;> omega
  · have hy := hs.resolve_left hx
    by_cases hxx : s.start.1 < s.finish.1 <;>
      simp [segmentDirection, hx, hxx, hy, segmentLength, Travels] <;> omega

theorem segmentLength_of_travels (d : Direction) (p q : ℕ × ℕ) (length : ℕ)
    (h : Travels d p q length) : segmentLength ⟨p,q⟩ = length := by
  cases d <;> dsimp [Travels, segmentLength] at * <;> omega

def advance (d : Direction) (p : ℕ × ℕ) (n : ℕ) : ℕ × ℕ :=
  match d with
  | .north => (p.1,p.2-n)
  | .east => (p.1+n,p.2)
  | .south => (p.1,p.2+n)
  | .west => (p.1-n,p.2)

/-- Outgoing turn slots begin one cell after a corner; incoming slots end two cells before it. -/
def trimmed (s : Segment) (front back : ℕ) : Segment :=
  ⟨advance (segmentDirection s) s.start front,
    advance (segmentDirection s).opposite s.finish back⟩

theorem advance_travels (d : Direction) (p q : ℕ × ℕ) (length front back : ℕ)
    (h : Travels d p q length) (hl : front+back ≤ length) :
    Travels d (advance d p front) (advance d.opposite q back) (length-front-back) := by
  cases d <;> dsimp [Travels, advance, Direction.opposite] at * <;> omega

theorem advance_bounded (d : Direction) (p q : ℕ × ℕ) (length front back bound : ℕ)
    (h : Travels d p q length) (hl : front+back ≤ length)
    (hp : p.1 ≤ bound ∧ p.2 ≤ bound) (hq : q.1 ≤ bound ∧ q.2 ≤ bound) :
    (advance d p front).1 ≤ bound ∧ (advance d p front).2 ≤ bound ∧
      (advance d.opposite q back).1 ≤ bound ∧ (advance d.opposite q back).2 ≤ bound := by
  cases d <;> dsimp [Travels, advance, Direction.opposite] at * <;> omega

theorem trimmed_travels (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2)
    (front back : ℕ) (hl : front+back ≤ segmentLength s) :
    Travels (segmentDirection s) (trimmed s front back).start (trimmed s front back).finish
      (segmentLength s-front-back) :=
  advance_travels _ _ _ _ _ _ (segment_travels s hs) hl

theorem trimmed_length (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2)
    (front back : ℕ) (hl : front+back ≤ segmentLength s) :
    segmentLength (trimmed s front back) = segmentLength s-front-back :=
  segmentLength_of_travels _ _ _ _ (trimmed_travels s hs front back hl)

/-- A genuine rotated complete finite line piece, with exact endpoint ownership. -/
def lineInstance (w : ℕ) (hw : 2 ≤ w) (s : Segment)
    (above first last initial target desiredSide : Bool) : PushFS.Instance :=
  let atoms := Line.program w (segmentLength s) (above != desiredSide)
  let I := Line.ownedPuzzle w hw atoms above first last initial target
  GridIsometry.reorientInstance I (Line.rotation w atoms (segmentDirection s))

/-- The exact dense physical patch, retaining all real wall, working-box, and goal flags. -/
def linePatch (w : ℕ) (hw : 2 ≤ w) (s : Segment)
    (above first last initial target desiredSide : Bool) : Bitmap.Patch :=
  let atoms := Line.program w (segmentLength s) (above != desiredSide)
  Bitmap.instancePatch (lineInstance w hw s above first last initial target desiredSide)
    (Line.offsetX w atoms (segmentDirection s) s.start)
    (Line.offsetY w atoms (segmentDirection s) s.start)

theorem linePatch_fits (w : ℕ) (hw : 2 ≤ w) (s : Segment)
    (above first last initial target desiredSide : Bool)
    (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2)
    (hl : 17*w+61 ≤ segmentLength s)
    (hp : s.start.1 ≤ tileStride w ∧ s.start.2 ≤ tileStride w)
    (hq : s.finish.1 ≤ tileStride w ∧ s.finish.2 ≤ tileStride w) :
    (linePatch w hw s above first last initial target desiredSide).x+
        (linePatch w hw s above first last initial target desiredSide).bitmap.width ≤ tileSide w ∧
      (linePatch w hw s above first last initial target desiredSide).y+
        (linePatch w hw s above first last initial target desiredSide).bitmap.height ≤ tileSide w := by
  let atoms := Line.program w (segmentLength s) (above != desiredSide)
  have hspan : Line.span w atoms = segmentLength s := Line.program_span_of_bound w _ _ hl
  have ht : Travels (segmentDirection s) s.start s.finish (Line.span w atoms) := by
    rw [hspan]
    exact segment_travels s hs
  exact Line.placement_fits w atoms _ _ _ ht hp hq

end PushPuzzle.PushS.FiniteRouting
