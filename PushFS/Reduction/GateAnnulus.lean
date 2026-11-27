/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortRotation
public import PushFS.Gadgets.Gates.Collar

/-!
# Buffered physical-coordinate routing around the actual fixed gate cores

The annulus keeps the AND and OR cores unrotated. Its three inner ports have
the actual rows and columns of the long-wall gate ports. Long straight leads
join those core ports to the checked annular curves. Every resulting segment
has length at least 3000, leaving room for real guarded turns and 40/59 wires.
Distinct arms have a checked 20-cell gap; nonconsecutive pieces of one arm
have a 200-cell gap.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateAnnulus


open Turing.MultiTapeTM ComputableInPolyTime
open Gadgets

/-- Actual gate kind followed by the cyclic outer routing key. -/
abbrev Key := Bool × PortAnnulus.Key

/-- W/N/E role of a routing key. -/
def role (q : Key) : Fin 3 := q.2.2.2

/-- Move the first horizontal lead to the actual AND/OR port row. -/
def innerRow (q : Key) : ℕ := if role q = 0 ∧ q.1 = true then 99 else 101

/-- Buffered integer curves, retaining the exact outer cyclic endpoints. -/
def vertices (q : Key) : List (ℕ × ℕ) :=
  let vs := (PortAnnulus.vertices q.2).map (fun p => (4 * p.1, 4 * p.2))
  if role q = 1 then vs
  else if vs.length = 2 then
    if role q = 0 then
      [(80, innerRow q), (40, innerRow q), (40, 60), (20, 60), (20, 100), (0, 100)]
    else [(120, 101), (160, 101), (160, 140), (180, 140), (180, 100), (200, 100)]
  else (vs.take 2).map (fun p => (p.1, innerRow q)) ++ vs.drop 2

/-- Unequal row spacing aligns the AND's west row 29 with the east row 90. -/
def warpY (y : ℕ) : ℕ :=
  if y ≤ 99 then 1000 * y else if y = 100 then 99031 else 99061 + 1000 * (y - 101)

/-- Physical coordinates of a buffered annular lattice point. -/
def point (p : ℕ × ℕ) : ℕ × ℕ := (1000 * p.1, warpY p.2)

/-- Full physical-coordinate annular segment program. -/
def curve (q : Key) : List Segment :=
  let vs := (vertices q).map point
  vs.zipWith Segment.mk vs.tail

/-- The one actual translation of the unrotated 81×107 gate core. -/
def coreOffset (kind : Bool) : ℕ × ℕ := (100000 - (if kind then 43 else 44), 98971)

/-- The actual gate boundary anchors in the physical annular rectangle. -/
def corePort (q : Key) : ℕ × ℕ :=
  let p := Gates.port q.1 (role q)
  ((coreOffset q.1).1 + p.1.val, (coreOffset q.1).2 + p.2.val)

/-- The corresponding inner annular anchor reached by a long straight lead. -/
def innerPoint (q : Key) : ℕ × ℕ :=
  if role q = 0 then point (80, innerRow q)
  else if role q = 1 then point (100, 80) else point (120, 101)

/-- Connect the real complete gate to its actual annular port on the same ray. -/
def lead (q : Key) : Segment := ⟨corePort q, innerPoint q⟩

/-- The full gate-to-boundary route, including its actual core lead. -/
def route (q : Key) : List Segment := lead q :: curve q

private def lengthTest (s : Segment) : Bool :=
  decide ((s.start.1 = s.finish.1 ∧ min s.start.2 s.finish.2 + 3000 ≤ max s.start.2 s.finish.2) ∨
    (s.start.2 = s.finish.2 ∧ min s.start.1 s.finish.1 + 3000 ≤ max s.start.1 s.finish.1))

private def segmentTest (s : Segment) : Bool :=
  lengthTest s && decide (s.start.1 ≤ 200000 ∧ s.finish.1 ≤ 200000 ∧
    s.start.2 ≤ 198061 ∧ s.finish.2 ≤ 198061)

private def shapeTest (q : Key) : Bool :=
  decide (2 ≤ (vertices q).length) &&
    decide (point ((vertices q).headD (0, 0)) = innerPoint q) &&
    decide (point ((vertices q).getLastD (0, 0)) = point
      (let p := PortAnnulus.outerPoint (PortAnnulus.outerDirection q.2); (4 * p.1, 4 * p.2))) &&
    decide (PortAnnulus.Runs (PortAnnulus.innerDirection (role q)) (corePort q) (innerPoint q)) &&
    decide (PortAnnulus.Runs (PortAnnulus.innerDirection (role q)) (innerPoint q)
      (point ((vertices q).getD 1 (0, 0)))) &&
    decide (PortAnnulus.Runs (PortAnnulus.outerDirection q.2)
      (point ((vertices q).getD ((vertices q).length - 2) (0, 0)))
      (point ((vertices q).getLastD (0, 0)))) &&
    (route q).all segmentTest

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem shape_checked : ∀ q : Key, shapeTest q = true := by decide +kernel

/-- The source's real W/N/E core ports connect on the correct rays to their computed outer anchors. -/
theorem endpoints (q : Key) :
    2 ≤ (vertices q).length ∧ point ((vertices q).headD (0, 0)) = innerPoint q ∧
      point ((vertices q).getLastD (0, 0)) = point
        (let p := PortAnnulus.outerPoint (PortAnnulus.outerDirection q.2); (4 * p.1, 4 * p.2)) ∧
      PortAnnulus.Runs (PortAnnulus.innerDirection (role q)) (corePort q) (innerPoint q) := by
  have hh := shape_checked q
  simp only [shapeTest, Bool.and_eq_true, decide_eq_true_eq] at hh
  tauto

end PushPuzzle.PushFS.Reduction.GateAnnulus
