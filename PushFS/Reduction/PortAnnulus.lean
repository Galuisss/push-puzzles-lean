/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortAnnulus.Data

/-!
# Checked finite cyclic port routing around an unrotated core

The source star has outer triples E/S/W, N/E/S or W/N/E. Each of their three
cyclic matchings is realized by three explicitly listed orthogonal curves in
a 51×51 rectangle. They leave a central square for a fixed W/N/E gate, leave
and enter every port in its stated direction, and have a one-cell gap between
distinct curves. All certificates are checked by the kernel on the full table.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.PortAnnulus


open Turing.MultiTapeTM ComputableInPolyTime

/-- The fixed physical port directions, in clockwise order. -/
def innerDirection (i : Fin 3) : Direction :=
  if i = 0 then .west else if i = 1 then .north else .east

/-- The fixed port anchors on the boundary of the reserved central square. -/
def innerPoint (i : Fin 3) : ℕ × ℕ :=
  if i = 0 then (20, 25) else if i = 1 then (25, 20) else (30, 25)

/-- Outer source-star directions in their actual clockwise order. -/
def boundaryDirection (pattern : Fin 3) (i : ℕ) : Direction :=
  if pattern = 0 then if i = 0 then .east else if i = 1 then .south else .west
  else if pattern = 1 then if i = 0 then .north else if i = 1 then .east else .south
  else if i = 0 then .west else if i = 1 then .north else .east

/-- The cyclicly matched external direction of a physical port. -/
def outerDirection (q : Key) : Direction :=
  boundaryDirection q.1 ((q.2.1.val + q.2.2.val) % 3)

/-- The anchor on the full rectangle's boundary. -/
def outerPoint : Direction → ℕ × ℕ
  | .west => (0, 25)
  | .north => (25, 0)
  | .east => (50, 25)
  | .south => (25, 50)

/-- A nonempty straight segment traversed in the stated direction. -/
def Runs (d : Direction) (p q : ℕ × ℕ) : Prop :=
  match d with
  | .north => p.1 = q.1 ∧ q.2 < p.2
  | .east => p.2 = q.2 ∧ p.1 < q.1
  | .south => p.1 = q.1 ∧ p.2 < q.2
  | .west => p.2 = q.2 ∧ q.1 < p.1

instance (d : Direction) (p q : ℕ × ℕ) : Decidable (Runs d p q) := by
  cases d <;> unfold Runs <;> infer_instance

private def shapeTest (q : Key) : Bool :=
  decide (2 ≤ (vertices q).length) &&
    decide ((vertices q).headD (0, 0) = innerPoint q.2.2) &&
    decide ((vertices q).getLastD (0, 0) = outerPoint (outerDirection q)) &&
    decide (Runs (innerDirection q.2.2) (innerPoint q.2.2)
      ((vertices q).getD 1 (0, 0))) &&
    decide (Runs (outerDirection q) ((vertices q).getD ((vertices q).length - 2) (0, 0))
      (outerPoint (outerDirection q))) &&
    (curve q).all (fun s => decide (s.start ≠ s.finish ∧
      (s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) ∧
      s.start.1 ≤ 50 ∧ s.start.2 ≤ 50 ∧ s.finish.1 ≤ 50 ∧ s.finish.2 ≤ 50))

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem shape_checked : ∀ q : Key, shapeTest q = true := by decide +kernel

/-- Both geometric endpoints and both outward port directions match the declared interface. -/
theorem endpoints (q : Key) :
    2 ≤ (vertices q).length ∧
      (vertices q).headD (0, 0) = innerPoint q.2.2 ∧
      (vertices q).getLastD (0, 0) = outerPoint (outerDirection q) ∧
      Runs (innerDirection q.2.2) (innerPoint q.2.2) ((vertices q).getD 1 (0, 0)) ∧
      Runs (outerDirection q) ((vertices q).getD ((vertices q).length - 2) (0, 0))
        (outerPoint (outerDirection q)) := by
  have hh := shape_checked q
  simp only [shapeTest, Bool.and_eq_true, decide_eq_true_eq] at hh
  tauto

/-- Every declared instruction is nondegenerate and axis-aligned, within the actual rectangle. -/
theorem segment_shape (q : Key) {s : Segment} (hs : s ∈ curve q) :
    s.start ≠ s.finish ∧ (s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) ∧
      s.start.1 ≤ 50 ∧ s.start.2 ≤ 50 ∧ s.finish.1 ≤ 50 ∧ s.finish.2 ≤ 50 := by
  have hh := shape_checked q
  simp only [shapeTest, Bool.and_eq_true] at hh
  exact of_decide_eq_true (List.all_eq_true.mp hh.2 s hs)

end PushPuzzle.PushFS.Reduction.PortAnnulus
