/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.EdgeTrace

/-! Finite interval certificates for thickened orthogonal segment separation. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction


/-- Points whose two coordinate differences are at most the given margin. -/
def Nearby (margin : ℕ) (p q : ℕ × ℕ) : Prop :=
  p.1 ≤ q.1 + margin ∧ q.1 ≤ p.1 + margin ∧
    p.2 ≤ q.2 + margin ∧ q.2 ≤ p.2 + margin

/-- Certify separation by disjoint coordinate intervals, including a chosen margin. -/
def Segment.gapTest (margin : ℕ) (s t : Segment) : Bool :=
  decide (max s.start.1 s.finish.1 + margin < min t.start.1 t.finish.1 ∨
    max t.start.1 t.finish.1 + margin < min s.start.1 s.finish.1 ∨
    max s.start.2 s.finish.2 + margin < min t.start.2 t.finish.2 ∨
    max t.start.2 t.finish.2 + margin < min s.start.2 s.finish.2)

/-- Every represented point lies in the segment's literal coordinate intervals. -/
theorem Segment.coordinate_bounds {s : Segment} {p : ℕ × ℕ} (hp : s.Contains p) :
    min s.start.1 s.finish.1 ≤ p.1 ∧ p.1 ≤ max s.start.1 s.finish.1 ∧
      min s.start.2 s.finish.2 ≤ p.2 ∧ p.2 ≤ max s.start.2 s.finish.2 := by
  rcases hp with hp | hp <;> omega

/-- A checked interval gap excludes all pairs of trace points within the given margin. -/
theorem Segment.not_nearby_of_gap {s t : Segment} {margin : ℕ}
    (hg : s.gapTest margin t = true) {p q : ℕ × ℕ}
    (hp : s.Contains p) (hq : t.Contains q) : ¬Nearby margin p q := by
  have hs := s.coordinate_bounds hp
  have ht := t.coordinate_bounds hq
  have hg := of_decide_eq_true hg
  unfold Nearby
  omega

end PushPuzzle.PushFS.Reduction
