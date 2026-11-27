/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Basic
public import PushS.Boundary

/-! Fixed wall-free YES and NO instances for total reductions. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS

namespace Reduction

/-- The one-cell empty board is already solved. -/
def accept : Instance :=
  Instance.ofState ∅ (⟨(0, 0), ∅⟩ : State 1 1) (by simp) (by simp)

/-- The only box starts on the right edge and is required at the left edge. -/
def reject : Instance :=
  Instance.ofState {(0, 0)} (⟨(0, 0), {(1, 0)}⟩ : State 2 1)
    (by decide +kernel) (by simp)

/-- A box on the right edge cannot reach the specified left-edge goal. -/
theorem reject_not_solvable : ¬reject.Solvable := by
  rintro ⟨t, hr, hgoal⟩
  have hgoals : Disjoint reject.board.goals (Boundary.edge .east) := by decide +kernel
  have ht : Disjoint t.boxes (Boundary.edge .east) := by
    rw [hgoal]
    exact hgoals
  have hs := Boundary.reachable_edge_empty hr .east ht
  have hb : ((1, 0) : Cell 2 1) ∈ reject.initial.boxes := by
    change ((1, 0) : Cell 2 1) ∈ ({(1, 0)} : Finset (Cell 2 1))
    exact Finset.mem_singleton_self _
  have he : ((1, 0) : Cell 2 1) ∈ Boundary.edge .east := by decide +kernel
  exact Finset.disjoint_left.mp hs hb he

end Reduction
end PushPuzzle.PushS
