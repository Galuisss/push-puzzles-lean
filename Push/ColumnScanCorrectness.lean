/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSoundness
public import Push.ColumnScanSourceLiftComplete
public import Push.ColumnScanPolyTime
public import CslibFrontier.Computability.Complexity.Reduction

/-! The actual committed column reader is a standard polynomial-time reduction. -/

public section
namespace PushPuzzle.Push.ColumnScan

open PushFS PushS Cslib.Complexity

/-- Reach the source corner with enough simultaneous holes in every source column. -/
def cornerQuotas : Set Input := {r | ∃ s : State r.width r.height,
  Reachable r.sourceBoard none r.initial.toState s ∧ s.player = r.sourceCorner ∧
    ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ ((holes s).filter fun q => q.1 = i).card}

/-- The single ordinary destination tests all quotas in one reachable source corner state. -/
theorem Input.compile_solvable_iff_cornerQuotas (r : Input) :
    r.compile.Solvable ↔ r ∈ cornerQuotas := by
  constructor
  · exact r.compile_solvable_implies_corner_quotas
  · rintro ⟨s, hr, hp, hq⟩
    exact r.compile_solvable_of_source_corner_quotas hr hp hq

/-- The concrete dense reader compiles corner quotas to ordinary Push-* in polynomial time. -/
theorem polyTimeReducible_cornerQuotas :
    PolyTimeReducible Input.encoding Push.encoding cornerQuotas Push.solvable :=
  ⟨Input.compile, Input.compile_polyTime, fun r => r.compile_solvable_iff_cornerQuotas.symm⟩

end PushPuzzle.Push.ColumnScan
