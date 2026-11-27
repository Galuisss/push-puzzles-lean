/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxesReachable
public import Push.WordSourceChecked
public import Push.WordSourceGates
import all Push.WordSourcePoint

/-! Arbitrary accepted physical endpoints project through the actual repaired source to the original word language. -/

public section
namespace PushPuzzle.Push.WordSource

open PushFS PushS Cslib.Complexity

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Every actual admitted accepted source computation yields the original H-word path. -/
theorem mem_of_accepted {x : NCL.HWord.Instance q} (guarded : guard H hq x = true)
    (computation : accepted H hq x) : x ∈ NCL.HWord.language H := by
  rcases gateCenterCoordinates_ne_nil_or_mem H hq guarded with gates | word
  · obtain ⟨t, run, accepted⟩ := accepted_physical H hq computation
    have path := AcceptanceSoundness.canonical_axes_reachable
      (layout H hq x) (scales H hq x) (layout_valid H hq x)
      (highest_le_scales_levels H hq x) (portCount_le_scales_axes H hq x)
      (initialAxes H hq x) (targetAxes H hq x) gates (layout_readerPartners H hq x)
      (initial_ordered H hq guarded).toInputLegal (target_ordered H hq guarded).toInputLegal run accepted
    exact (axes_reachable_iff H hq guarded).mp path
  · exact word

/-- The total actual ordinary point compiler recognizes precisely the original fixed-alphabet word language. -/
theorem checkedCompile_mem_iff (x : NCL.HWord.Instance q) :
    x ∈ NCL.HWord.language H ↔ (checkedCompile H hq x).Solvable := by
  constructor
  · exact checkedCompile_complete H hq
  · intro solution
    obtain ⟨guarded, computation⟩ := (checkedCompile_solvable_iff H hq x).mp solution
    exact mem_of_accepted H hq guarded computation

end PushPuzzle.Push.WordSource
