/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSource
public import Push.PartnerGates

/-! Actual nontrivial word-source layouts contain a retained core gate. -/

public section
namespace PushPuzzle.Push.WordSource

open PushS Cslib.Complexity

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- An admitted source with an empty actual contour already has its original target word reachable. -/
private theorem mem_of_raw_portCount_zero {x : NCL.HWord.Instance q} (guarded : guard H hq x = true)
    (empty : (rawLayout H hq x).portCount = 0) : x ∈ NCL.HWord.language H := by
  have bound := layout_portCount_le H hq x
  rw [empty] at bound
  have finalEmpty : (layout H hq x).portCount = 0 := by omega
  have initial : initialAxes H hq x = [] :=
    List.eq_nil_of_length_eq_zero ((initialAxes_length H hq x).trans finalEmpty)
  have target : targetAxes H hq x = [] :=
    List.eq_nil_of_length_eq_zero ((targetAxes_length H hq x).trans finalEmpty)
  apply (axes_reachable_iff H hq guarded).mp
  rw [initial, target]

/-- Every nonempty actual contour retains a gate middle axis through the complete partner repair. -/
private theorem gateCenterCoordinates_ne_nil_of_raw_pos {x : NCL.HWord.Instance q}
    (nonempty : 0 < (rawLayout H hq x).portCount) : (layout H hq x).gateCenterCoordinates ≠ [] := by
  have rawGate : ∃ kind first, LowerGroup.gate kind first ∈ (rawLayout H hq x).lowerGroups :=
    Partner.compile_gate_exists_of_portCount_pos _ _ nonempty
  exact Partner.gateCenterCoordinates_ne_nil (Partner.Cuts.repair_gate_exists _ rawGate)

/-- Each admitted actual hard source either contains a core gate or already has the original word path. -/
theorem gateCenterCoordinates_ne_nil_or_mem {x : NCL.HWord.Instance q} (guarded : guard H hq x = true) :
    (layout H hq x).gateCenterCoordinates ≠ [] ∨ x ∈ NCL.HWord.language H := by
  by_cases empty : (rawLayout H hq x).portCount = 0
  · exact Or.inr (mem_of_raw_portCount_zero H hq guarded empty)
  · exact Or.inl (gateCenterCoordinates_ne_nil_of_raw_pos H hq (Nat.pos_of_ne_zero empty))

end PushPuzzle.Push.WordSource
