/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Space.FiniteEdge
public import PushPush.Space.DecisionSearch

/-! Polynomial-space search with a fixed bound on maximum-slide run lengths. -/

public section
namespace PushPuzzle.PushPush.Finite.SearchGraph

open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Complexity

variable {α : Type} (limit : ℕ) (store : α → PushFS.Instance)
  (goal : α × List Bool → Bool)

/-- The finite-push checker supplies the actual state relation to Savitch search. -/
private def system : DecisionSearch.System store where
  step _ := Finite.Step limit
  edge q := Machine.edge limit (store q.1, q.2)
  correct I u v := Machine.edge_correct limit (store I) u v

/-- A bounded maximum-slide trajectory reaches a terminal state. -/
@[expose] def Language : Set α :=
  {I | ∃ s, Finite.Reachable limit (store I).initial s ∧ goal (I, s.bits) = true}

/-- A polynomial-time terminal test gives a polynomial-space bounded-push language. -/
theorem language_mem_PSPACE {enc : α ↪ List Bool}
    (hs : ComputableInPolyTime store enc PushFS.encoding)
    (hg : ComputableInPolyTime goal (encPair enc encBits) encBool) :
    Language limit store goal ∈ PSPACE enc := by
  change DecisionSearch.Language store goal (system limit store) ∈ PSPACE enc
  apply DecisionSearch.language_mem_PSPACE store goal (system limit store) hs hg
  change ComputableInPolyTime
    (fun q : α × List Bool × List Bool => Machine.edge limit (store q.1, q.2))
    (encPair enc (encPair encBits encBits)) encBool
  fun_prop

end PushPuzzle.PushPush.Finite.SearchGraph
