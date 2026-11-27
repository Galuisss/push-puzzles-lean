/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Space.Edge
public import PushPush.Space.DecisionSearch

/-! Polynomial-space maximum-slide reachability for any polynomial-time terminal test. -/

public section
namespace PushPuzzle.PushPush.SearchGraph

open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Complexity

variable {α : Type} (store : α → PushFS.Instance) (goal : α × List Bool → Bool)

/-- The actual maximum-slide relation and its dense edge checker. -/
private def system : DecisionSearch.System store where
  step _ := Step
  edge q := Machine.edge (store q.1, q.2)
  correct I u v := Machine.edge_correct (store I) u v

/-- A reached state satisfies the supplied terminal test. -/
@[expose] def Language : Set α :=
  {I | ∃ s, Reachable (store I).initial s ∧ goal (I, s.bits) = true}

variable {enc : α ↪ List Bool}

theorem language_mem_PSPACE
    (hs : ComputableInPolyTime store enc PushFS.encoding)
    (hg : ComputableInPolyTime goal (encPair enc encBits) encBool) :
    Language store goal ∈ PSPACE enc := by
  change DecisionSearch.Language store goal (system store) ∈ PSPACE enc
  apply DecisionSearch.language_mem_PSPACE store goal (system store) hs hg
  change ComputableInPolyTime
    (fun q : α × List Bool × List Bool => Machine.edge (store q.1, q.2))
    (encPair enc (encPair encBits encBits)) encBool
  fun_prop

end PushPuzzle.PushPush.SearchGraph
