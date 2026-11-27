/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.SearchGraph
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability

/-!
# Push-kFS and Push-*FS belong to PSPACE

The dynamic state is represented by two dense cell bitmaps and a tag. The
polynomial-time edge test checks the entire consecutive run even when push
length is unbounded. Savitch's explicit-stack machine decides reachability
within polynomial work space under the same fixed dense instance encoding.

## Main results

* `solvable_mem_PSPACE`: membership for every fixed cap, including no cap.
-/

public section

open Cslib.Complexity

namespace PushPuzzle.PushFS


open Turing.MultiTapeTM ComputableInPolyTime

namespace SearchGraph

@[fun_prop] theorem width_polyTime :
    ComputableInPolyTime width encoding encUnary := by
  unfold width
  fun_prop

@[fun_prop] theorem accept_polyTime :
    ComputableInPolyTime accept encoding encBits := by
  unfold accept
  fun_prop

@[fun_prop] theorem wordEdge_polyTime (cap : Option ℕ) :
    ComputableInPolyTime (wordEdge cap) (encPair encoding (encPair encBits encBits)) encBool := by
  unfold wordEdge
  have he := Machine.edge_polyTime cap
  have hg := Machine.goal_polyTime
  fun_prop

@[fun_prop] theorem start_polyTime :
    ComputableInPolyTime (fun I : Instance => false :: I.initial.bits) encoding encBits := by
  have hi : ComputableInPolyTime (fun I : Instance => I.initial.bits) encoding encBits :=
    Machine.initial_state_encoding_polyTime
  fun_prop

/-- All Savitch parameters are computed in polynomial time from the explicit board. -/
private theorem arguments_polyTime :
    ComputableInPolyTime
      (fun I : Instance => (I, width I, width I, false :: I.initial.bits, accept I))
      encoding (Cslib.Reachability.encArgs encoding) := by
  unfold Cslib.Reachability.encArgs
  fun_prop

/-- The search uses polynomial work space, including the edge checker and input preparation. -/
private theorem solve_polySpace (cap : Option ℕ) :
    ∃ t s, PolyBounded (fun I => (encoding I).length) s ∧
      ComputableInTimeAndSpace (solve cap) encoding encBool t s := by
  apply Cslib.Reachability.exists_polyBounded_space_savitch
    (wordEdge_polyTime cap) arguments_polyTime
  · intro I
    simp [width, Instance.area]
  · intro I
    simp [accept, width]

end SearchGraph

/-- Storage reachability is in PSPACE for every fixed finite or unlimited push cap. -/
theorem solvable_mem_PSPACE (cap : Option ℕ) : solvable cap ∈ PSPACE encoding := by
  obtain ⟨t, s, hs, hmachine⟩ := SearchGraph.solve_polySpace cap
  exact mem_PSPACE_of_computableInTimeAndSpace hs hmachine
    (fun I => (SearchGraph.solve_correct cap I).symm)

end PushPuzzle.PushFS
