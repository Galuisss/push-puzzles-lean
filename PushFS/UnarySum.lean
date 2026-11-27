/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Polynomial-time summation of the unary lengths used by the geometric compiler. -/

public section

namespace PushPuzzle.PushFS


open Turing.MultiTapeTM ComputableInPolyTime

/-- Concatenate unary counters and count the result using the actual list machines. -/
@[fun_prop] theorem unary_sum_polyTime :
    ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have hrep : ComputableInPolyTime (fun n : ℕ => List.replicate n false)
      encUnary (encList encBool) := replicate id' (const false)
  have hflat : ComputableInPolyTime (fun ns : List ℕ => ns.flatMap fun n => List.replicate n false)
      (encList encUnary) (encList encBool) :=
    flatMapWithInput id' (hrep.comp (snd (encList encUnary) encUnary))
  have hp : ComputableInPolyTime
      (fun ns : List ℕ => (ns.flatMap fun n => List.replicate n false).length)
      (encList encUnary) encUnary := by
    fun_prop
  have he (ns : List ℕ) : (ns.flatMap fun n => List.replicate n false).length = ns.sum := by
    simp
  exact hp.of_enc_eq (fun ns => congrArg encUnary (he ns).symm)

end PushPuzzle.PushFS
