/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanNormalize
public import PushFS.UnarySum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-! Standard unary polynomial-time normalization of actual sparse request lists. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS Turing.MultiTapeTM

/-- Literal unary lane/quota pairs, with the ordinary framed list encoding. -/
abbrev encRequests : List (ℕ × ℕ) ↪ List Bool := encList (encPair encUnary encUnary)

/-- Actual unary dimensions followed by the complete sparse request list. -/
abbrev encDenseInput : (ℕ × ℕ × List (ℕ × ℕ)) ↪ List Bool :=
  encPair encUnary (encPair encUnary encRequests)

@[fun_prop] theorem quotaAt_polyTime : ComputableInPolyTime
    (fun p : List (ℕ × ℕ) × ℕ => quotaAt p.1 p.2)
    (encPair encRequests encUnary) encUnary := by
  unfold quotaAt encRequests
  fun_prop

private theorem denseQuotas_range (side : Direction) (w h : ℕ) (requests : List (ℕ × ℕ)) :
    denseQuotas side w h requests = (List.range (laneCount side w h)).map (quotaAt requests) := by
  apply List.ext_getElem
  · simp only [denseQuotas_length, List.length_map, List.length_range]
  · intro i hi hi'
    simp only [denseQuotas, List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- Every raw request list is normalized by an actual standard machine; lane validity is needed only for semantic equivalence. -/
@[fun_prop] theorem denseQuotas_polyTime (side : Direction) : ComputableInPolyTime
    (fun p : ℕ × ℕ × List (ℕ × ℕ) => denseQuotas side p.1 p.2.1 p.2.2)
    encDenseInput (encList encUnary) := by
  have hcount : ComputableInPolyTime
      (fun p : ℕ × ℕ × List (ℕ × ℕ) => List.range (laneCount side p.1 p.2.1))
      encDenseInput (encList encUnary) := by
    cases side <;> unfold laneCount encDenseInput <;> fun_prop
  have hargs : ComputableInPolyTime
      (fun p : (ℕ × ℕ × List (ℕ × ℕ)) × ℕ => (p.1.2.2, p.2))
      (encPair encDenseInput encUnary) (encPair encRequests encUnary) := by
    unfold encDenseInput
    fun_prop
  have hraw := quotaAt_polyTime.comp hargs
  have hcallback : ComputableInPolyTime
      (fun p : (ℕ × ℕ × List (ℕ × ℕ)) × ℕ => quotaAt p.1.2.2 p.2)
      (encPair encDenseInput encUnary) encUnary := hraw.of_enc_eq (by intro p; rfl)
  have hmap := ComputableInPolyTime.mapWithInput
    (f := fun (p : ℕ × ℕ × List (ℕ × ℕ)) lane => quotaAt p.2.2 lane) hcount hcallback
  exact hmap.of_enc_eq (fun p => congrArg (encList encUnary) (denseQuotas_range side p.1 p.2.1 p.2.2))

/-- A computed finite side tag also has the same total polynomial-time dense-vector emission. -/
@[fun_prop] theorem denseQuotas_tagged_polyTime : ComputableInPolyTime
    (fun p : Direction × ℕ × ℕ × List (ℕ × ℕ) => denseQuotas p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair (encFinite Direction) encDenseInput) (encList encUnary) := by
  apply ComputableInPolyTime.finite_cases
    (branch := fun side (p : Direction × ℕ × ℕ × List (ℕ × ℕ)) =>
      denseQuotas side p.2.1 p.2.2.1 p.2.2.2)
    (ComputableInPolyTime.fst (encFinite Direction) encDenseInput)
  intro side
  exact (denseQuotas_polyTime side).comp (ComputableInPolyTime.snd _ _)

end PushPuzzle.Push.Scan
