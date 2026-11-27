/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanNormalizePolyTime
public import Push.CyclicSourceLine
public import Push.CyclicTurnProgram

/-! Standard polynomial-time transport of literal sparse lane/quota request lists. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS Turing.MultiTapeTM

@[fun_prop] theorem sourceLane_polyTime : ComputableInPolyTime
    (fun p : Direction × ℕ => sourceLane p.1 p.2)
    (encPair (encFinite Direction) encUnary) encUnary := by
  apply ComputableInPolyTime.finite_cases
    (branch := fun side (p : Direction × ℕ) => sourceLane side p.2)
    (ComputableInPolyTime.fst (encFinite Direction) encUnary)
  intro side
  cases side <;> unfold sourceLane <;> fun_prop

@[fun_prop] theorem turnLane_polyTime : ComputableInPolyTime
    (fun p : ℕ × Direction × ℕ => turnLane p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair (encFinite Direction) encUnary)) encUnary := by
  have hside : ComputableInPolyTime (fun p : ℕ × Direction × ℕ => p.2.1)
      (encPair encUnary (encPair (encFinite Direction) encUnary)) (encFinite Direction) := by fun_prop
  apply ComputableInPolyTime.finite_cases
    (branch := fun side (p : ℕ × Direction × ℕ) => turnLane p.1 side p.2.2) hside
  intro side
  cases side <;> unfold turnLane <;> fun_prop

/-- Translate the actual requests to their embedded source rows or columns. -/
@[expose] def sourceRequests (side : Direction) (requests : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  requests.map fun a => (sourceLane side a.1, a.2)

/-- Turn the complete request list, retaining every read quota. -/
@[expose] def turnRequests (w : ℕ) (side : Direction) (requests : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  requests.map fun a => (turnLane w side a.1, a.2)

@[fun_prop] theorem sourceRequests_polyTime : ComputableInPolyTime
    (fun p : Direction × List (ℕ × ℕ) => sourceRequests p.1 p.2)
    (encPair (encFinite Direction) Scan.encRequests) Scan.encRequests := by
  unfold sourceRequests Scan.encRequests
  apply ComputableInPolyTime.mapWithInput
  · fun_prop
  · fun_prop

@[fun_prop] theorem turnRequests_polyTime : ComputableInPolyTime
    (fun p : ℕ × Direction × List (ℕ × ℕ) => turnRequests p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair (encFinite Direction) Scan.encRequests)) Scan.encRequests := by
  unfold turnRequests Scan.encRequests
  apply ComputableInPolyTime.mapWithInput
  · fun_prop
  · fun_prop

end PushPuzzle.Push.Cyclic
