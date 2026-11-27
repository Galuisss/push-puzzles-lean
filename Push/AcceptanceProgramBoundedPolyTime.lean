/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramBounded
public import Push.AcceptanceProgramPolyTimeSets

/-! Standard PT normalization of computed compact programs to their actual rectangle lanes. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS Turing.MultiTapeTM
open scoped PushPuzzle.Push.AcceptanceProgram

@[local fun_prop] private theorem laneCount_polyTime : ComputableInPolyTime
    (fun p : Direction × ℕ × ℕ => Scan.laneCount p.1 p.2.1 p.2.2)
    (encPair (encFinite Direction) (encPair encUnary encUnary)) encUnary := by
  apply ComputableInPolyTime.finite_cases
    (branch := fun side (p : Direction × ℕ × ℕ) => Scan.laneCount side p.2.1 p.2.2)
    (ComputableInPolyTime.fst _ _)
  intro side
  cases side <;> unfold Scan.laneCount <;> fun_prop

/-- Restrict a complete actual read/clear block to its encoded rectangle in standard polynomial time. -/
@[fun_prop] theorem boundedRound_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × Round => p.2.bounded p.1.1 p.1.2)
    (encPair (encPair encUnary encUnary) encRound) encRound := by
  have hread : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Direction × List (ℕ × ℕ) =>
        p.2.2.filter fun a => a.1 < Scan.laneCount p.2.1 p.1.1 p.1.2)
      (encPair (encPair encUnary encUnary) (encPair (encFinite Direction) Scan.encRequests)) Scan.encRequests := by
    unfold Scan.encRequests
    fun_prop
  have hclear : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Direction × Finset ℕ =>
        p.2.2.filter fun lane => lane < Scan.laneCount p.2.1 p.1.1 p.1.2)
      (encPair (encPair encUnary encUnary) (encPair (encFinite Direction) encLaneSet)) encLaneSet := by
    apply laneSet_filterDecide_polyTime (by fun_prop)
    fun_prop
  have h := encRound_elim_polyTime (encP := encPair encUnary encUnary) (encE := encRound)
    (g0 := fun p => .read p.2.1 (p.2.2.filter fun a => a.1 < Scan.laneCount p.2.1 p.1.1 p.1.2))
    (g1 := fun p => .clear p.2.1 (p.2.2.filter fun lane => lane < Scan.laneCount p.2.1 p.1.1 p.1.2))
    (by fun_prop) (by fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨_, block⟩; cases block <;> rfl)

/-- The complete actual block list and its fixed skeleton are normalized in standard polynomial time. -/
@[fun_prop] theorem boundedRounds_polyTime {α : Type} {enc : α ↪ List Bool}
    {width height : α → ℕ} {rounds : α → List Round}
    (hw : ComputableInPolyTime width enc encUnary)
    (hh : ComputableInPolyTime height enc encUnary)
    (hr : ComputableInPolyTime rounds enc encRounds) :
    ComputableInPolyTime (fun a => boundedRounds (width a) (height a) (rounds a)) enc encRounds := by
  unfold boundedRounds encRounds
  apply ComputableInPolyTime.mapWithInput hr
  exact boundedRound_polyTime.comp (((hw.prod hh).comp (ComputableInPolyTime.fst enc encRound)).prod
    (ComputableInPolyTime.snd enc encRound))

end PushPuzzle.Push.AcceptanceProgram
