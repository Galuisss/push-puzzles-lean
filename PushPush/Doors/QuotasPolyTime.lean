/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Quotas

/-! Standard polynomial-time emission of the complete seven-round physical reader program. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open Turing.MultiTapeTM
open Push.AcceptanceProgram
open scoped Push.AcceptanceProgram

@[fun_prop] theorem rackProbeRows_polyTime :
    ComputableInPolyTime rackProbeRows encLayout (encList encUnary) := by
  unfold rackProbeRows
  fun_prop

@[fun_prop] theorem markerRows_polyTime :
    ComputableInPolyTime markerRows encLayout (encList encUnary) := by
  unfold markerRows
  fun_prop

@[fun_prop] theorem dividerNeighbors_polyTime :
    ComputableInPolyTime dividerNeighbors encLayout (encList encUnary) := by
  unfold dividerNeighbors
  fun_prop

@[fun_prop] theorem probeRequests_polyTime :
    ComputableInPolyTime probeRequests encLayout Push.Scan.encRequests := by
  unfold probeRequests
  fun_prop

@[fun_prop] theorem finalRequests_polyTime :
    ComputableInPolyTime finalRequests encLayout Push.Scan.encRequests := by
  unfold finalRequests
  fun_prop

-- Certify all seven template constructors and their list payloads together.
set_option maxHeartbeats 800000 in
@[fun_prop] theorem quotaTemplates_polyTime :
    ComputableInPolyTime quotaTemplates encLayout encTemplates := by
  unfold quotaTemplates
  fun_prop

/-- All actual reference holes, enumerated once as bounded unary coordinate pairs. -/
def referencePoints (L : Layout) : List (ℕ × ℕ) :=
  (rectanglePoints L.width L.height).filter fun p => !stockTest (L.goalList, p)

private theorem referencePoints_nodup (L : Layout) : L.referencePoints.Nodup :=
  (rectanglePoints_nodup L.width L.height).filter _

theorem mem_referencePoints (L : Layout) (p : ℕ × ℕ) :
    p ∈ L.referencePoints ↔ (p.1 < L.width ∧ p.2 < L.height) ∧ p ∉ L.goalsRaw := by
  simp only [referencePoints, List.mem_filter, mem_rectanglePoints,
    stockTest, List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not]
  rw [← L.goalList_toFinset]
  simp only [List.mem_toFinset]

private theorem referencePoints_finset (L : Layout) :
    L.referencePoints.toFinset = L.referenceHoles.map (cellPoint L.width L.height) := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [List.mem_toFinset, mem_referencePoints, Finset.mem_map]
  constructor
  · rintro ⟨⟨hx, hy⟩, hp⟩
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
    exact Finset.mem_compl.mpr (fun h => hp ((L.mem_raster _ _).mp h))
  · rintro ⟨q, hq, he⟩
    have hx : q.1.val = x := congrArg Prod.fst he
    have hy : q.2.val = y := congrArg Prod.snd he
    rw [← hx, ← hy]
    exact ⟨⟨q.1.isLt, q.2.isLt⟩,
      fun h => Finset.mem_compl.mp hq ((L.mem_raster _ _).mpr h)⟩

@[fun_prop] theorem referencePoints_polyTime :
    ComputableInPolyTime referencePoints encLayout (encList encPoint) := by
  have hr : ComputableInPolyTime (fun L : Layout => rectanglePoints L.width L.height)
      encLayout (encList encPoint) := by fun_prop
  unfold referencePoints
  fun_prop

/-- The finite target points and literal prefix templates fed to the existing standard emitter. -/
def quotaFormula (L : Layout) : FormulaInput :=
  ⟨L.width, L.height, L.quotaTemplates, L.referencePoints⟩

@[fun_prop] theorem quotaFormula_polyTime :
    ComputableInPolyTime quotaFormula encLayout encFormulaInput := by
  unfold quotaFormula
  fun_prop

/-- All seven complete rounds are emitted in standard machine polynomial time. -/
theorem quotaProgram_rounds_polyTime :
    ComputableInPolyTime (fun L : Layout => L.quotaProgram.rounds) encLayout encRounds := by
  have hm := formulaRoundsNat_polyTime.comp quotaFormula_polyTime
  exact hm.of_enc_eq fun L => congrArg encRounds
    (formulaRoundsNat_correct L.quotaTemplates L.referencePoints L.referenceHoles
      L.referencePoints_nodup L.referencePoints_finset).symm

end PushPuzzle.PushPush.Doors.Layout
