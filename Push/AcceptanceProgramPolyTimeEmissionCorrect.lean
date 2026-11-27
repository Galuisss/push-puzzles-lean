/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimePoints

/-! The standard finite-prefix machine emits exactly the existing stateful compact program. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS Turing.MultiTapeTM

/-- The explicit point test is exactly the actual surviving-target prefix predicate. -/
private theorem quotaPointTest_cell {w h : ℕ} (stages before : List Template) (side : Direction)
    (requests : List (ℕ × ℕ)) (points : List (ℕ × ℕ)) (i : ℕ) (request : ℕ × ℕ) (q : Cell w h) :
    quotaPointTest ⟨⟨⟨w, h, stages, points⟩, before, side, requests⟩, i, request⟩ (cellPoint w h q) = true ↔
      q ∉ allRegions before ∧ q ∉ readRegion side (requests.take i) ∧
        q ∈ (Scan.lineCells side request.1).take request.2 := by
  change quotaPointTest ⟨⟨⟨w, h, stages, points⟩, before, side, requests⟩, i, request⟩ (q.1.val, q.2.val) = true ↔ _
  rcases request with ⟨lane, span⟩
  have hs := stagesTest_cell before q
  have hr := readRegionTest_cell side (requests.take i) q
  simp only [quotaPointTest, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    prefixTest_cell side lane span q]
  tauto

/-- Actual point-list counting computes precisely the existing finite-cell quota. -/
private theorem quotaCount_formula {w h : ℕ} (stages before : List Template) (side : Direction)
    (requests : List (ℕ × ℕ)) (points : List (ℕ × ℕ)) (E : Finset (Cell w h))
    (hn : points.Nodup) (he : points.toFinset = E.map (cellPoint w h)) (i : ℕ) (request : ℕ × ℕ) :
    quotaCount ⟨⟨⟨w, h, stages, points⟩, before, side, requests⟩, i, request⟩ =
      (E.filter fun q => q ∉ allRegions before ∧ q ∉ readRegion side (requests.take i) ∧
        q ∈ (Scan.lineCells side request.1).take request.2).card := by
  unfold quotaCount
  rw [point_filter_count points E hn he]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q _
  exact quotaPointTest_cell stages before side requests points i request q

/-- The machine's actual same-direction request list is the exact finite-prefix quota formula. -/
private theorem formulaRequests_correct {w h : ℕ} (stages before : List Template) (side : Direction)
    (requests : List (ℕ × ℕ)) (points : List (ℕ × ℕ)) (E : Finset (Cell w h))
    (hn : points.Nodup) (he : points.toFinset = E.map (cellPoint w h)) :
    formulaRequests ⟨⟨w, h, stages, points⟩, before, side, requests⟩ = quotaRequests before side requests E := by
  unfold formulaRequests quotaRequests
  rw [List.mapIdx_eq_zipIdx_map]
  apply List.map_congr_left
  rintro ⟨request, i⟩ _
  exact congrArg (Prod.mk request.1) (quotaCount_formula stages before side requests points E hn he i request)

/-- The machine's actual read or clear round agrees exactly with the existing finite-prefix round formula. -/
private theorem formulaRoundNat_correct {w h : ℕ} (stages : List Template) (stage : Template)
    (i : ℕ)
    (points : List (ℕ × ℕ)) (E : Finset (Cell w h))
    (hn : points.Nodup) (he : points.toFinset = E.map (cellPoint w h)) :
    formulaRoundNat (⟨w, h, stages, points⟩, i) stage = formulaRound (stages.take i) stage E := by
  cases stage with
  | read side requests =>
    exact congrArg (Round.read side) (formulaRequests_correct stages (stages.take i) side requests points E hn he)
  | clear => rfl

/-- The complete standard machine output is exactly the existing actual compact-round emitter. -/
theorem formulaRoundsNat_correct {w h : ℕ} (stages : List Template) (points : List (ℕ × ℕ))
    (E : Finset (Cell w h)) (hn : points.Nodup) (he : points.toFinset = E.map (cellPoint w h)) :
    formulaRoundsNat ⟨w, h, stages, points⟩ = (emit stages E).rounds := by
  rw [emit_rounds_formula]
  unfold formulaRoundsNat formulaRounds
  rw [List.mapIdx_eq_zipIdx_map]
  apply List.map_congr_left
  rintro ⟨stage, i⟩ _
  exact formulaRoundNat_correct stages stage i points E hn he

/-- Emit the actual finite target bitmap and then its complete compact round list. -/
@[expose] def emitFromSource (p : PointSource × List Template) : List Round :=
  formulaRoundsNat ⟨p.1.width, p.1.height, p.2, holePoints p.1⟩

/-- The actual segment-target compact emitter uses a standard polynomial-time machine on all raw inputs. -/
@[fun_prop] theorem emitFromSource_polyTime :
    ComputableInPolyTime emitFromSource (encPair encPointSource encTemplates) encRounds := by
  have hargs : ComputableInPolyTime (fun p : PointSource × List Template =>
      ({width := p.1.width, height := p.1.height, stages := p.2, points := holePoints p.1} : FormulaInput))
      (encPair encPointSource encTemplates) encFormulaInput := by fun_prop
  exact formulaRoundsNat_polyTime.comp hargs

/-- The machine emits precisely the existing compact rounds on the actual finite target-hole set. -/
theorem emitFromSource_correct (source : PointSource) (stages : List Template) :
    emitFromSource (source, stages) =
      (emit stages (SegmentRecipe.holes source.width source.height source.segments)).rounds :=
  formulaRoundsNat_correct stages (holePoints source) _ (holePoints_nodup source) (holePoints_finset source)

end PushPuzzle.Push.AcceptanceProgram
