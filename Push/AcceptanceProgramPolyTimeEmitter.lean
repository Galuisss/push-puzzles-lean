/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeFormula

/-! A standard machine emits all actual compact rounds by finite-prefix tests on the original target bitmap. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction Turing.MultiTapeTM

/-- The actual source rectangle, its literal templates and its explicit target-hole points. -/
structure FormulaInput where
  width : ℕ
  height : ℕ
  stages : List Template
  points : List (ℕ × ℕ)

/-- One actual read round, together with the literal templates preceding it. -/
structure ReadFormula where
  input : FormulaInput
  before : List Template
  side : Direction
  requests : List (ℕ × ℕ)

/-- One actual request and its index among the preceding same-round requests. -/
structure QuotaFormula where
  read : ReadFormula
  index : ℕ
  request : ℕ × ℕ

noncomputable section

/-- Unary rectangle fields and the literal finite target/template data. -/
enc_structure encFormulaInput : FormulaInput where
  width : encUnary, height : encUnary, stages : encTemplates, points : (encList Bitmap.encPoint)

/-- Literal computed read-context fields in their existing compact encodings. -/
enc_structure encReadFormula : ReadFormula where
  input : encFormulaInput, before : encTemplates, side : (encFinite Direction), requests : Scan.encRequests

/-- A complete actual quota query, including its original request and unary index. -/
enc_structure encQuotaFormula : QuotaFormula where
  read : encReadFormula, index : encUnary, request : Bitmap.encPoint

end

/-- A point pays this request exactly when it survived every earlier round and earlier request. -/
@[expose] def quotaPointTest (q : QuotaFormula) (point : ℕ × ℕ) : Bool :=
  let query : PointQuery := ⟨q.read.input.width, q.read.input.height, point⟩
  !stagesTest query q.read.before &&
    !readRegionTest query q.read.side (q.read.requests.take q.index) &&
    prefixTest q.read.side ⟨query, q.request⟩

/-- Count the actual target bitmap points paying one literal request. -/
@[expose] def quotaCount (q : QuotaFormula) : ℕ :=
  (q.read.input.points.filter (quotaPointTest q)).length

/-- Emit a complete read request list by its literal finite-prefix target counts. -/
@[expose] def formulaRequests (q : ReadFormula) : List (ℕ × ℕ) :=
  q.requests.zipIdx.map fun (request, index) => (request.1, quotaCount ⟨q, index, request⟩)

/-- Emit one actual round with its complete literal preceding-template context. -/
@[expose] def formulaRoundNat (q : FormulaInput × ℕ) : Template → Round
  | .read side requests => .read side (formulaRequests ⟨q.1, q.1.stages.take q.2, side, requests⟩)
  | .clear side lanes => .clear side lanes

/-- Emit all compact rounds directly from the original finite target bitmap and actual template list. -/
@[expose] def formulaRoundsNat (input : FormulaInput) : List Round :=
  input.stages.zipIdx.map fun (stage, index) => formulaRoundNat (input, index) stage

/-- Each actual quota-point test is a standard polynomial-time finite-prefix query. -/
@[fun_prop] theorem quotaPointTest_polyTime :
    ComputableInPolyTime (fun p : QuotaFormula × (ℕ × ℕ) => quotaPointTest p.1 p.2)
      (encPair encQuotaFormula Bitmap.encPoint) encBool := by
  unfold quotaPointTest
  dsimp only
  fun_prop

/-- Counting actual target points satisfying a literal quota test is standard polynomial time. -/
@[fun_prop] theorem quotaCount_polyTime : ComputableInPolyTime quotaCount encQuotaFormula encUnary := by
  unfold quotaCount
  fun_prop

/-- Every actual same-round request receives its true computed target-prefix quota in standard polynomial time. -/
@[fun_prop] theorem formulaRequests_polyTime :
    ComputableInPolyTime formulaRequests encReadFormula Scan.encRequests := by
  have hcallback : ComputableInPolyTime (fun p : ReadFormula × ((ℕ × ℕ) × ℕ) =>
      (p.2.1.1, quotaCount ⟨p.1, p.2.2, p.2.1⟩))
      (encPair encReadFormula (encPair Bitmap.encPoint encUnary)) (encPair encUnary encUnary) := by fun_prop
  have hlist : ComputableInPolyTime (fun q : ReadFormula => q.requests.zipIdx)
      encReadFormula (encList (encPair Bitmap.encPoint encUnary)) := by fun_prop
  unfold formulaRequests
  exact ComputableInPolyTime.mapWithInput
    (f := fun (q : ReadFormula) (entry : (ℕ × ℕ) × ℕ) => (entry.1.1, quotaCount ⟨q, entry.2, entry.1⟩)) hlist hcallback

/-- The literal actual read/clear round emitter is a standard polynomial-time machine. -/
@[fun_prop] theorem formulaRoundNat_polyTime :
    ComputableInPolyTime (fun p : (FormulaInput × ℕ) × Template => formulaRoundNat p.1 p.2)
      (encPair (encPair encFormulaInput encUnary) encTemplate) encRound := by
  have hr : ComputableInPolyTime (fun p : (FormulaInput × ℕ) × Direction × List (ℕ × ℕ) =>
      Round.read p.2.1 (formulaRequests ⟨p.1.1, p.1.1.stages.take p.1.2, p.2.1, p.2.2⟩))
      (encPair (encPair encFormulaInput encUnary) (encPair (encFinite Direction) Scan.encRequests)) encRound := by fun_prop
  have hc : ComputableInPolyTime (fun p : (FormulaInput × ℕ) × Direction × Finset ℕ => Round.clear p.2.1 p.2.2)
      (encPair (encPair encFormulaInput encUnary) (encPair (encFinite Direction) encLaneSet)) encRound := by fun_prop
  exact (encTemplate_elim_polyTime hr hc).of_enc_eq (fun p => by cases p.2 <;> rfl)

/-- All actual compact output rounds emit directly in the standard framed round encoding. -/
@[fun_prop] theorem formulaRoundsNat_polyTime :
    ComputableInPolyTime formulaRoundsNat encFormulaInput encRounds := by
  have hargs : ComputableInPolyTime (fun p : FormulaInput × (Template × ℕ) => ((p.1, p.2.2), p.2.1))
      (encPair encFormulaInput (encPair encTemplate encUnary))
      (encPair (encPair encFormulaInput encUnary) encTemplate) := by fun_prop
  have hcallback : ComputableInPolyTime (fun p : FormulaInput × (Template × ℕ) => formulaRoundNat (p.1, p.2.2) p.2.1)
      (encPair encFormulaInput (encPair encTemplate encUnary)) encRound := formulaRoundNat_polyTime.comp hargs
  have hlist : ComputableInPolyTime (fun input : FormulaInput => input.stages.zipIdx)
      encFormulaInput (encList (encPair encTemplate encUnary)) := by fun_prop
  unfold formulaRoundsNat
  exact ComputableInPolyTime.mapWithInput
    (f := fun (input : FormulaInput) (entry : Template × ℕ) => formulaRoundNat (input, entry.2) entry.1)
    hlist hcallback

end PushPuzzle.Push.AcceptanceProgram
