/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeSets
public import Push.AcceptanceProgramEmissionFormula
public import Push.AcceptanceProgramPrefix
public import PushFS.Reduction.Bitmap

/-! Explicit unary coordinate tests for the actual compact emitter's finite-prefix quota formula. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction Turing.MultiTapeTM

/-- A literal point query in a unary rectangle. -/
structure PointQuery where
  width : ℕ
  height : ℕ
  point : ℕ × ℕ

/-- A literal bounded-prefix query on the same rectangle. -/
structure PrefixQuery where
  query : PointQuery
  request : ℕ × ℕ

/-- Unary dimensions, actual query point and literal prefix fields. -/
enc_structure encPointQuery : PointQuery where
  width : encUnary, height : encUnary, point : Bitmap.encPoint

/-- Actual point queries followed by a lane/span pair. -/
enc_structure encPrefixQuery : PrefixQuery where
  query : encPointQuery, request : (encPair encUnary encUnary)

/-- Perpendicular lane coordinate of an explicit natural-coordinate point. -/
@[expose] def pointLane (side : Direction) (point : ℕ × ℕ) : ℕ :=
  match side with
  | .north | .south => point.1
  | .east | .west => point.2

/-- Test exactly the literal coordinate prefix of a real read template. -/
@[expose] def prefixTest (side : Direction) (q : PrefixQuery) : Bool :=
  match side with
  | .north => decide (q.query.point.1 = q.request.1 ∧ q.query.point.2 < q.request.2)
  | .south => decide (q.query.point.1 = q.request.1 ∧ q.query.height - 1 - q.query.point.2 < q.request.2)
  | .west => decide (q.query.point.2 = q.request.1 ∧ q.query.point.1 < q.request.2)
  | .east => decide (q.query.point.2 = q.request.1 ∧ q.query.width - 1 - q.query.point.1 < q.request.2)

/-- Test whether one actual same-direction request family touches the point. -/
@[expose] def readRegionTest (q : PointQuery) (side : Direction) (requests : List (ℕ × ℕ)) : Bool :=
  requests.any fun request => prefixTest side ⟨q, request⟩

/-- Test the actual coordinate region of one literal read or clear block. -/
@[expose] def templateTest (q : PointQuery) : Template → Bool
  | .read side requests => readRegionTest q side requests
  | .clear side lanes => decide (pointLane side q.point ∈ lanes)

/-- Test whether any actual preceding compact stage has touched the point. -/
@[expose] def stagesTest (q : PointQuery) (stages : List Template) : Bool := stages.any (templateTest q)

/-- The natural-coordinate query agrees exactly with the genuine finite line prefix. -/
theorem prefixTest_cell {w h : ℕ} (side : Direction) (lane span : ℕ) (q : Cell w h) :
    prefixTest side ⟨⟨w, h, (q.1.val, q.2.val)⟩, (lane, span)⟩ = true ↔
      q ∈ (Scan.lineCells side lane).take span := by
  cases side <;> simp only [prefixTest, decide_eq_true_eq, mem_line_prefix, Direction.lane, prefixRank]

/-- The explicit request-family test agrees with the actual finite read region. -/
theorem readRegionTest_cell {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ)) (q : Cell w h) :
    readRegionTest ⟨w, h, (q.1.val, q.2.val)⟩ side requests = true ↔ q ∈ readRegion side requests := by
  simp only [readRegionTest, List.any_eq_true, mem_readRegion]
  constructor
  · rintro ⟨⟨lane, span⟩, hr, hp⟩
    exact ⟨(lane, span), hr, (mem_line_prefix side lane span q).mp ((prefixTest_cell side lane span q).mp hp)⟩
  · rintro ⟨⟨lane, span⟩, hr, hp⟩
    exact ⟨(lane, span), hr, (prefixTest_cell side lane span q).mpr ((mem_line_prefix side lane span q).mpr hp)⟩

/-- The literal read/clear region test has exactly the existing finite-set semantics. -/
theorem templateTest_cell {w h : ℕ} (stage : Template) (q : Cell w h) :
    templateTest ⟨w, h, (q.1.val, q.2.val)⟩ stage = true ↔ q ∈ stage.region := by
  cases stage with
  | read side requests => exact readRegionTest_cell side requests q
  | clear side lanes =>
    have hlane : pointLane side (q.1.val, q.2.val) = side.lane q := by cases side <;> rfl
    change decide (pointLane side (q.1.val, q.2.val) ∈ lanes) = true ↔
      q ∈ (Finset.univ : Finset (Cell w h)).filter (fun p => side.lane p ∈ lanes)
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hlane, decide_eq_true_eq]

/-- The complete prior-stage test has exactly the existing touched-region semantics. -/
theorem stagesTest_cell {w h : ℕ} (stages : List Template) (q : Cell w h) :
    stagesTest ⟨w, h, (q.1.val, q.2.val)⟩ stages = true ↔ q ∈ allRegions stages := by
  simp only [stagesTest, List.any_eq_true, templateTest_cell, mem_allRegions]

/-- Actual natural point lanes are standard unary computations on each fixed side. -/
@[fun_prop] theorem pointLane_polyTime (side : Direction) :
    ComputableInPolyTime (pointLane side) Bitmap.encPoint encUnary := by
  cases side <;> unfold pointLane Bitmap.encPoint <;> fun_prop

/-- A computed side tag also computes the actual unary point lane. -/
@[fun_prop] theorem pointLane_tagged_polyTime :
    ComputableInPolyTime (fun p : Direction × (ℕ × ℕ) => pointLane p.1 p.2)
      (encPair (encFinite Direction) Bitmap.encPoint) encUnary := by
  apply ComputableInPolyTime.finite_cases (branch := fun side p => pointLane side p.2)
    (ComputableInPolyTime.fst _ _)
  intro side
  exact (pointLane_polyTime side).comp (ComputableInPolyTime.snd _ _)

/-- Every actual fixed-side literal prefix test has a standard polynomial-time unary machine. -/
@[fun_prop] theorem prefixTest_polyTime (side : Direction) :
    ComputableInPolyTime (prefixTest side) encPrefixQuery encBool := by
  cases side <;> unfold prefixTest <;> fun_prop

/-- The same actual prefix test works uniformly on a computed finite direction tag. -/
@[fun_prop] theorem prefixTest_tagged_polyTime :
    ComputableInPolyTime (fun p : Direction × PrefixQuery => prefixTest p.1 p.2)
      (encPair (encFinite Direction) encPrefixQuery) encBool := by
  apply ComputableInPolyTime.finite_cases (branch := fun side p => prefixTest side p.2)
    (ComputableInPolyTime.fst _ _)
  intro side
  exact (prefixTest_polyTime side).comp (ComputableInPolyTime.snd _ _)

/-- Testing a literal request family against one actual point is standard polynomial time. -/
@[fun_prop] theorem readRegionTest_polyTime :
    ComputableInPolyTime (fun p : PointQuery × Direction × List (ℕ × ℕ) => readRegionTest p.1 p.2.1 p.2.2)
      (encPair encPointQuery (encPair (encFinite Direction) Scan.encRequests)) encBool := by
  let encInput := encPair encPointQuery (encPair (encFinite Direction) Scan.encRequests)
  have hargs : ComputableInPolyTime (fun p : (PointQuery × Direction × List (ℕ × ℕ)) × (ℕ × ℕ) =>
      (p.1.2.1, ({query := p.1.1, request := p.2} : PrefixQuery)))
      (encPair encInput (encPair encUnary encUnary)) (encPair (encFinite Direction) encPrefixQuery) := by
    unfold encInput
    fun_prop
  have htest := prefixTest_tagged_polyTime.comp hargs
  have hl : ComputableInPolyTime (fun p : PointQuery × Direction × List (ℕ × ℕ) => p.2.2)
      encInput Scan.encRequests := by unfold encInput; fun_prop
  exact ComputableInPolyTime.anyWithInput (test := fun (p : PointQuery × Direction × List (ℕ × ℕ)) request => prefixTest p.2.1 ⟨p.1, request⟩) hl htest

/-- The actual read/clear template test has a standard polynomial-time machine in its compact encoding. -/
@[fun_prop] theorem templateTest_polyTime :
    ComputableInPolyTime (fun p : PointQuery × Template => templateTest p.1 p.2)
      (encPair encPointQuery encTemplate) encBool := by
  have hr : ComputableInPolyTime
      (fun p : PointQuery × Direction × List (ℕ × ℕ) => readRegionTest p.1 p.2.1 p.2.2)
      (encPair encPointQuery (encPair (encFinite Direction) Scan.encRequests)) encBool := readRegionTest_polyTime
  have hc : ComputableInPolyTime
      (fun p : PointQuery × Direction × Finset ℕ => decide (pointLane p.2.1 p.1.point ∈ p.2.2))
      (encPair encPointQuery (encPair (encFinite Direction) encLaneSet)) encBool := by
    have hx : ComputableInPolyTime (fun p : PointQuery × Direction × Finset ℕ => (p.2.2, pointLane p.2.1 p.1.point))
        (encPair encPointQuery (encPair (encFinite Direction) encLaneSet)) (encPair encLaneSet encUnary) := by fun_prop
    exact laneSet_mem_polyTime.comp hx
  exact (encTemplate_elim_polyTime hr hc).of_enc_eq (fun p => by cases p.2 <;> rfl)

/-- Testing all actual preceding templates is a standard polynomial-time list search. -/
@[fun_prop] theorem stagesTest_polyTime :
    ComputableInPolyTime (fun p : PointQuery × List Template => stagesTest p.1 p.2)
      (encPair encPointQuery encTemplates) encBool := by
  have hargs : ComputableInPolyTime (fun p : (PointQuery × List Template) × Template => (p.1.1, p.2))
      (encPair (encPair encPointQuery encTemplates) encTemplate) (encPair encPointQuery encTemplate) := by fun_prop
  have htest : ComputableInPolyTime (fun p : (PointQuery × List Template) × Template => templateTest p.1.1 p.2)
      (encPair (encPair encPointQuery encTemplates) encTemplate) encBool := templateTest_polyTime.comp hargs
  exact ComputableInPolyTime.anyWithInput (test := fun (p : PointQuery × List Template) stage => templateTest p.1 stage)
    (ComputableInPolyTime.snd _ _) htest

end PushPuzzle.Push.AcceptanceProgram
