/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTopology
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! Standard polynomial-time emission of the same literal baseline contour and port layout. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal Turing.MultiTapeTM
open scoped Cslib.Complexity.NCL PushPuzzle.PushS

@[fun_prop] theorem computableInPolyTime_crossingToken :
    ComputableInPolyTime (fun p : Crossing × Bool => p.1.token p.2)
      (encPair encCrossing encBool) encToken := by
  unfold Crossing.token
  fun_prop

@[fun_prop] theorem computableInPolyTime_incidenceToken :
    ComputableInPolyTime incidenceToken (NCL.encPort encNat) encToken := by
  unfold incidenceToken
  fun_prop

@[local fun_prop] private theorem pointSub_polyTime :
    ComputableInPolyTime (fun p : Point × Point => p.1 - p.2) (encPair encPoint encPoint) encPoint := by
  change ComputableInPolyTime (fun p : Point × Point => (p.1.1 - p.2.1, p.1.2 - p.2.2)) _ _
  unfold encPoint
  fun_prop

@[fun_prop] theorem computableInPolyTime_outgoingVector (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × NCL.Port ℕ => outgoingVector width p.1 p.2)
      (encPair Graph.encOrthogonalDrawing (NCL.encPort encNat)) encPoint := by
  have hprep := computableInPolyTime_prepare width
  have hroute : ComputableInPolyTime
      (fun p : Graph.OrthogonalDrawing × NCL.Port ℕ => (prepare width p.1).2.getD p.2.edge [])
      (encPair Graph.encOrthogonalDrawing (NCL.encPort encNat)) encRoute := by
    apply ComputableInPolyTime.listGetD_binary (encL := encList encRoute) []
    · unfold Graph.encOrthogonalDrawing at hprep
      fun_prop
    · fun_prop
  unfold outgoingVector
  fun_prop

@[fun_prop] theorem computableInPolyTime_tangentKey :
    ComputableInPolyTime tangentKey encPoint encNat := by unfold tangentKey encPoint; fun_prop

@[fun_prop] theorem computableInPolyTime_fan (width : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => fan width p.1 p.2)
      (encPair encInput encUnary) (encList (NCL.encWeightedPort encNat)) := by
  have hsort := Sort.computableInPolyTime_run (encPair encNat (NCL.encWeightedPort encNat))
    (by fun_prop : ComputableInPolyTime (Prod.fst (α := ℕ) (β := NCL.WeightedPort ℕ))
      (encPair encNat (NCL.encWeightedPort encNat)) encNat) (0, ⟨⟨0, false⟩, 0⟩)
  unfold fan
  fun_prop

private theorem kind_test (b : Bool) :
    (if b then Shuttle.Kind.andGate else .orGate) = .andGate ↔ b = true := by cases b <;> simp

@[fun_prop] theorem computableInPolyTime_coreTemplate :
    ComputableInPolyTime (fun p : ℕ × List (NCL.WeightedPort ℕ) => coreTemplate p.1 p.2)
      (encPair encUnary (encList (NCL.encWeightedPort encNat))) encBlock := by
  dsimp only [coreTemplate]
  simp only [kind_test]
  fun_prop

@[fun_prop] theorem computableInPolyTime_coreBlock (width : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => coreBlock width p.1 p.2)
      (encPair encInput encUnary) encBlock := by unfold coreBlock; fun_prop

@[fun_prop] theorem computableInPolyTime_vertexBlock (width : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => vertexBlock width p.1 p.2)
      (encPair encInput encUnary) encBlock := by unfold vertexBlock; fun_prop

@[fun_prop] theorem computableInPolyTime_edgeVisits (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × ℕ => edgeVisits width p.1 p.2)
      (encPair Graph.encOrthogonalDrawing encUnary) (encList encToken) := by
  have he : ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × ℕ => p.2)
      (encPair Graph.encOrthogonalDrawing encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold edgeVisits
  fun_prop

@[local fun_prop] private theorem optionToList_polyTime {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (Option.toList (α := α)) (encOption enc) (encList enc) :=
  (ComputableInDegree.optionToList enc).computableInPolyTime

@[fun_prop] theorem computableInPolyTime_pairOff :
    ComputableInPolyTime pairOff (encList encToken) (encList (encPair encToken encToken)) := by
  unfold pairOff
  simp only [List.filterMap_eq_flatMap_toList]
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.zipIdx encToken)
  have hmod : ComputableInPolyTime (fun p : List Token × (Token × ℕ) => p.2.2 % 2)
      (encPair (encList encToken) (encPair encToken encUnary)) encUnary := by fun_prop
  fun_prop

/-- Emit the complete actual contour and original incidence labels on every raw input. -/
@[fun_prop] theorem computableInPolyTime_cut (width : ℕ) :
    ComputableInPolyTime (cut width) encInput encCut := by unfold cut; fun_prop

@[fun_prop] theorem computableInPolyTime_rank :
    ComputableInPolyTime (fun p : Cut × Token => p.1.rank p.2) (encPair encCut encToken) encUnary := by
  unfold Cut.rank
  fun_prop

private theorem lowerGroup_polyTime :
    ComputableInPolyTime (fun p : Cut × TokenGroup => p.1.lowerGroup p.2)
      (encPair encCut encTokenGroup) encLowerGroup := by
  have h := encTokenGroup_elim_polyTime (encP := encCut) (encE := encLowerGroup)
    (g0 := fun p => .wire (min (p.1.rank p.2.1) (p.1.rank p.2.2))
      (max (p.1.rank p.2.1) (p.1.rank p.2.2)))
    (g1 := fun p => .gate p.2.1 (p.1.rank p.2.2.1))
    (by fun_prop) (by fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨c, g⟩; cases g <;> rfl)

/-- Number the actual contour by its computed `idxOf` positions in the standard port encoding. -/
@[fun_prop] theorem computableInPolyTime_toLayout :
    ComputableInPolyTime Cut.toLayout encCut encPortLayout := by
  have hgroup := lowerGroup_polyTime
  unfold Cut.toLayout
  fun_prop

/-- The raw baseline compiler is an actual standard polynomial-time function. -/
@[fun_prop] theorem computableInPolyTime_compile (width : ℕ) :
    ComputableInPolyTime (compile width) encInput encPortLayout :=
  computableInPolyTime_toLayout.comp (computableInPolyTime_cut width)

end PushPuzzle.PushS.Comb
