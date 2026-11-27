/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeSets
public import Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortWalkBudget
import all PushS.EndpointWalking
import all PushS.PortStreetSeparation

/-! Standard machines for the actual finite lane and page metadata of fixed-level source families. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open Turing.MultiTapeTM

/-- Unary metadata retained with each actual page-column request. -/
enc_structure encPageColumn : PageColumn where
  column : encUnary, level : encUnary, privateColumn : encBool

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS Turing.MultiTapeTM Push.AcceptanceProgram

attribute [local fun_prop] Coordinates_x_polyTime Coordinates_depth_polyTime Coordinates_length_polyTime
  endpoints_polyTime centers_polyTime auxiliary_polyTime guardColumns_polyTime streetColumns_polyTime
  workingRows_polyTime axisColumns_polyTime
  encEndpoint_side_polyTime encEndpoint_level_polyTime encEndpoint_port_polyTime
  encCoordinates_D_polyTime encCoordinates_W_polyTime encCoordinates_H_polyTime

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)

include hl haxes hlevels

/-- The actual ordinary and gate page-column metadata emits in standard polynomial time. -/
theorem acceptance_pageColumns_polyTime (side : Side) :
    ComputableInPolyTime (fun a => Push.AcceptanceProgram.pageColumns (layout a) (p a) side)
      enc (encList encPageColumn) := by
  have hc := coordinates_polyTime haxes hlevels
  have hD := computableInPolyTime_D haxes hlevels
  have hD' : ComputableInPolyTime (fun q : α × ℕ => (p q.1).D) (encPair enc encUnary) encUnary :=
    hD.comp (ComputableInPolyTime.fst _ _)
  have hbeq : ComputableInPolyTime (fun s : Side => s == side) encSide encBool := .of_finite _
  have hAux : ComputableInPolyTime (fun q : α × Endpoint => auxiliary (coordinates (p q.1)) q.2)
      (encPair enc encEndpoint) (encPair encUnary encUnary) :=
    auxiliary_polyTime.comp ((hc.comp (ComputableInPolyTime.fst _ _)).pair (ComputableInPolyTime.snd _ _))
  have he : ComputableInPolyTime (fun q : α × Endpoint =>
      [({ column := (auxiliary (coordinates (p q.1)) q.2).1, level := q.2.level, privateColumn := false } : PageColumn),
       { column := (auxiliary (coordinates (p q.1)) q.2).2, level := q.2.level, privateColumn := false }])
      (encPair enc encEndpoint) (encList encPageColumn) := by fun_prop
  have hg : ComputableInPolyTime (fun q : α × ℕ =>
      [({ column := (q.2 + 1) * (p q.1).D - 2, level := 1, privateColumn := false } : PageColumn),
       { column := (q.2 + 1) * (p q.1).D + 4, level := 1, privateColumn := true },
       { column := (q.2 + 1) * (p q.1).D + 6, level := 1, privateColumn := false },
       { column := (q.2 + 1) * (p q.1).D + 8, level := 1, privateColumn := false },
       { column := (q.2 + 1) * (p q.1).D + 12, level := 1, privateColumn := false }])
      (encPair enc encUnary) (encList encPageColumn) := by fun_prop
  unfold Push.AcceptanceProgram.pageColumns gateCenterCoordinates Scales.Parameters.x
  dsimp only [EndpointStreet.column]
  fun_prop

/-- Every actual numbered main-axis coordinate emits in the canonical finite lane-set encoding. -/
theorem acceptance_axes_polyTime :
    ComputableInPolyTime (fun a => axes (layout a) (p a)) enc encLaneSet := by
  have hc := coordinates_polyTime haxes hlevels
  exact laneSet_ofList_polyTime.comp (axisColumns_polyTime.comp (hl.pair hc))

/-- Every actual gate-center axis emits in the canonical finite lane-set encoding. -/
theorem acceptance_cores_polyTime :
    ComputableInPolyTime (fun a => cores (layout a) (p a)) enc encLaneSet := by
  have hD := computableInPolyTime_D haxes hlevels
  have hD' : ComputableInPolyTime (fun q : α × ℕ => (p q.1).D) (encPair enc encUnary) encUnary :=
    hD.comp (ComputableInPolyTime.fst _ _)
  have hx : ComputableInPolyTime (fun q : α × ℕ => (q.2 + 1) * (p q.1).D)
      (encPair enc encUnary) encUnary := by fun_prop
  unfold cores gateCenterCoordinates Scales.Parameters.x
  fun_prop

/-- The actual sample columns emit directly from the original gate-center list. -/
theorem acceptance_samples_polyTime :
    ComputableInPolyTime (fun a => samples (layout a) (p a)) enc encLaneSet := by
  have hD := computableInPolyTime_D haxes hlevels
  have hD' : ComputableInPolyTime (fun q : α × ℕ => (p q.1).D) (encPair enc encUnary) encUnary :=
    hD.comp (ComputableInPolyTime.fst _ _)
  have hx : ComputableInPolyTime (fun q : α × ℕ =>
      [(q.2 + 1) * (p q.1).D + 2, (q.2 + 1) * (p q.1).D + 10])
      (encPair enc encUnary) (encList encUnary) := by fun_prop
  unfold samples gateCenterCoordinates Scales.Parameters.x
  fun_prop

/-- The actual recomputed guard columns emit from the complete marked fixed-segment list. -/
theorem acceptance_guards_polyTime :
    ComputableInPolyTime (fun a => guards (layout a) (p a)) enc encLaneSet := by
  have hc := coordinates_polyTime haxes hlevels
  have hf := computableInPolyTime_fixedSegments hl haxes hlevels
  unfold guards acceptanceGuardCoordinates
  fun_prop

/-- The actual complete two-page working-row set emits in the canonical finite lane-set encoding. -/
theorem acceptance_workRows_polyTime :
    ComputableInPolyTime (fun a => workRows (layout a) (p a)) enc encLaneSet := by
  have hc := coordinates_polyTime haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  have hH' : ComputableInPolyTime (fun q : α × ℕ => (p q.1).H) (encPair enc encUnary) encUnary :=
    hH.comp (ComputableInPolyTime.fst _ _)
  have hx : ComputableInPolyTime (fun q : α × ℕ => [q.2, (p q.1).H - q.2])
      (encPair enc encUnary) (encList encUnary) := by fun_prop
  unfold workRows workingDepthCoordinates
  fun_prop

/-- The actual auxiliary columns, after removing main axes and frame columns, emit in standard polynomial time. -/
theorem acceptance_auxiliaries_polyTime :
    ComputableInPolyTime (fun a => auxiliaries (layout a) (p a)) enc encLaneSet := by
  have hc := coordinates_polyTime haxes hlevels
  have hW := computableInPolyTime_W haxes hlevels
  have hstreet := laneSet_ofList_polyTime.comp (streetColumns_polyTime.comp (hl.pair hc))
  have hmain := acceptance_axes_polyTime hl haxes hlevels
  have hframe : ComputableInPolyTime (fun a => ([0, (p a).W] : List ℕ).toFinset) enc encLaneSet := by fun_prop
  have hraw : ComputableInPolyTime (fun a =>
      (streetColumns (layout a) (coordinates (p a))).toFinset \ (axes (layout a) (p a) ∪ ([0, (p a).W] : List ℕ).toFinset))
      enc encLaneSet := by fun_prop
  exact hraw.of_enc_eq (fun a => by
    apply congrArg encLaneSet
    simp [auxiliaries, streetColumnCoordinates])

omit hl

/-- The actual finite central, half-depth and interlevel cut rows emit in standard polynomial time. -/
theorem acceptance_cutRows_polyTime :
    ComputableInPolyTime (fun a => cutRows (p a)) enc encLaneSet := by
  have hD := computableInPolyTime_D haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  have hY := computableInPolyTime_Y haxes hlevels 1
  have hrows : ComputableInPolyTime (fun a => (List.range (M - 1)).flatMap fun j =>
      [((p a).Y (j + 1) + (p a).Y (j + 2)) / 2,
        (p a).H - ((p a).Y (j + 1) + (p a).Y (j + 2)) / 2]) enc (encList encUnary) := by
    apply ComputableInPolyTime.flatMapConst
    intro j _
    have hj := computableInPolyTime_Y haxes hlevels (j + 1)
    have hn := computableInPolyTime_Y haxes hlevels (j + 2)
    fun_prop
  unfold cutRows
  simp only [hlevels]
  fun_prop

/-- The actual neighboring-row family is a fixed list of polynomial-time unary row coordinates. -/
theorem acceptance_neighboringRows_polyTime :
    ComputableInPolyTime (fun a => neighboringRows (p a)) enc encLaneSet := by
  have hH := computableInPolyTime_H haxes hlevels
  have hrows : ComputableInPolyTime (fun a => (List.range M).flatMap fun j =>
      [(p a).Y (j + 1) - 1, (p a).Y (j + 1) + 1,
        (p a).H - ((p a).Y (j + 1) - 1), (p a).H - ((p a).Y (j + 1) + 1)]) enc (encList encUnary) := by
    apply ComputableInPolyTime.flatMapConst
    intro j _
    have hj := computableInPolyTime_Y haxes hlevels (j + 1)
    fun_prop
  unfold neighboringRows
  simp only [hlevels]
  fun_prop

end PushPuzzle.PushS.PortLayout
