/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeInterior
public import Push.AcceptanceProgramPolyTimeStages
public import PushS.PortSegments
public import Push.AcceptanceProgram
import all Push.AcceptanceProgram

/-! Standard emission of the actual complete fixed-level compact program. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS Turing.MultiTapeTM

/-- The literal rectangle and segment target of the canonical source. -/
@[expose] def canonicalPointSource (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : PointSource :=
  ⟨p.W + 1, p.H + 1, l.encodedSegments p (l.canonical target)⟩

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout} {p : α → Scales.Parameters}
  {target : α → List Bool} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)
  (htarget : ComputableInPolyTime target enc (encList encBool))

include hl haxes hlevels htarget

/-- The complete canonical target bitmap source emits from the actual layout and endpoint word. -/
private theorem canonicalPointSource_polyTime :
    ComputableInPolyTime (fun a => canonicalPointSource (layout a) (p a) (target a)) enc encPointSource := by
  have hr := PortLayout.computableInPolyTime_canonicalRecipe hl haxes hlevels htarget htarget
  have hf : ComputableInPolyTime (fun r : SegmentRecipe =>
      ({width := r.width, height := r.height, segments := r.targetSegments} : PointSource))
      encSegmentRecipe encPointSource := by fun_prop
  exact hf.comp hr

/-- The strict-interior inventory of the actual canonical target uses the original encoded input. -/
theorem canonicalInterior_polyTime :
    ComputableInPolyTime (fun a => (targetHoles (layout a) (p a) (target a) \ Boundary.frame).card)
      enc encUnary := by
  have hs := canonicalPointSource_polyTime hl haxes hlevels htarget
  exact (interiorCount_polyTime.comp hs).of_enc_eq fun a =>
    congrArg encUnary (interiorCount_correct (canonicalPointSource (layout a) (p a) (target a))).symm

variable (hpages : ∀ a, (layout a).pages.Valid) (hhighest : ∀ a, (layout a).pages.highest ≤ (p a).levels)

include hpages hhighest

/-- Every actual fixed-level template emits directly from the original source input. -/
theorem canonicalTemplates_polyTime :
    ComputableInPolyTime (fun a => schedule (layout a) (p a)
      (targetHoles (layout a) (p a) (target a) \ Boundary.frame).card) enc encTemplates :=
  schedule_polyTime hl haxes hlevels hpages hhighest (canonicalInterior_polyTime hl haxes hlevels htarget)

/-- All actual read quotas and clear lanes of the canonical program emit in standard polynomial time. -/
theorem program_rounds_polyTime :
    ComputableInPolyTime (fun a => (program (layout a) (p a) (target a)).rounds) enc encRounds := by
  have hs := canonicalPointSource_polyTime hl haxes hlevels htarget
  have ht := canonicalTemplates_polyTime hl haxes hlevels htarget hpages hhighest
  have hm := emitFromSource_polyTime.comp (hs.pair ht)
  exact hm.of_enc_eq fun a => congrArg encRounds
    (emitFromSource_correct (canonicalPointSource (layout a) (p a) (target a))
      (schedule (layout a) (p a) (targetHoles (layout a) (p a) (target a) \ Boundary.frame).card)).symm

end PushPuzzle.Push.AcceptanceProgram
