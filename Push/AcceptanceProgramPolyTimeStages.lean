/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimePages
public import Push.AcceptanceProgramStock
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramNarrowSignals

/-! Standard emission of the actual compact acceptance-stage lane families. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)

include hl haxes hlevels

private theorem live_polyTime (side : Side) :
    ComputableInPolyTime (fun a => live (layout a) (p a) side) enc encLaneSet := by
  have hc := acceptance_pageColumns_polyTime hl haxes hlevels side
  unfold live
  simp only [hlevels]
  fun_prop

private theorem levelColumns_polyTime (side : Side) (j : ℕ) :
    ComputableInPolyTime (fun a => levelColumns (layout a) (p a) side j) enc encLaneSet := by
  have hc := acceptance_pageColumns_polyTime hl haxes hlevels side
  unfold levelColumns
  fun_prop

/-- The actual private gate-column set emits from its literal page metadata. -/
private theorem privateColumns_polyTime :
    ComputableInPolyTime (fun a => privateColumns (layout a) (p a)) enc encLaneSet := by
  have hc := acceptance_pageColumns_polyTime hl haxes hlevels .lower
  unfold privateColumns
  fun_prop

/-- The actual retained-row set emits from its working, cut and central marker rows. -/
private theorem keepRows_polyTime :
    ComputableInPolyTime (fun a => keepRows (layout a) (p a)) enc encLaneSet := by
  have hw := acceptance_workRows_polyTime hl haxes hlevels
  have hc := acceptance_cutRows_polyTime haxes hlevels
  have hD := computableInPolyTime_D haxes hlevels
  unfold keepRows
  fun_prop

omit hl in
/-- The literal interior side-band clear family emits from its actual computed hole budget. -/
private theorem sideBands_polyTime {k : α → ℕ} (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a => sideBands (p a) (k a)) enc encLaneSet := by
  have hW := computableInPolyTime_W haxes hlevels
  have hW' : ComputableInPolyTime (fun q : α × ℕ => (p q.1).W) (encPair enc encUnary) encUnary :=
    hW.comp (ComputableInPolyTime.fst _ _)
  have hk' : ComputableInPolyTime (fun q : α × ℕ => k q.1) (encPair enc encUnary) encUnary :=
    hk.comp (ComputableInPolyTime.fst _ _)
  have hr : ComputableInPolyTime (fun a => Finset.range ((p a).W + 1)) enc encLaneSet := by fun_prop
  apply laneSet_filterDecide_polyTime (keep := fun a x => (1 ≤ x ∧ x ≤ k a) ∨ ((p a).W - k a ≤ x ∧ x < (p a).W)) hr
  fun_prop

omit hl in
private theorem lowerFinish_polyTime {columns : α → Finset ℕ} (hc : ComputableInPolyTime columns enc encLaneSet) :
    ComputableInPolyTime (fun a => lowerFinish (p a) (columns a)) enc encTemplate := by
  have hD := computableInPolyTime_D haxes hlevels
  unfold lowerFinish
  fun_prop

/-- All actual same-page marker checks emit their literal row reads and level-column requests. -/
private theorem pageChecks_polyTime (side : Side) :
    ComputableInPolyTime (fun a => pageChecks (layout a) (p a) side) enc encTemplates := by
  have hD := computableInPolyTime_D haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  have hY := computableInPolyTime_Y haxes hlevels 1
  have haux := acceptance_auxiliaries_polyTime hl haxes hlevels
  have hlive := live_polyTime hl haxes hlevels side
  have hcore := acceptance_cores_polyTime hl haxes hlevels
  have hfinish := lowerFinish_polyTime haxes hlevels
    (show ComputableInPolyTime (fun a => auxiliaries (layout a) (p a) \ live (layout a) (p a) side) enc encLaneSet by fun_prop)
  have hhalf := readRows_polyTime haxes hlevels .west
    (show ComputableInPolyTime (fun a => ({(p a).H - (p a).Y 1 / 2} : Finset ℕ)) enc encLaneSet by fun_prop)
  have htail : ComputableInPolyTime (fun a => (List.range (M - 1)).flatMap fun k =>
      [readRows (p a) .west {if side = .upper then ((p a).Y (k + 1) + (p a).Y (k + 1 + 1)) / 2
          else (p a).H - ((p a).Y (k + 1) + (p a).Y (k + 1 + 1)) / 2},
        if side = .lower then lowerFinish (p a) (levelColumns (layout a) (p a) side (k + 1))
        else .clear .north (levelColumns (layout a) (p a) side (k + 1))]) enc encTemplates := by
    apply ComputableInPolyTime.flatMapConst
    intro k _
    have hy := computableInPolyTime_Y haxes hlevels (k + 1)
    have hn := computableInPolyTime_Y haxes hlevels (k + 1 + 1)
    have hcols := levelColumns_polyTime hl haxes hlevels side (k + 1)
    have hlow := lowerFinish_polyTime haxes hlevels hcols
    have hrow := readRows_polyTime haxes hlevels .west
      (show ComputableInPolyTime (fun a => ({if side = .upper then ((p a).Y (k + 1) + (p a).Y (k + 1 + 1)) / 2
          else (p a).H - ((p a).Y (k + 1) + (p a).Y (k + 1 + 1)) / 2} : Finset ℕ)) enc encLaneSet by fun_prop)
    fun_prop
  unfold pageChecks
  simp only [hlevels]
  fun_prop

variable (hpages : ∀ a, (layout a).pages.Valid) (hhighest : ∀ a, (layout a).pages.highest ≤ (p a).levels)
include hpages hhighest

/-- The actual thirteen preparation blocks emit their complete literal prefix and clear requests. -/
private theorem preparation_polyTime {k : α → ℕ} (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a => preparation (layout a) (p a) (k a)) enc encTemplates := by
  have hW := computableInPolyTime_W haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  have hD := computableInPolyTime_D haxes hlevels
  have hY := computableInPolyTime_Y haxes hlevels 1
  have hs := sideBands_polyTime haxes hlevels hk
  have hu := trimRound_polyTime hl haxes hlevels .upper
  have hd := trimRound_polyTime hl haxes hlevels .lower
  have hkeep := keepRows_polyTime hl haxes hlevels
  have hneighbors := acceptance_neighboringRows_polyTime haxes hlevels
  have hmainU := mainRound_polyTime hl haxes hlevels hpages hhighest .upper
  have hmainD := mainRound_polyTime hl haxes hlevels hpages hhighest .lower
  have hprivate := privateColumns_polyTime hl haxes hlevels
  have hguards := acceptance_guards_polyTime hl haxes hlevels
  have hflanks := readRows_polyTime haxes hlevels .east
    (show ComputableInPolyTime (fun a => ({(p a).D - 2, (p a).D + 2} : Finset ℕ)) enc encLaneSet by fun_prop)
  have hguardRow := readRows_polyTime haxes hlevels .west
    (show ComputableInPolyTime (fun a => ({(p a).D - 4} : Finset ℕ)) enc encLaneSet by fun_prop)
  have hmainTop : ComputableInPolyTime (fun a => mainTop (layout a) (p a)) enc encTemplate := by
    simpa only [mainTop, mainRound, ite_true] using hmainU
  have hmainBottom : ComputableInPolyTime (fun a => mainBottom (layout a) (p a)) enc encTemplate := by
    simpa only [mainBottom, mainRound, reduceCtorEq, ite_false] using hmainD
  unfold preparation frameSchedule
  change ComputableInPolyTime (fun a => _ ++ [_, _, _, _, _, _, _,
    Template.read .south (prefixRequests (privateColumns (layout a) (p a)) fun _ => (p a).Y 1 + 3), _, _, _]) _ _
  fun_prop

-- The twenty-five fixed front blocks share the same layout and scale machine proofs.
set_option maxHeartbeats 400000 in
/-- The actual complete fixed-level compact template list emits directly from the real layout. -/
theorem schedule_polyTime {k : α → ℕ} (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a => schedule (layout a) (p a) (k a)) enc encTemplates := by
  have hW := computableInPolyTime_W haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  have hD := computableInPolyTime_D haxes hlevels
  have hY := computableInPolyTime_Y haxes hlevels 1
  have hpre := preparation_polyTime hl haxes hlevels hpages hhighest hk
  have haxes' := acceptance_axes_polyTime hl haxes hlevels
  have hcore := acceptance_cores_polyTime hl haxes hlevels
  have haux := acceptance_auxiliaries_polyTime hl haxes hlevels
  have hg := acceptance_guards_polyTime hl haxes hlevels
  have hs := acceptance_samples_polyTime hl haxes hlevels
  have hw := acceptance_workRows_polyTime hl haxes hlevels
  have hc := acceptance_cutRows_polyTime haxes hlevels
  have hp := acceptance_probeRows_polyTime hl haxes hlevels hpages hhighest
  have hprobe := readRows_polyTime haxes hlevels .west hp
  have hguard := readColumns_polyTime haxes hlevels .south hg
  have hsample := readRows_polyTime haxes hlevels .east
    (show ComputableInPolyTime (fun a => ({(p a).D + 4} : Finset ℕ)) enc encLaneSet by fun_prop)
  have hwork := readRows_polyTime haxes hlevels .west
    (show ComputableInPolyTime (fun a => workRows (layout a) (p a) \ ({0, (p a).H} ∪ probeRows (layout a) (p a))) enc encLaneSet by fun_prop)
  have hlow := pageChecks_polyTime hl haxes hlevels .lower
  have hupp := pageChecks_polyTime hl haxes hlevels .upper
  have haxisRead : ComputableInPolyTime (fun a => Template.read .north
      (prefixRequests (axes (layout a) (p a) \ cores (layout a) (p a)) (fun _ => (p a).H + 1) ++
        prefixRequests (cores (layout a) (p a)) (fun _ => (p a).H - (p a).Y 1))) enc encTemplate := by fun_prop
  have hcoreRead : ComputableInPolyTime (fun a => Template.read .north
      (prefixRequests (cores (layout a) (p a)) fun _ => (p a).H - (p a).Y 1 + 1)) enc encTemplate := by fun_prop
  unfold schedule
  dsimp only
  fun_prop

end PushPuzzle.Push.AcceptanceProgram
