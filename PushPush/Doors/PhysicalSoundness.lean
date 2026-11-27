/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalJunction

/-! Composition of the physical pin and signal readouts with the complete source control invariant. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity
open PushFS (Cell Direction)

/-- One actual positive slide on a complete successful storage trajectory, carrying
the exact source configuration and normalized physical control shadow. -/
structure SuccessfulSlide (I : Instance) where
  /-- The same original source configuration carried by this control phase. -/
  sourceConfig : State
  /-- The original source path already executed. -/
  sourceReachable : SelfClosingDoor.Reachable I.doors I.initial sourceConfig
  /-- The complete physical control phase. -/
  control : Control true I
  /-- The source configuration agrees with this physical phase. -/
  phase : ControlPhase true I sourceConfig control
  /-- Wire endpoints have been normalized to working rows. -/
  regular : control.signal.Regular
  /-- The actual player and box positions before the slide. -/
  source : PushFS.State (layout true I).width (layout true I).height
  /-- The actual state after the slide. -/
  target : PushFS.State (layout true I).width (layout true I).height
  /-- The exact-storage terminal state of this same trajectory. -/
  final : PushFS.State (layout true I).width (layout true I).height
  /-- The original actual prefix. -/
  prefixPath : Reachable (puzzle true I).initial source
  /-- The original actual suffix. -/
  suffixPath : Reachable target final
  /-- This trajectory ends at the real compiler's complete box target. -/
  goals : final.boxes = (puzzle true I).board.goals
  /-- Complete stock equality before the slide. -/
  realizes : control.stock.Realizes true source
  /-- The physical direction. -/
  direction : Direction
  /-- The entire initial moving box run. -/
  length : ℕ
  /-- Its maximum positive sliding distance. -/
  distance : ℕ
  /-- Positive initial run length. -/
  length_pos : 0 < length
  /-- Positive sliding distance. -/
  distance_pos : 0 < distance
  /-- The source player is on an empty cell. -/
  valid : source.player ∉ source.boxes
  /-- The actual maximum-slide ray. -/
  slide : Slide direction source length distance
  /-- The real player advances exactly one cell. -/
  player : target.player = slide.cell ⟨1, by omega⟩
  /-- The real whole-run box update. -/
  boxes : target.boxes = slide.boxes

namespace SuccessfulSlide

variable {I : Instance}

def first (M : SuccessfulSlide I) : Cell (layout true I).width (layout true I).height :=
  M.slide.cell ⟨1, by have := M.length_pos; omega⟩

theorem move (M : SuccessfulSlide I) : Move M.direction M.source M.target :=
  .push M.valid M.length_pos M.distance_pos M.slide M.player M.boxes

theorem source_protected (M : SuccessfulSlide I) : Protected true I M.source :=
  protected_prefix true I M.prefixPath ((Relation.ReflTransGen.single ⟨M.direction, M.move⟩).trans M.suffixPath) M.goals

theorem target_protected (M : SuccessfulSlide I) : Protected true I M.target :=
  protected_prefix true I (M.prefixPath.tail ⟨M.direction, M.move⟩) M.suffixPath M.goals

end SuccessfulSlide

/-- The two geometric cases left after protected-frame and original-register classification. -/
structure SuccessfulPushDecoder (I : Instance) : Prop where
  /-- A first original pin either certifies prior acceptance or has a safe physical successor. -/
  pin : ∀ M : SuccessfulSlide I,
    (M.first.1.val, M.first.2.val) ∈ (layout true I).pins →
      I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target
  /-- The same readout for a first active signal. -/
  signal : ∀ M : SuccessfulSlide I,
    (M.first.1.val, M.first.2.val) = M.control.stock.signal →
      I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target

namespace SuccessfulPushDecoder

variable {I : Instance}

private theorem decode (decoder : SuccessfulPushDecoder I) (M : SuccessfulSlide I) :
    I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target := by
  rcases M.control.stock.first_actor M.source_protected M.target_protected M.realizes M.slide
      M.length_pos M.distance_pos M.valid M.boxes with hpin | hregister | hsignal
  · exact decoder.pin M hpin
  · obtain ⟨door, hdoor⟩ := hregister
    exact Or.inr (M.phase.register_push M.regular M.source_protected M.target_protected M.realizes
      door M.slide M.length_pos M.distance_pos M.valid M.boxes hdoor)
  · exact decoder.signal M hsignal

private theorem move (decoder : SuccessfulPushDecoder I)
    {current : Control true I} (hcontrol : Control.Reachable (Control.initial true I) current)
    (hregular : current.signal.Regular)
    {s t final : PushFS.State (layout true I).width (layout true I).height}
    (hprefix : Reachable (puzzle true I).initial s) (hstock : current.stock.Realizes true s)
    {d : Direction} (hm : Move d s t) (hsuffix : Reachable t final)
    (hgoals : final.boxes = (puzzle true I).board.goals) :
    I ∈ SelfClosingDoor.Reachability ∨ current.PhysicalNext t := by
  cases hm with
  | walk hv ha he hb =>
    exact Or.inr ((Control.PhysicalNext.refl current hregular hstock).same_boxes hb)
  | @push n k hv hn hk r hp hb =>
    rcases hcontrol.sourceSafe with haccept | ⟨source, hreach, hphase⟩
    · exact Or.inl haccept
    · exact decoder.decode {
        sourceConfig := source
        sourceReachable := hreach
        control := current
        phase := hphase
        regular := hregular
        source := s
        target := t
        final := final
        prefixPath := hprefix
        suffixPath := hsuffix
        goals := hgoals
        realizes := hstock
        direction := d
        length := n
        distance := k
        length_pos := hn
        distance_pos := hk
        valid := hv
        slide := r
        player := hp
        boxes := hb }

/-- Actual successful storage paths decode to the same original self-closing-door instance. -/
theorem sound (decoder : SuccessfulPushDecoder I)
    {final : PushFS.State (layout true I).width (layout true I).height}
    (hactual : Reachable (puzzle true I).initial final)
    (hgoals : final.boxes = (puzzle true I).board.goals) : I ∈ SelfClosingDoor.Reachability := by
  have invariant {s : PushFS.State (layout true I).width (layout true I).height}
      (hprefix : Reachable (puzzle true I).initial s) (hsuffix : Reachable s final) :
      I ∈ SelfClosingDoor.Reachability ∨ (Control.initial true I).PhysicalNext s := by
    induction hprefix with
    | refl => exact Or.inr (Control.initial_physical true I)
    | @tail s t hprefix hm ih =>
      rcases ih ((Relation.ReflTransGen.single hm).trans hsuffix) with haccept | hshadow
      · exact Or.inl haccept
      · obtain ⟨current, hcontrol, hregular, hstock⟩ := hshadow
        rcases hm with ⟨d, hm⟩
        rcases decoder.move hcontrol hregular hprefix hstock hm hsuffix hgoals with haccept | hnext
        · exact Or.inl haccept
        · exact Or.inr (hnext.prefix hcontrol)
  rcases invariant hactual Relation.ReflTransGen.refl with haccept | hshadow
  · exact haccept
  · obtain ⟨current, hcontrol, _, hstock⟩ := hshadow
    exact hcontrol.source_of_goals (hstock.symm.trans hgoals)

end SuccessfulPushDecoder
end PushPuzzle.PushPush.Doors.Source
