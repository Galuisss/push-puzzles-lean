/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.TerminalInventory
public import PushPush.Doors.PhysicalSoundness
public import PushPush.Doors.ControlParked

/-! Physical source decoding on any protected corridor ending at the parking signal. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity
open PushFS (Cell Direction)

/-- An actual positive slide on a protected corridor with its normalized control shadow. -/
structure ProtectedSlide (storage : Bool) (I : Instance)
    (initial final : PushFS.State (layout storage I).width (layout storage I).height) where
  sourceConfig : State
  sourceReachable : SelfClosingDoor.Reachable I.doors I.initial sourceConfig
  control : Control storage I
  phase : ControlPhase storage I sourceConfig control
  regular : control.signal.Regular
  source : PushFS.State (layout storage I).width (layout storage I).height
  target : PushFS.State (layout storage I).width (layout storage I).height
  prefixPath : Reachable initial source
  suffixPath : Reachable target final
  corridor : ProtectedCorridor storage I initial final
  realizes : control.stock.Realizes storage source
  direction : Direction
  length : ℕ
  distance : ℕ
  length_pos : 0 < length
  distance_pos : 0 < distance
  valid : source.player ∉ source.boxes
  slide : Slide direction source length distance
  player : target.player = slide.cell ⟨1, by omega⟩
  boxes : target.boxes = slide.boxes

namespace ProtectedSlide

variable {storage : Bool} {I : Instance}
  {initial final : PushFS.State (layout storage I).width (layout storage I).height}

def first (M : ProtectedSlide storage I initial final) : Cell (layout storage I).width (layout storage I).height :=
  M.slide.cell ⟨1, by have := M.length_pos; omega⟩

private theorem move
    (M : ProtectedSlide storage I initial final) : Move M.direction M.source M.target :=
  .push M.valid M.length_pos M.distance_pos M.slide M.player M.boxes

theorem source_protected (M : ProtectedSlide storage I initial final) : Protected storage I M.source :=
  M.corridor M.source M.prefixPath ((Relation.ReflTransGen.single ⟨M.direction, M.move⟩).trans M.suffixPath)

theorem target_protected (M : ProtectedSlide storage I initial final) : Protected storage I M.target :=
  M.corridor M.target (M.prefixPath.tail ⟨M.direction, M.move⟩) M.suffixPath

theorem target_corridor (M : ProtectedSlide storage I initial final) :
    ProtectedCorridor storage I M.target final :=
  M.corridor.tail (M.prefixPath.tail ⟨M.direction, M.move⟩)

end ProtectedSlide

/-- A complete first-box readout independent of the final door-register values. -/
structure ProtectedPushDecoder (storage : Bool) (I : Instance)
    (initial final : PushFS.State (layout storage I).width (layout storage I).height) : Prop where
  pin : ∀ M : ProtectedSlide storage I initial final,
    (M.first.1.val, M.first.2.val) ∈ (layout storage I).pins →
      I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target
  signal : ∀ M : ProtectedSlide storage I initial final,
    (M.first.1.val, M.first.2.val) = M.control.stock.signal →
      I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target

namespace ProtectedPushDecoder

variable {storage : Bool} {I : Instance}
  {initial final : PushFS.State (layout storage I).width (layout storage I).height}

private theorem decode (decoder : ProtectedPushDecoder storage I initial final)
    (M : ProtectedSlide storage I initial final) :
    I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target := by
  rcases M.control.stock.first_actor M.source_protected M.target_protected M.realizes M.slide
      M.length_pos M.distance_pos M.valid M.boxes with hpin | hregister | hsignal
  · exact decoder.pin M hpin
  · obtain ⟨door, hdoor⟩ := hregister
    exact Or.inr (M.phase.register_push M.regular M.source_protected M.target_protected M.realizes
      door M.slide M.length_pos M.distance_pos M.valid M.boxes hdoor)
  · exact decoder.signal M hsignal

private theorem move (decoder : ProtectedPushDecoder storage I initial final)
    (hcorridor : ProtectedCorridor storage I initial final)
    {current : Control storage I} (hcontrol : Control.Reachable (Control.initial storage I) current)
    (hregular : current.signal.Regular)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hprefix : Reachable initial s) (hstock : current.stock.Realizes storage s)
    {d : Direction} (hm : Move d s t) (hsuffix : Reachable t final) :
    I ∈ SelfClosingDoor.Reachability ∨ current.PhysicalNext t := by
  cases hm with
  | walk hv ha he hb =>
    exact Or.inr ((Control.PhysicalNext.refl current hregular hstock).same_boxes hb)
  | @push n k hv hn hk r hp hb =>
    rcases hcontrol.sourceSafe with haccept | ⟨source, hreach, hphase⟩
    · exact Or.inl haccept
    · exact decoder.decode {
        sourceConfig := source, sourceReachable := hreach, control := current,
        phase := hphase, regular := hregular, source := s, target := t,
        prefixPath := hprefix, suffixPath := hsuffix, corridor := hcorridor,
        realizes := hstock, direction := d, length := n, distance := k,
        length_pos := hn, distance_pos := hk, valid := hv, slide := r,
        player := hp, boxes := hb }

theorem sound (decoder : ProtectedPushDecoder storage I initial final)
    (hcorridor : ProtectedCorridor storage I initial final)
    (hinitial : (Control.initial storage I).stock.Realizes storage initial)
    (hactual : Reachable initial final)
    (hpark : workCell storage I (targetRow I) (targetRow_fit storage I) ∈ final.boxes) :
    I ∈ SelfClosingDoor.Reachability := by
  have invariant {s : PushFS.State (layout storage I).width (layout storage I).height}
      (hprefix : Reachable initial s) (hsuffix : Reachable s final) :
      I ∈ SelfClosingDoor.Reachability ∨ (Control.initial storage I).PhysicalNext s := by
    induction hprefix with
    | refl => exact Or.inr (Control.PhysicalNext.refl _ trivial hinitial)
    | @tail s t hprefix hm ih =>
      rcases ih ((Relation.ReflTransGen.single hm).trans hsuffix) with haccept | hshadow
      · exact Or.inl haccept
      · obtain ⟨current, hcontrol, hregular, hstock⟩ := hshadow
        rcases hm with ⟨d, hm⟩
        rcases decoder.move hcorridor hcontrol hregular hprefix hstock hm hsuffix with haccept | hnext
        · exact Or.inl haccept
        · exact Or.inr (hnext.prefix hcontrol)
  rcases invariant hactual Relation.ReflTransGen.refl with haccept | hshadow
  · exact haccept
  · obtain ⟨current, hcontrol, hregular, hstock⟩ := hshadow
    exact hcontrol.source_of_parked hregular (hstock ▸ hpark)

end ProtectedPushDecoder
end PushPuzzle.PushPush.Doors.Source
