/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalSoundness
public import PushPush.Doors.PhysicalWorkingReadout
public import PushPush.Doors.WireReadoutAdvance
public import PushPush.Doors.WireReadoutInternal

/-! The actual signal and all working-column pin branches of a successful slide. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.SuccessfulSlide

open Cslib.Complexity

variable {I : Instance}

private theorem working_pin_reject (M : SuccessfulSlide I) (row : ℕ)
    (hworking : M.control.signal = .working row)
    (hpin : (M.first.1.val, M.first.2.val) ∈ (layout true I).pins) : False := by
  have hlocation := reachable_location_mem I M.sourceReachable
  have hposition : M.control.stock.signal = atRow true I row := by
    change M.control.signal.point = atRow true I row
    rw [hworking]
    rfl
  exact M.phase.working_pin_reject M.regular hlocation row
    (M.phase.working_row_fit hlocation row hworking) hposition M.realizes M.target_protected
    M.prefixPath M.suffixPath M.goals M.slide M.length_pos M.distance_pos
    ⟨M.direction, M.move⟩ M.boxes hpin

theorem signal_readout (M : SuccessfulSlide I)
    (hfirst : (M.first.1.val, M.first.2.val) = M.control.stock.signal) :
    I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target := by
  cases hsignal : M.control.signal with
  | working row =>
    exact M.phase.working_signal_push M.sourceReachable row hsignal
      M.source_protected M.target_protected M.realizes M.prefixPath M.suffixPath M.goals
      M.slide M.length_pos M.distance_pos M.valid ⟨M.direction, M.move⟩ M.boxes hfirst
  | wire index corner =>
    have hcontrol : M.control = ⟨M.control.register, .wire index corner⟩ := by
      exact congrArg (Control.mk M.control.register) hsignal
    have hregular : 0 < corner.val ∧ corner.val < 7 := by
      have h := M.regular
      simpa only [hsignal, SignalPosition.Regular] using h
    have hstock : (⟨M.control.register, .wire index corner⟩ : Control true I).stock.Realizes true M.source := by
      rw [← hcontrol]
      exact M.realizes
    have hfirstwire : (M.first.1.val, M.first.2.val) =
        (SignalPosition.wire (storage := true) index corner).point := by
      calc
        _ = M.control.stock.signal := hfirst
        _ = _ := by rw [hcontrol]; rfl
    apply Or.inr
    by_cases hlast : corner.val < 6
    · have hnext := Control.wire_internal_signal M.control.register index corner
        hregular.1 hlast hstock M.target_protected M.slide M.length_pos M.distance_pos M.boxes hfirstwire
      simpa only [← hcontrol] using hnext
    · have hcorner : corner = 6 := Fin.ext (by omega)
      subst corner
      have hphase : ControlPhase true I M.sourceConfig ⟨M.control.register, .wire index 6⟩ := by
        rw [← hcontrol]
        exact M.phase
      have hnext := hphase.arrival_actor_push hstock M.target_protected M.slide
        M.length_pos M.distance_pos M.boxes (Or.inr hfirstwire)
      simpa only [← hcontrol] using hnext

theorem pin_readout (M : SuccessfulSlide I)
    (hpin : (M.first.1.val, M.first.2.val) ∈ (layout true I).pins) :
    I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target := by
  cases hsignal : M.control.signal with
  | working row => exact False.elim (M.working_pin_reject row hsignal hpin)
  | wire index corner =>
    have hcontrol : M.control = ⟨M.control.register, .wire index corner⟩ :=
      congrArg (Control.mk M.control.register) hsignal
    have hregular : 0 < corner.val ∧ corner.val < 7 := by
      have h := M.regular
      simpa only [hsignal, SignalPosition.Regular] using h
    by_cases hlast : corner.val < 6
    · have hposition : M.control.stock.signal = wirePositionRaw (layout true I) index.val
          (layout true I).wires[index] corner := by
        rw [hcontrol]
        rfl
      exact False.elim (M.control.stock.internal_pin_reject true index corner
        hregular.1 hlast hposition M.phase.register_ne_erase M.realizes M.target_protected
        M.prefixPath M.suffixPath M.goals M.slide M.length_pos M.distance_pos
        ⟨M.direction, M.move⟩ M.boxes hpin)
    · have hcorner : corner = 6 := Fin.ext (by omega)
      subst corner
      have hphase : ControlPhase true I M.sourceConfig ⟨M.control.register, .wire index 6⟩ := by
        rw [← hcontrol]
        exact M.phase
      have hstock : (⟨M.control.register, .wire index 6⟩ : Control true I).stock.Realizes true M.source := by
        rw [← hcontrol]
        exact M.realizes
      have hnext := hphase.arrival_actor_push hstock M.target_protected M.slide
        M.length_pos M.distance_pos M.boxes (Or.inl hpin)
      exact Or.inr (by simpa only [← hcontrol] using hnext)

end PushPuzzle.PushPush.Doors.Source.SuccessfulSlide
