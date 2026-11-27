/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalRun
public import PushPush.Doors.ColumnWorkingReadout
public import PushPush.Doors.ColumnInternal

/-! Complete physical decoding under the reader's terminal private-column budgets. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.ProtectedSlide

open Cslib.Complexity

variable {storage : Bool} {I : Instance}
  {initial final : PushFS.State (layout storage I).width (layout storage I).height}

private theorem working_pin_reject_columns (M : ProtectedSlide storage I initial final) (row : ℕ)
    (hworking : M.control.signal = .working row)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    (hpin : (M.first.1.val, M.first.2.val) ∈ (layout storage I).pins) : False := by
  have hlocation := reachable_location_mem I M.sourceReachable
  have hposition : M.control.stock.signal = atRow storage I row := by
    change M.control.signal.point = atRow storage I row
    rw [hworking]
    rfl
  exact M.phase.working_pin_reject_columns M.regular hlocation row
    (M.phase.working_row_fit hlocation row hworking) hposition M.realizes M.target_protected
    M.suffixPath M.target_corridor hterminal M.slide M.length_pos M.distance_pos M.boxes hpin

theorem signal_readout_columns (M : ProtectedSlide storage I initial final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    (hfirst : (M.first.1.val, M.first.2.val) = M.control.stock.signal) :
    I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target := by
  cases hsignal : M.control.signal with
  | working row =>
    exact M.phase.working_signal_push_columns M.sourceReachable row hsignal
      M.source_protected M.target_protected M.realizes M.suffixPath M.target_corridor hterminal
      M.slide M.length_pos M.distance_pos M.valid M.boxes hfirst
  | wire index corner =>
    have hcontrol : M.control = ⟨M.control.register, .wire index corner⟩ := by
      exact congrArg (Control.mk M.control.register) hsignal
    have hregular : 0 < corner.val ∧ corner.val < 7 := by
      have h := M.regular
      simpa only [hsignal, SignalPosition.Regular] using h
    have hstock : (⟨M.control.register, .wire index corner⟩ : Control storage I).stock.Realizes storage M.source := by
      rw [← hcontrol]
      exact M.realizes
    have hfirstwire : (M.first.1.val, M.first.2.val) =
        (SignalPosition.wire (storage := storage) index corner).point := by
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
      have hphase : ControlPhase storage I M.sourceConfig ⟨M.control.register, .wire index 6⟩ := by
        rw [← hcontrol]
        exact M.phase
      have hnext := hphase.arrival_actor_push hstock M.target_protected M.slide
        M.length_pos M.distance_pos M.boxes (Or.inr hfirstwire)
      simpa only [← hcontrol] using hnext

theorem pin_readout_columns (M : ProtectedSlide storage I initial final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    (hpin : (M.first.1.val, M.first.2.val) ∈ (layout storage I).pins) :
    I ∈ SelfClosingDoor.Reachability ∨ M.control.PhysicalNext M.target := by
  cases hsignal : M.control.signal with
  | working row => exact False.elim (M.working_pin_reject_columns row hsignal hterminal hpin)
  | wire index corner =>
    have hcontrol : M.control = ⟨M.control.register, .wire index corner⟩ :=
      congrArg (Control.mk M.control.register) hsignal
    have hregular : 0 < corner.val ∧ corner.val < 7 := by
      have h := M.regular
      simpa only [hsignal, SignalPosition.Regular] using h
    by_cases hlast : corner.val < 6
    · have hposition : M.control.stock.signal = wirePositionRaw (layout storage I) index.val
          (layout storage I).wires[index] corner := by
        rw [hcontrol]
        rfl
      exact False.elim (M.control.stock.internal_pin_reject_columns storage index corner
        hregular.1 hlast hposition M.phase.register_ne_erase M.realizes M.target_protected
        M.suffixPath M.target_corridor hterminal M.slide M.length_pos M.distance_pos M.boxes hpin)
    · have hcorner : corner = 6 := Fin.ext (by omega)
      subst corner
      have hphase : ControlPhase storage I M.sourceConfig ⟨M.control.register, .wire index 6⟩ := by
        rw [← hcontrol]
        exact M.phase
      have hstock : (⟨M.control.register, .wire index 6⟩ : Control storage I).stock.Realizes storage M.source := by
        rw [← hcontrol]
        exact M.realizes
      have hnext := hphase.arrival_actor_push hstock M.target_protected M.slide
        M.length_pos M.distance_pos M.boxes (Or.inl hpin)
      exact Or.inr (by simpa only [← hcontrol] using hnext)

end PushPuzzle.PushPush.Doors.Source.ProtectedSlide
