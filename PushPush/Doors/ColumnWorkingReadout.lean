/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnWorking

/-! Working signal readout from private-column budgets and the final parking request. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity
open PushFS (Cell Direction)

theorem ControlPhase.working_signal_horizontal_columns {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (row : ℕ) (hworking : C.signal = .working row)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (hsuffix : Reachable t final) (hcorridor : ProtectedCorridor storage I t final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = C.stock.signal)
    (hd : d = .east ∨ d = .west) :
    I ∈ SelfClosingDoor.Reachability ∨ C.PhysicalNext t := by
  rcases hphase.working_row_address hreach row hworking with haccept | haddress
  · exact Or.inl haccept
  rcases C with ⟨register, signal⟩
  cases hworking
  have hx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 := congrArg Prod.fst hfirst
  have hy : (r.cell ⟨1, by omega⟩).2.val = row + (layout storage I).shift := congrArg Prod.snd hfirst
  rcases haddress with hrack | ⟨index, hsource⟩ | ⟨index, hterminalRow⟩
  · exact False.elim (hs.full_rack_no_horizontal ht r hn hk hv hb (hs.input_rack_box hrack _ hx hy) hd)
  · subst row
    exact Or.inr (Control.launch_push register index hstock ht r hn hk hb hfirst hd)
  · apply False.elim
    apply Stock.terminal_row_signal_reject_columns storage _ index ?_ rfl hphase.register_ne_erase hstock ht hsuffix hcorridor hterminal r hn hk hb hfirst hd
    have htarget : 10 ≤ (layout storage I).wires[index].target :=
      wire_target_ge storage I (List.getElem_mem index.isLt)
    change row + (layout storage I).shift =
      (((layout storage I).wirePins index.val (layout storage I).wires[index]).getD 5 (0, 0)).2
    simp only [Layout.wirePins, List.getD_cons_succ, List.getD_cons_zero]
    rw [← hterminalRow]
    exact (beside_add _ _ _ (by omega)).symm

theorem ControlPhase.working_signal_push_columns {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (row : ℕ) (hworking : C.signal = .working row)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (hsuffix : Reachable t final) (hcorridor : ProtectedCorridor storage I t final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = C.stock.signal) :
    I ∈ SelfClosingDoor.Reachability ∨ C.PhysicalNext t := by
  by_cases hd : d = .east ∨ d = .west
  · exact hphase.working_signal_horizontal_columns hreach row hworking hs ht hstock hsuffix hcorridor hterminal r hn hk hv hb hfirst hd
  · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
    exact Or.inr (hphase.working_signal_vertical (reachable_location_mem I hreach) row hworking hs ht hstock r hn hk hv hb hfirst hdv)

end PushPuzzle.PushPush.Doors.Source
