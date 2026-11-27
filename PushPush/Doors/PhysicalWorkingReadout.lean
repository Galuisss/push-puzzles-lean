/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalWorkingRows
public import PushPush.Doors.PhysicalFaultSignal
public import PushPush.Doors.PhysicalCollision
public import PushPush.Doors.PhysicalJunction
public import PushPush.Doors.WireReadoutEndpointsFault
public import PushPush.Doors.WireReadoutWrongSide

/-! Complete physical readout while the travelling signal is on the working column. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity
open PushFS (Cell Direction)

theorem ControlPhase.working_signal_vertical {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hlocation : source.location ∈ labels I) (row : ℕ) (hworking : C.signal = .working row)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = C.stock.signal)
    (hd : d = .north ∨ d = .south) : C.PhysicalNext t := by
  let F : WireFault storage I C.stock := ⟨∅, ∅, r.cell ⟨1, by omega⟩, by simp, hfirst⟩
  have hboxes : s.boxes = F.boxes := by simpa only [Stock.Realizes, F, WireFault.boxes, Finset.sdiff_empty, Finset.union_empty] using hstock
  have hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1 := by simp [F]
  cases hphase with
  | junction j p hj hp =>
    exact Control.junction_push _ _ j p (rank_bound I hlocation) hj hp hs ht hstock r hn hk hv hb hfirst
  | upper j hj hused =>
    exact False.elim (F.endpoint_signal_no_vertical _ j (rank_bound I hlocation) hj false hused rfl hs ht r hn hk hv hb rfl hd)
  | lower j hj hused =>
    have hsignal : (⟨sourceRegisters I source, .working (lowerRow I (rank I source.location) j)⟩ : Control storage I).stock.signal =
        atRow storage I (roomBase I (rank I source.location) j + endpointOffset I true) := by
      have hh := chamberHeight_ge I
      apply Prod.ext
      · rfl
      · change lowerRow I (rank I source.location) j + (layout storage I).shift = _
        simp only [lowerRow, endpointOffset, ite_true, atRow]
        omega
    exact False.elim (F.endpoint_signal_no_vertical _ j (rank_bound I hlocation) hj true hused hsignal hs ht r hn hk hv hb rfl hd)
  | call door channel stored incoming hentry hsession =>
    exact ControlPhase.signal_call_push door channel stored incoming hsession hs ht hstock r hn hk hv hb hfirst
  | result door channel stored incoming keep hentry hsession =>
    apply False.elim
    cases keep
    · exact F.pair_signal_no_vertical hland door incoming stored (by simp [Control.stock]) rfl hboxes ht r hn hk hv hb rfl hd
    · exact F.pair_signal_no_vertical hland door stored incoming (by simp [Control.stock]) rfl hboxes ht r hn hk hv hb rfl hd
  | junctionWire index corner j p hj hp htarget => cases hworking
  | doorWire door channel stored incoming index corner hentry hsession htarget => cases hworking

private theorem ControlPhase.working_signal_horizontal {storage : Bool} {I : Instance}
    {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (row : ℕ) (hworking : C.signal = .working row)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable t final)
    (hgoal : final.boxes = (puzzle storage I).board.goals)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hmove : Step s t) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = C.stock.signal)
    (hd : d = .east ∨ d = .west) :
    I ∈ SelfClosingDoor.Reachability ∨ C.PhysicalNext t := by
  rcases hphase.working_row_address hreach row hworking with haccept | haddress
  · exact Or.inl haccept
  rcases C with ⟨register, signal⟩
  cases hworking
  have hx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 := congrArg Prod.fst hfirst
  have hy : (r.cell ⟨1, by omega⟩).2.val = row + (layout storage I).shift := congrArg Prod.snd hfirst
  rcases haddress with hrack | ⟨index, hsource⟩ | ⟨index, hterminal⟩
  · exact False.elim (hs.full_rack_no_horizontal ht r hn hk hv hb (hs.input_rack_box hrack _ hx hy) hd)
  · subst row
    exact Or.inr (Control.launch_push register index hstock ht r hn hk hb hfirst hd)
  · apply False.elim
    apply Stock.terminal_row_signal_reject storage _ index ?_ rfl hphase.register_ne_erase hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst hd
    have htarget : 10 ≤ (layout storage I).wires[index].target :=
      wire_target_ge storage I (List.getElem_mem index.isLt)
    change row + (layout storage I).shift =
      (((layout storage I).wirePins index.val (layout storage I).wires[index]).getD 5 (0, 0)).2
    simp only [Layout.wirePins, List.getD_cons_succ, List.getD_cons_zero]
    rw [← hterminal]
    exact (beside_add _ _ _ (by omega)).symm

theorem ControlPhase.working_signal_push {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (row : ℕ) (hworking : C.signal = .working row)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable t final)
    (hgoal : final.boxes = (puzzle storage I).board.goals)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hmove : Step s t) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = C.stock.signal) :
    I ∈ SelfClosingDoor.Reachability ∨ C.PhysicalNext t := by
  by_cases hd : d = .east ∨ d = .west
  · exact hphase.working_signal_horizontal hreach row hworking hs ht hstock hprefix hsuffix hgoal r hn hk hv hmove hb hfirst hd
  · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
    exact Or.inr (hphase.working_signal_vertical (reachable_location_mem I hreach) row hworking hs ht hstock r hn hk hv hb hfirst hdv)

end PushPuzzle.PushPush.Doors.Source
