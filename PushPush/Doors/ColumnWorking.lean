/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnFault
public import PushPush.Doors.PhysicalWorkingReadout

/-! Working-column pin and wrong-side signal faults violate private-column budgets. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem ControlPhase.working_pin_reject_columns {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hregular : C.signal.Regular) (hlocation : source.location ∈ labels I)
    (row : ℕ) (hbound : row ≤ (layout storage I).depth)
    (hposition : C.stock.signal = atRow storage I row)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : C.stock.Realizes storage s) (ht : Protected storage I t)
    (hsuffix : Reachable t final) (hcorridor : ProtectedCorridor storage I t final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hpin : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) : False := by
  obtain ⟨rfl, signal, hsignal, ha, hboxes⟩ := C.stock.pin_slide storage hstock r hn hk
    (by rw [← hb]; exact ht.interior) _ hpin rfl
  let pin := r.cell ⟨1, by omega⟩
  let landed := r.cell ⟨1 + k, by omega⟩
  change (pin.1.val, pin.2.val) ∈ (layout storage I).pins at hpin
  have hworking : signal.1.val = (layout storage I).rackX - 1 :=
    congrArg Prod.fst (hsignal.trans hposition)
  have hsignalrow : signal.2.val = row + (layout storage I).shift :=
    congrArg Prod.snd (hsignal.trans hposition)
  have hlane : d.lane signal = d.lane pin := ha.lane.trans ((r.lane _).trans (r.lane _).symm)
  have hwest := (layout storage I).pins_west hpin
  change 7 ≤ pin.1.val ∧ pin.1.val + 2 < (layout storage I).rackX at hwest
  have hd : d = .east ∨ d = .west := by
    by_contra hd
    have hv : d = .north ∨ d = .south := by cases d <;> simp_all
    rcases hv with rfl | rfl <;> simp only [Direction.lane] at hlane <;> omega
  have hrow : signal.2 = pin.2 := by rcases hd with rfl | rfl <;> exact Fin.ext hlane
  have hde : d = .east := by
    rcases hd with hd | rfl
    · exact hd
    · have hp := r.position ⟨1, by omega⟩
      have hl := r.position ⟨1 + k, by omega⟩
      have hs := ha.position
      change -((pin.1.val : ℕ) : ℤ) = -(s.player.1.val : ℤ) + 1 at hp
      change -((landed.1.val : ℕ) : ℤ) = -(s.player.1.val : ℤ) + (1 + k : ℕ) at hl
      change -((signal.1.val : ℕ) : ℤ) = -(landed.1.val : ℤ) + 1 at hs
      omega
  have haland : Adjacent .west signal landed := by
    simpa only [hde, Direction.opposite] using ha.reverse
  have hpinrow : pin.2.val = row + (layout storage I).shift := by
    have hy := congrArg Fin.val hrow
    omega
  have hodd : row % 2 = 1 := by
    rcases pins_row_cases storage I hpin with hout | ⟨e, he, hh | hh⟩
    · omega
    · have ho := (wires_launch storage I he).odd
      change pin.2.val = _ at hh
      have hr : row = e.source := by omega
      exact hr ▸ ho
    · have ho := (wires_terminalPin storage I he).odd
      change (pinRow e) % 2 = 1 at ho
      change pin.2.val = _ at hh
      have hr : row = pinRow e := by omega
      exact hr ▸ ho
  have htarget : t.boxes = insert landed ((C.stock.boxes storage).erase pin) := by
    rw [hb, hboxes, hstock]
  have hdead := hphase.working_pin_deadStock hregular hlocation row hodd hposition
    signal pin landed hpin hsignal hrow haland (ht.of_boxes_eq htarget.symm)
  apply deadStock_reject_columns hsuffix hcorridor hterminal
    (by rw [htarget]; exact hdead)
  have hfree := WireFault.working_neighbor_free hworking haland
  apply Or.inr
  refine ⟨landed, ?_, hfree.1, hfree.2⟩
  rw [htarget]
  exact Finset.mem_insert_self _ _

namespace Stock

variable {I : Instance}

theorem terminal_row_signal_reject_columns (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hrow : S.signal.2 = (wireStopRaw (layout storage I) index.val
      (layout storage I).wires[index] 5).2)
    (hworking : S.signal.1 = (layout storage I).rackX - 1)
    (hregister : ∀ door, S.register door ≠ .erase)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    (hsuffix : Reachable t final) (hcorridor : ProtectedCorridor storage I t final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal)
    (hd : d = .east ∨ d = .west) : False := by
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let pin := wireStop storage I index.val index.isLt e he 5
  let signal := r.cell ⟨1, by omega⟩
  have hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins := by
    apply wireStopRaw_pin_mem storage I _ 5 (by decide)
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hsigx : signal.1.val = (layout storage I).rackX - 1 :=
    (congrArg Prod.fst hfirst).trans hworking
  have hsigrow : signal.2 = pin.2 := Fin.ext ((congrArg Prod.snd hfirst).trans hrow)
  have hgap : pin.1.val + 3 ≤ signal.1.val := by
    have hi := index.isLt
    change Layout.wireC index.val + 3 ≤ _
    rw [hsigx]
    dsimp [Layout.wireC, Layout.rackX]
    omega
  obtain ⟨rfl, hdw, hstop⟩ := S.row_signal_slide storage signal pin hfirst hpin hsigrow hgap
    hstock r hn hk (by rw [← hb]; exact ht.interior) rfl hd
  let landed := r.cell ⟨1 + k, by omega⟩
  have ha : Adjacent .east pin landed := by
    have ha := hstop.reverse
    simpa only [hdw, Direction.opposite] using ha
  have hlandx : landed.1.val = Layout.wireC index.val + 1 := ha.1
  have hprivate : landed.1.val < (layout storage I).rackX - 1 := by
    have hi := index.isLt
    dsimp [Layout.wireC, Layout.rackX] at hlandx ⊢
    omega
  have hfree : ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val := by
    intro p hp
    rw [hlandx]
    exact ((layout storage I).pins_not_free_column index.val hp).2.2
  have hclear : signal ∉ S.stationary storage := by
    intro hp
    have heq := S.stationary_at_pin_row storage hpin hsigrow hp
    have hx := congrArg (fun p => p.1.val) heq
    omega
  let next : Stock I := {S with signal := (landed.1.val, landed.2.val)}
  have hboxes : t.boxes = next.boxes storage := by
    have hu := S.boxes_setSignal storage signal landed hfirst.symm hclear
    rw [hb, single_slide_boxes r, hstock]
    simpa only [next, signal, landed, Nat.add_comm] using hu.symm
  have hd := next.private_pair_deadStock storage landed pin rfl hpin ha hprivate hfree hregister
    (ht.of_boxes_eq hboxes.symm)
  apply deadStock_reject_columns hsuffix hcorridor hterminal
    (by rw [hboxes]; exact hd)
  apply Or.inr
  refine ⟨landed, ?_, hprivate, hfree⟩
  rw [hboxes]
  exact ((layout storage I).mem_raster _ _).mpr
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))

end Stock
end PushPuzzle.PushPush.Doors.Source
