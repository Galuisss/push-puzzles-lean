/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutPrivate
public import PushPush.Doors.PhysicalCollision
public import PushPush.Doors.WireSourceForwardClear

/-! Every normal private wire slide has the exact normalized control successor. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem wire_private_position (L : Layout) (i : ℕ) (hi : i < L.wires.length)
    (e : Wire) (corner : Fin 8) (hlo : 0 < corner.val) (hhi : corner.val < 7) :
    (wirePositionRaw L i e corner).1 < L.rackX - 1 := by
  rcases corner with ⟨corner, hcorner⟩
  change 0 < corner at hlo
  change corner < 7 at hhi
  have hc : corner = 1 ∨ corner = 2 ∨ corner = 3 ∨ corner = 4 ∨ corner = 5 ∨ corner = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [wirePositionRaw, Layout.wirePath, List.getD_cons_zero,
      List.getD_cons_succ, Layout.wireA, Layout.wireB, Layout.wireC,
      Layout.rackX] <;> omega

theorem Stock.wire_private_empty {storage : Bool} {I : Instance} (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7) (hlo : 0 < corner.val) :
    let e := (layout storage I).wires[index]
    let he := List.getElem_mem index.isLt
    wirePosition storage I index.val index.isLt e he corner.castSucc ∉ S.stationary storage := by
  intro e he
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  let source := wirePosition storage I index.val index.isLt e he corner.castSucc
  let dest := wirePosition storage I index.val index.isLt e he corner.succ
  let stop := wireStop storage I index.val index.isLt e he corner
  have hg := wire_leg_geometry (layout storage I) index.val e index.isLt
    (wires_fit storage I he).1 (wires_fit storage I he).2 corner source dest stop rfl rfl rfl
  have hpins := wire_interval_pin_clear storage I hei corner source dest stop source
    rfl rfl rfl rfl hg.2.1.le
  have hx : source.1.val < (layout storage I).rackX - 1 :=
    wire_private_position _ _ index.isLt e corner.castSucc hlo corner.isLt
  exact fun hp => S.private_clear storage hx hpins (((layout storage I).mem_raster _ _).mp hp)

/-- The physical forward alternative, including the final private corner, preserves
all registers and normalizes wire endpoint seven back to its working row. -/
theorem Control.wire_push {storage : Bool} {I : Instance}
    (register : Fin I.doors.length → Register)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7) (hlo : 0 < corner.val)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : (⟨register, .wire index corner.castSucc⟩ : Control storage I).stock.Realizes storage s)
    {d : Direction} {k : ℕ} (r : Slide d s 1 k) (hb : t.boxes = r.boxes)
    (hd : d = wireDirection (layout storage I) index.val (layout storage I).wires[index] corner)
    (hfirst : r.cell ⟨1, by omega⟩ =
      wirePosition storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) corner.castSucc)
    (hstop : Adjacent d (r.cell ⟨1 + k, by omega⟩)
      (wireStop storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) corner)) :
    (⟨register, .wire index corner.castSucc⟩ : Control storage I).PhysicalNext t := by
  let current : Control storage I := ⟨register, .wire index corner.castSucc⟩
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let dest := wirePosition storage I index.val index.isLt e he corner.succ
  have hg := wire_leg_geometry (layout storage I) index.val e index.isLt
    (wires_fit storage I he).1 (wires_fit storage I he).2 corner
    (wirePosition storage I index.val index.isLt e he corner.castSucc) dest
    (wireStop storage I index.val index.isLt e he corner) rfl rfl rfl
  have hlast : r.cell ⟨k + 1, by omega⟩ = dest := by
    have ha := hstop.reverse
    have ha' := hg.2.2.reverse
    rw [← hd] at ha'
    simpa only [Nat.add_comm] using ha.functional ha'
  have hclear : r.cell ⟨1, by omega⟩ ∉ current.stock.stationary storage := by
    rw [hfirst]
    exact current.stock.wire_private_empty index corner hlo
  let step : Control storage I := ⟨register, .wire index corner.succ⟩
  have hstep : Control.Reachable current step := .single (.wire register index corner)
  by_cases hlastCorner : corner.val < 6
  · apply Control.signal_slide hstep (show step.signal.Regular from ⟨by dsimp [step]; omega,
      by dsimp [step]; omega⟩) rfl hstock r hb
    · rw [hfirst]
      rfl
    · exact hclear
    · rw [hlast]
      rfl
  · have hcorner : corner = 6 := Fin.ext (by omega)
    subst corner
    let next : Control storage I := ⟨register, .working e.target⟩
    have hreach : Control.Reachable current next :=
      hstep.tail (.leaveWire register index)
    apply Control.signal_slide hreach trivial rfl hstock r hb
    · rw [hfirst]
      rfl
    · exact hclear
    · rw [hlast]
      rfl

/-- At each genuine internal corner, moving the signal itself always advances
the safe control machine. The reverse alternative moves an original pin. -/
theorem Control.wire_internal_signal {storage : Bool} {I : Instance}
    (register : Fin I.doors.length → Register)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : (⟨register, .wire index corner⟩ : Control storage I).stock.Realizes storage s)
    (ht : Protected storage I t) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
      (SignalPosition.wire (storage := storage) index corner).point) :
    (⟨register, .wire index corner⟩ : Control storage I).PhysicalNext t := by
  let S := (⟨register, .wire index corner⟩ : Control storage I).stock
  let e := (layout storage I).wires[index]
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hclassification := S.wire_internal_slide storage hei corner hlo hhi rfl hstock r hn hk
    (by rw [← hb]; exact ht.interior) (Or.inr hfirst)
  have hn1 := hclassification.1
  clear hclassification
  subst n
  let here : Fin 7 := ⟨corner.val, by omega⟩
  have hcorner : here.castSucc = corner := Fin.ext rfl
  have hclassification := S.wire_internal_slide storage hei corner hlo hhi rfl hstock r hn hk
    (by rw [← hb]; exact ht.interior) (Or.inr hfirst)
  have hsignal : r.cell ⟨1, by omega⟩ =
      wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) corner :=
    Prod.ext (Fin.ext (congrArg Prod.fst hfirst)) (Fin.ext (congrArg Prod.snd hfirst))
  rcases hclassification.2 with ⟨hd, hf, ha⟩ | ⟨_, hf, ha⟩
  · have hs : (⟨register, .wire index here.castSucc⟩ : Control storage I).stock.Realizes storage s := by
      rw [hcorner]
      exact hstock
    have hr := Control.wire_push register index here hlo hs r hb hd
      (by simpa only [hcorner] using hf) ha
    simpa only [hcorner] using hr
  · have hc := wire_private_corner_geometry storage I hei corner hlo hhi
    have hp := hc.2.2.2
    rw [← hf, hsignal] at hp
    omega

end PushPuzzle.PushPush.Doors.Source
