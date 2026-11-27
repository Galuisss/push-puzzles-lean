/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutAdvance
public import PushPush.Doors.ControlWire

/-! Actual arrival ports have one adjacent vertical pin and one rack stopper. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

private theorem adjacent_position_bound {w h : ℕ} {a b : Cell w h} {e : Direction}
    (ha : Adjacent e a b) (d : Direction) : d.position b ≤ d.position a + 1 := by
  cases e <;> cases d <;> simp only [Adjacent, Direction.position] at * <;>
    rcases ha with ⟨hfirst, hsecond⟩ <;>
    try { have := congrArg Fin.val hfirst }
    <;> try { have := congrArg Fin.val hsecond }
    <;> omega

theorem wire_arrival_adjacent (storage : Bool) (I : Instance)
    (index : Fin (layout storage I).wires.length) :
    Adjacent (if (layout storage I).wires[index].targetSouth then .south else .north)
      (wirePosition storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 6)
      (wireStop storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 5) := by
  have ht := wire_target_ge storage I (List.getElem_mem index.isLt)
  cases he : (layout storage I).wires[index].targetSouth <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Adjacent] <;>
    refine ⟨rfl, ?_⟩
  · change (wireStopRaw (layout storage I) index.val (layout storage I).wires[index] 5).2 + 1 =
      (layout storage I).wires[index].target + (layout storage I).shift
    change Layout.beside (layout storage I).wires[index].targetSouth
      ((layout storage I).wires[index].target + (layout storage I).shift) + 1 = _
    rw [he]
    dsimp [Layout.beside]
    omega
  · change (wireStopRaw (layout storage I) index.val (layout storage I).wires[index] 5).2 =
      (layout storage I).wires[index].target + (layout storage I).shift + 1
    change Layout.beside (layout storage I).wires[index].targetSouth
      ((layout storage I).wires[index].target + (layout storage I).shift) = _
    rw [he]
    rfl

namespace Stock

variable {I : Instance}

/-- The arrival row contains precisely the travelling signal and its rack box. -/
theorem arrival_row (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hregister : atRow storage I (layout storage I).wires[index].target ∉
      S.registerPoints storage)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s)
    (q : Cell (layout storage I).width (layout storage I).height)
    (hrow : q.2.val = (layout storage I).wires[index].target + (layout storage I).shift)
    (hq : q ∈ s.boxes) :
    (q.1.val, q.2.val) = S.signal ∨ q.1.val = (layout storage I).rackX := by
  have he := List.getElem_mem index.isLt
  have hraw := ((layout storage I).mem_raster _ _).mp (hs ▸ hq)
  rcases Finset.mem_union.mp hraw with hraw | hraw
  · rcases Finset.mem_union.mp hraw with hraw | hraw
    · rcases Finset.mem_union.mp hraw with hraw | hraw
      · rcases Finset.mem_union.mp hraw with hpin | hrack
        · exact False.elim ((pins_not_target_row storage I he hpin) hrow)
        · exact Or.inr ((layout storage I).rack_column hrack)
      · obtain ⟨row, hrowmem, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hraw)
        have hy := congrArg Prod.snd heq
        have hroweq : row = (layout storage I).wires[index].target := by dsimp at hy; omega
        exact False.elim ((wires_target_free storage I he) (hroweq ▸ hrowmem))
    · have hx := S.registerPoints_column storage hraw
      have hpoint : (q.1.val, q.2.val) = atRow storage I
          (layout storage I).wires[index].target := Prod.ext hx hrow
      exact False.elim (hregister (hpoint ▸ hraw))
  · exact Or.inl (Finset.mem_singleton.mp hraw)

/-- No original pin can move while the signal is at the last private corner. -/
theorem arrival_pin_blocked (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] 6)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) {d : Direction} {n k : ℕ} (r : Slide d s n k)
    (hn : 0 < n) (hk : 0 < k) (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hpin : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) : False := by
  obtain ⟨_, signal, hsig, ha, _⟩ := S.pin_slide storage hs r hn hk hinterior _ hpin rfl
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let arrival := wirePosition storage I index.val index.isLt e he 6
  let previous := wireStop storage I index.val index.isLt e he 5
  have hsigcell : signal = arrival := by
    have hh := hsig.trans hsignal
    exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
  have hprevpin : (previous.1.val, previous.2.val) ∈ (layout storage I).pins := by
    apply wireStopRaw_pin_mem storage I _ 5 (by decide)
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hlane : d.lane (r.cell ⟨1, by omega⟩) = d.lane signal :=
    (r.lane _).trans ((ha.lane.trans (r.lane _)).symm)
  rw [hsigcell] at hlane
  have hfirst : r.cell ⟨1, by omega⟩ = previous := by
    apply pin_lane_unique storage I d _ previous hpin hprevpin
    rw [hlane]
    cases d
    · rfl
    · exact False.elim ((pins_not_target_row storage I he hpin) (by
        change (r.cell ⟨1, by omega⟩).2.val = e.target + (layout storage I).shift
        exact hlane))
    · rfl
    · exact False.elim ((pins_not_target_row storage I he hpin) (by
        change (r.cell ⟨1, by omega⟩).2.val = e.target + (layout storage I).shift
        exact hlane))
  have hnear := adjacent_position_bound (wire_arrival_adjacent storage I index).reverse d
  change d.position arrival ≤ d.position previous + 1 at hnear
  have hp := r.position ⟨1, by omega⟩
  have hl := r.position ⟨n + k, by omega⟩
  have hstop := ha.position
  rw [hsigcell] at hstop
  rw [hfirst] at hp
  change d.position previous = d.position s.player + (1 : ℕ) at hp
  change d.position (r.cell ⟨n + k, by omega⟩) =
    d.position s.player + (n + k : ℕ) at hl
  omega

/-- The final private signal has only its eastward single-box slide. -/
private theorem arrival_signal_slide (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] 6)
    (hregister : atRow storage I (layout storage I).wires[index].target ∉
      S.registerPoints storage)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) {d : Direction} {n k : ℕ} (r : Slide d s n k)
    (hn : 0 < n) (hk : 0 < k) (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal) :
    n = 1 ∧ d = .east ∧ Adjacent d (r.cell ⟨n + k, by omega⟩)
      (wireStop storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 6) := by
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let arrival := wirePosition storage I index.val index.isLt e he 6
  let previous := wireStop storage I index.val index.isLt e he 5
  let rack := wireStop storage I index.val index.isLt e he 6
  have hfirstcell : r.cell ⟨1, by omega⟩ = arrival := by
    have hh := hfirst.trans hsignal
    exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
  have hprevpin : (previous.1.val, previous.2.val) ∈ (layout storage I).pins := by
    apply wireStopRaw_pin_mem storage I _ 5 (by decide)
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  obtain ⟨stop, hstop, ha⟩ := r.exists_stopper hn hinterior
  have hstoplane : d.lane stop = d.lane arrival := by
    exact ha.lane.trans ((r.lane _).trans (by simpa only [hfirstcell] using (r.lane ⟨1, by omega⟩).symm))
  have hp := r.position ⟨1, by omega⟩
  rw [hfirstcell] at hp
  change d.position arrival = d.position s.player + (1 : ℕ) at hp
  have hl := r.position ⟨n + k, by omega⟩
  change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hl
  have hstoppos := ha.position
  have hd : d = .east ∨ d = .west := by
    by_contra hd
    have hv : d = .north ∨ d = .south := by cases d <;> simp_all
    have hline : d.lane stop = d.lane previous := by
      rcases hv with rfl | rfl <;> exact hstoplane
    rcases (S.pin_line_readout storage hs d previous stop hprevpin hline).mp hstop with hh | hh
    · subst stop
      have hnear := adjacent_position_bound (wire_arrival_adjacent storage I index) d
      change d.position previous ≤ d.position arrival + 1 at hnear
      omega
    · have hh : stop = arrival := by
        have hh := hh.trans hsignal
        exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
      subst stop
      omega
  have hrow : stop.2.val = e.target + (layout storage I).shift := by
    rcases hd with rfl | rfl <;> exact hstoplane
  have hstopx : stop.1.val = (layout storage I).rackX := by
    rcases S.arrival_row storage index hregister hs stop hrow hstop with hh | hh
    · have hh : stop = arrival := by
        have hh := hh.trans hsignal
        exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
      subst stop
      omega
    · exact hh
  have hstopcell : stop = rack := Prod.ext (Fin.ext hstopx) (Fin.ext hrow)
  have hgap : arrival.1.val + 2 ≤ (layout storage I).rackX := by
    change Layout.wireC index.val + 2 ≤ (layout storage I).rackX
    have hi := index.isLt
    dsimp [Layout.wireC, Layout.rackX]
    omega
  have hde : d = .east := by
    rcases hd with hd | rfl
    · exact hd
    · simp only [Direction.position] at hp hl hstoppos
      omega
  have hn1 : n = 1 := by
    apply Doors.slide_length_one r hn
    intro q haq hq
    have hy : q.2.val = e.target + (layout storage I).shift := by
      rw [hfirstcell, hde] at haq
      exact congrArg Fin.val haq.2
    rcases S.arrival_row storage index hregister hs q hy hq with hh | hh
    · have hqx := congrArg Prod.fst (hh.trans hsignal)
      have hqa := haq.position
      rw [hfirstcell, hde] at hqa
      change (q.1.val : ℤ) = (arrival.1.val : ℤ) + 1 at hqa
      change q.1.val = arrival.1.val at hqx
      omega
    · have hqa := haq.position
      rw [hfirstcell, hde] at hqa
      change (q.1.val : ℤ) = (arrival.1.val : ℤ) + 1 at hqa
      omega
  rw [hstopcell] at ha
  exact ⟨hn1, hde, ha⟩

end Stock

private theorem ControlPhase.wire_target_ready {storage : Bool} {I : Instance} {source : State}
    {register : Fin I.doors.length → Register}
    {index : Fin (layout storage I).wires.length} {corner : Fin 8}
    (hphase : ControlPhase storage I source ⟨register, .wire index corner⟩) :
    atRow storage I (layout storage I).wires[index].target ∉
      (⟨register, .wire index corner⟩ : Control storage I).stock.registerPoints storage := by
  cases hphase with
  | junctionWire index corner j p hj hp htarget =>
    rw [htarget]
    exact Stock.junction_input_ready storage _ _ _ _
  | doorWire door channel stored incoming index corner entry session target =>
    rw [target]
    rw [← Register.row_ofSlot incoming]
    apply Stock.door_input_ready storage _ door (Register.ofSlot incoming)
    rw [show (⟨sessionRegisters I source door stored, .wire index corner⟩ :
      Control storage I).stock.register door = Register.ofSlot stored from sessionRegisters_self I source door stored]
    exact fun he => Room.reachable_call_distinct _ channel stored incoming session (ofSlot_injective he)

/-- Any genuine arrival-port signal slide has the normalized working-row successor. -/
private theorem ControlPhase.arrival_push {storage : Bool} {I : Instance} {source : State}
    {register : Fin I.doors.length → Register}
    {index : Fin (layout storage I).wires.length}
    (hphase : ControlPhase storage I source ⟨register, .wire index 6⟩)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : (⟨register, .wire index 6⟩ : Control storage I).stock.Realizes storage s)
    (ht : Protected storage I t) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
      (⟨register, .wire index 6⟩ : Control storage I).stock.signal) :
    (⟨register, .wire index 6⟩ : Control storage I).PhysicalNext t := by
  obtain ⟨rfl, hd, hstop⟩ := (⟨register, .wire index 6⟩ : Control storage I).stock.arrival_signal_slide
    storage index rfl hphase.wire_target_ready hstock r hn hk
    (by rw [← hb]; exact ht.interior) hfirst
  apply Control.wire_push register index 6 (by decide) hstock r hb hd
  · exact Prod.ext (Fin.ext (congrArg Prod.fst hfirst)) (Fin.ext (congrArg Prod.snd hfirst))
  · exact hstop

/-- The complete pin-or-signal classification at the last private corner. -/
theorem ControlPhase.arrival_actor_push {storage : Bool} {I : Instance} {source : State}
    {register : Fin I.doors.length → Register}
    {index : Fin (layout storage I).wires.length}
    (hphase : ControlPhase storage I source ⟨register, .wire index 6⟩)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : (⟨register, .wire index 6⟩ : Control storage I).stock.Realizes storage s)
    (ht : Protected storage I t) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
        (layout storage I).pins ∨
      ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
        (⟨register, .wire index 6⟩ : Control storage I).stock.signal) :
    (⟨register, .wire index 6⟩ : Control storage I).PhysicalNext t := by
  rcases hfirst with hpin | hsignal
  · exact False.elim ((⟨register, .wire index 6⟩ : Control storage I).stock.arrival_pin_blocked
      storage index rfl hstock r hn hk (by rw [← hb]; exact ht.interior) hpin)
  · exact hphase.arrival_push hstock ht r hn hk hb hsignal

end PushPuzzle.PushPush.Doors.Source
