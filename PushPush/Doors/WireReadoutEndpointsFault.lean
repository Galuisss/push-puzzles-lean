/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutWrongSide
public import PushPush.Doors.PhysicalFaultSignal

/-! Reverse working-port pin faults close the horizontal line and its new private column. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

namespace WireFault

variable {storage : Bool} {I : Instance} {S : Stock I}

theorem working_neighbor_free {signal landed : Cell (layout storage I).width (layout storage I).height}
    (hsignal : signal.1.val = (layout storage I).rackX - 1)
    (ha : Adjacent .west signal landed) :
    landed.1.val < (layout storage I).rackX - 1 ∧
      ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val := by
  refine ⟨by have hh := ha.1; omega, ?_⟩
  intro p hp
  have hw := (layout storage I).pins_west hp
  have hh := ha.1
  omega

/-- After a pin reaches the working signal's west neighbour, every remaining original pin is blocked. -/
private theorem working_pin_blocked
    (signal pin landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hworking : signal.1.val = (layout storage I).rackX - 1)
    (hrow : signal.2 = pin.2) (ha : Adjacent .west signal landed) :
    (single signal pin landed hpin hsignal).BlocksFirst
      fun p => (p.1.val, p.2.val) ∈ (layout storage I).pins := by
  let F := single signal pin landed hpin hsignal
  have hfree := working_neighbor_free hworking ha
  have hne : pin ≠ landed := fun he => hfree.2 _ hpin (congrArg (fun p => p.1.val) he)
  have hmissing : pin ∉ F.boxes := single_missing signal pin landed hpin hsignal hne
  intro d s n k r hn hk hb hv ht hfirstpin
  have hfirstbox : r.cell ⟨1, by omega⟩ ∈ F.boxes := hb ▸ r.occupied ⟨0, hn⟩
  obtain ⟨stop, hstop, hstopadj⟩ := r.exists_stopper hn ht.interior
  have hstopbox : stop ∈ F.boxes := hb ▸ hstop
  have hlane : d.lane stop = d.lane (r.cell ⟨1, by omega⟩) :=
    hstopadj.lane.trans ((r.lane _).trans (r.lane _).symm)
  have hbad : stop = signal ∨ stop = landed → False := by
    intro hcases
    have hfirstwest := (layout storage I).pins_west hfirstpin
    have haX := ha.1
    dsimp at hfirstwest
    have hh : d = .east ∨ d = .west := by
      by_contra hh
      have hv : d = .north ∨ d = .south := by cases d <;> simp_all
      rcases hcases with rfl | rfl <;> rcases hv with rfl | rfl <;>
        simp only [Direction.lane] at hlane <;> omega
    have hy : (r.cell ⟨1, by omega⟩).2 = pin.2 := by
      apply Fin.ext
      rcases hcases with rfl | rfl <;> rcases hh with rfl | rfl <;>
        simp only [Direction.lane] at hlane <;>
        have hy := congrArg Fin.val hrow <;> have hay := congrArg Fin.val ha.2 <;> omega
    have heq : r.cell ⟨1, by omega⟩ = pin := by
      have he := pins_same_row storage I hfirstpin hpin (congrArg Fin.val hy)
      exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
    exact hmissing (heq ▸ hfirstbox)
  rw [single_boxes] at hstopbox
  rcases Finset.mem_insert.mp hstopbox with hstopland | hbase
  · exact hbad (Or.inr hstopland)
  · let base : PushFS.State (layout storage I).width (layout storage I).height :=
      ⟨s.player, S.boxes storage⟩
    rcases (S.pin_line_readout storage (s := base) rfl d _ stop hfirstpin hlane).mp
        (Finset.mem_erase.mp hbase).2 with heq | heq
    · have hp := r.position ⟨1, by omega⟩
      have hl := r.position ⟨n + k, by omega⟩
      have hs := hstopadj.position
      change d.position (r.cell ⟨1, by omega⟩) = d.position s.player + (1 : ℕ) at hp
      change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hl
      have hforward : d.position (r.cell ⟨1, by omega⟩) < d.position stop := by omega
      exact (ne_of_lt hforward) (congrArg d.position heq).symm
    · have heq : stop = signal := by
        have heq := heq.trans hsignal.symm
        exact Prod.ext (Fin.ext (congrArg Prod.fst heq)) (Fin.ext (congrArg Prod.snd heq))
      exact hbad (Or.inl heq)

/-- The new private column contains only the landed pin, so it cannot move vertically. -/
private theorem working_added_no_vertical
    (signal pin landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hworking : signal.1.val = (layout storage I).rackX - 1)
    (ha : Adjacent .west signal landed)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hb : s.boxes = (single signal pin landed hpin hsignal).boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hfirst : r.cell ⟨1, by omega⟩ = landed) (hd : d = .north ∨ d = .south) : False := by
  have hfree := working_neighbor_free hworking ha
  obtain ⟨stop, hstop, hstopadj⟩ := r.exists_stopper hn hinterior
  have hstopbox := hb ▸ hstop
  have hlane : d.lane stop = d.lane landed :=
    hstopadj.lane.trans ((r.lane _).trans (by simpa only [hfirst] using (r.lane ⟨1, by omega⟩).symm))
  have hx : stop.1.val = landed.1.val := by rcases hd with rfl | rfl <;> exact hlane
  rw [single_boxes] at hstopbox
  rcases Finset.mem_insert.mp hstopbox with heq | hbase
  · have hp := r.position ⟨1, by omega⟩
    have hl := r.position ⟨n + k, by omega⟩
    have hs := hstopadj.position
    rw [hfirst] at hp
    rw [heq] at hs
    change d.position landed = d.position s.player + (1 : ℕ) at hp
    change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hl
    omega
  · have hraw := ((layout storage I).mem_raster _ _).mp (Finset.mem_erase.mp hbase).2
    exact S.raw_column_empty storage landed.1.val hfree.1 hfree.2
      (by have hh := congrArg Prod.fst hsignal; have hh' := ha.1; dsimp at hh; omega) hx hraw

/-- In either horizontal direction the new adjacent pair fills its entire occupied line. -/
private theorem working_pair_no_horizontal
    (signal pin landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hworking : signal.1.val = (layout storage I).rackX - 1)
    (hrow : signal.2 = pin.2) (ha : Adjacent .west signal landed)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hb : s.boxes = (single signal pin landed hpin hsignal).boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hfirst : r.cell ⟨1, by omega⟩ = signal ∨ r.cell ⟨1, by omega⟩ = landed)
    (hd : d = .east ∨ d = .west) : False := by
  let F := single signal pin landed hpin hsignal
  let cluster : Finset (Cell (layout storage I).width (layout storage I).height) := {signal, landed}
  have hfree := working_neighbor_free hworking ha
  have hpinne : pin ≠ landed := fun he => hfree.2 _ hpin (congrArg (fun p => p.1.val) he)
  have hsigpin : signal ≠ pin := by
    have hw := (layout storage I).pins_west hpin
    intro he
    have hx := congrArg (fun p => p.1.val) he
    dsimp at hw
    omega
  have hsub : cluster ⊆ s.boxes := by
    rw [hb, single_boxes]
    intro p hp
    simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_erase.mpr ⟨hsigpin, ((layout storage I).mem_raster _ _).mpr
        (Finset.mem_union_right _ (Finset.mem_singleton.mpr hsignal))⟩
    · exact Finset.mem_insert_self _ _
  have hclosed : ∀ p ∈ cluster, ∀ q ∈ s.boxes, d.lane q = d.lane p → q ∈ cluster := by
    intro p hp q hq hl
    have hpline : d.lane p = d.lane pin := by
      simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> rcases hd with rfl | rfl <;>
        simp only [Direction.lane] <;>
        have hh := congrArg Fin.val hrow <;> have hh' := congrArg Fin.val ha.2 <;> omega
    rw [hb, single_boxes] at hq
    rcases Finset.mem_insert.mp hq with heq | hbase
    · simp [cluster, heq]
    · let base : PushFS.State (layout storage I).width (layout storage I).height :=
        ⟨s.player, S.boxes storage⟩
      rcases (S.pin_line_readout storage (s := base) rfl d pin q hpin
        (hl.trans hpline)).mp (Finset.mem_erase.mp hbase).2 with heq | heq
      · exact False.elim ((Finset.mem_erase.mp hbase).1 heq)
      · have heq : q = signal := by
          have heq := heq.trans hsignal.symm
          exact Prod.ext (Fin.ext (congrArg Prod.fst heq)) (Fin.ext (congrArg Prod.snd heq))
        simp [cluster, heq]
  have hdis := Wire.slide_avoids_closed_line r hn hk hinterior cluster hsub
    (Wire.pair_lineConvex ha) hclosed
  apply Finset.disjoint_left.mp hdis
  · simpa only [cluster, Finset.mem_insert, Finset.mem_singleton] using hfirst
  · exact Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩

end WireFault

/-- A consumed original pin beside any odd working output leaves no successful positive move. -/
theorem ControlPhase.working_pin_deadStock {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hregular : C.signal.Regular) (hlocation : source.location ∈ labels I)
    (row : ℕ) (hodd : row % 2 = 1) (hposition : C.stock.signal = atRow storage I row)
    (signal pin landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = C.stock.signal)
    (hrow : signal.2 = pin.2) (ha : Adjacent .west signal landed)
    (hprotected : Protected storage I ⟨(layout storage I).corner,
      insert landed ((C.stock.boxes storage).erase pin)⟩) :
    Wire.DeadStock (insert landed ((C.stock.boxes storage).erase pin)) (Protected storage I) := by
  let F := WireFault.single signal pin landed hpin hsignal
  have hworking : signal.1.val = (layout storage I).rackX - 1 :=
    congrArg Prod.fst (hsignal.trans hposition)
  have hfree := WireFault.working_neighbor_free hworking ha
  have hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1 := by
    intro p hp
    have hp : p = landed := Finset.mem_singleton.mp hp
    exact hp ▸ hfree.1
  have hprot : Protected storage I ⟨(layout storage I).corner, F.boxes⟩ := by
    simpa only [F, WireFault.single_boxes] using hprotected
  have hreg : F.BlocksFirst fun p => ∃ door : Fin I.doors.length, p = C.stock.doorPoint storage door := by
    intro d s n k r hn hk hb hv ht hfirst
    obtain ⟨door, hfirst⟩ := hfirst
    exact F.register_no_slide_working_odd hphase hregular hland row hodd hposition hb
      (hprot.of_boxes_eq hb) ht door r hn hk hv rfl hfirst
  have hactive : F.BlocksFirst fun p => p = F.signal ∨ p ∈ F.added := by
    intro d s n k r hn hk hb hv ht hfirst
    have hfirst' : r.cell ⟨1, by omega⟩ = signal ∨ r.cell ⟨1, by omega⟩ = landed := by
      simpa only [F, WireFault.single, Finset.mem_singleton] using hfirst
    by_cases hd : d = .east ∨ d = .west
    · exact WireFault.working_pair_no_horizontal signal pin landed hpin hsignal hworking hrow ha
        hb r hn hk ht.interior hfirst' hd
    · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
      rcases hfirst' with hsig | hadded
      · exact hphase.fault_signal_no_vertical_odd hregular hlocation F hland row hodd hposition hb
          (hprot.of_boxes_eq hb) ht r hn hk hv rfl hsig hdv
      · exact WireFault.working_added_no_vertical signal pin landed hpin hsignal hworking ha
          hb r hn hk ht.interior hadded hdv
  have hdead := F.deadStock_of_actors hprot
    (WireFault.working_pin_blocked signal pin landed hpin hsignal hworking hrow ha) hreg hactive
  simpa only [F, WireFault.single_boxes] using hdead

/-- Every original-pin push with a working-column signal creates a fatal reverse-pin stock. -/
theorem ControlPhase.working_pin_reject {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hregular : C.signal.Regular) (hlocation : source.location ∈ labels I)
    (row : ℕ) (hbound : row ≤ (layout storage I).depth)
    (hposition : C.stock.signal = atRow storage I row)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : C.stock.Realizes storage s) (ht : Protected storage I t)
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable t final)
    (hgoal : final.boxes = (puzzle storage I).board.goals)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hmove : Step s t) (hb : t.boxes = r.boxes)
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
  apply deadStock_reject storage I (hprefix.trans (.single hmove)) hsuffix hgoal
    (by rw [htarget]; exact hdead) pin hpin
  rw [htarget]
  have hfree := WireFault.working_neighbor_free hworking haland
  have hne : pin ≠ landed := fun he => hfree.2 _ hpin (congrArg (fun p => p.1.val) he)
  simp [hne]

end PushPuzzle.PushPush.Doors.Source
