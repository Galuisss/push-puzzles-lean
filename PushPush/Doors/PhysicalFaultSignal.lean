/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalFaultActors
public import PushPush.Doors.JunctionColumn
public import PushPush.Doors.ForwardJunctionMove

/-! A launch-row signal remains vertically blocked after a reverse source-pin push. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem Protected.frame_neighbor_no_slide {storage : Bool} {I : Instance}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (q : Cell (layout storage I).width (layout storage I).height)
    (hf : q ∈ (layout storage I).raster ((layout storage I).rack ∪ (layout storage I).blockers))
    (hq : q ∈ s.boxes)
    (ha : Adjacent d (r.cell ⟨1, by omega⟩) q ∨ Adjacent d q (r.cell ⟨1, by omega⟩)) : False := by
  have hfirst : r.cell ⟨1, by omega⟩ ∈ r.before :=
    Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hqbefore := r.before_adjacent hk hv hfirst hq ha
  exact Finset.disjoint_left.mp (hs.slide_avoids_frame ht r hn hk hv hb) hf hqbefore

theorem WireFault.pair_signal_no_vertical {storage : Bool} {I : Instance} {S : Stock I}
    (F : WireFault storage I S)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    (door : Fin I.doors.length) (moving kept : Room.Slot)
    (hregister : S.register door = Register.ofSlot kept)
    (hsignal : S.signal = atRow storage I (doorBase door.val + Room.landing moving kept))
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hboxes : s.boxes = F.boxes) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ = F.signal) (hd : d = .north ∨ d = .south) : False := by
  have hcOld := S.pair_column (storage := storage) door moving kept hregister hsignal
    (s := S.canonical storage) rfl
  have hc : Room.PairColumn s (doorCell storage I door 0 (by omega)).1
      (doorBase door.val + (layout storage I).shift)
      (pairLower (doorBase door.val + (layout storage I).shift) moving kept) := by
    intro p hx hlo hhi
    rw [hboxes, F.working_membership hland p (congrArg Fin.val hx)]
    exact hcOld p hx hlo hhi
  have hraw : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
      atRow storage I (doorBase door.val + Room.landing moving kept) := by
    rw [hfirst]
    exact F.signal_raw.trans hsignal
  have hfirstx : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 :=
    Fin.ext (congrArg Prod.fst hraw)
  have hfirsty : (r.cell ⟨1, by omega⟩).2.val =
      doorBase door.val + (layout storage I).shift + Room.landing moving kept := by
    have hy := congrArg Prod.snd hraw
    change (r.cell ⟨1, by omega⟩).2.val =
      doorBase door.val + Room.landing moving kept + (layout storage I).shift at hy
    omega
  have hy := (pairLower_inventory (doorBase door.val + (layout storage I).shift)
    (r.cell ⟨1, by omega⟩).2.val moving kept).mp (Or.inr hfirsty)
  have hbound := pairLower_bounds (doorBase door.val + (layout storage I).shift) moving kept
  exact ht.pair_door_no_vertical door _ hbound.1 hbound.2 hc r hn hk hv hb hfirstx hy hd

theorem WireFault.endpoint_signal_no_vertical {storage : Bool} {I : Instance} {S : Stock I}
    (F : WireFault storage I S) (v j : ℕ) (hvloc : v < (labels I).length) (hj : j < slots I)
    (south : Bool) (hused : endpointUsed I v j south = true)
    (hsignal : S.signal = atRow storage I (roomBase I v j + endpointOffset I south))
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ = F.signal) (hd : d = .north ∨ d = .south) : False := by
  have hh := chamberHeight_ge I
  have hcap : roomBase I v j + endpointCap I south ∈ (layout storage I).caps := by
    cases south
    · exact (junction_upper_cap_iff storage I v j hvloc hj).mpr hused
    · have he : roomBase I v j + endpointCap I true = roomBase I v j + chamberHeight I - 2 := by
        simp only [endpointCap, ite_true]; omega
      rw [he]
      exact (junction_lower_cap_iff storage I v j hvloc hj).mpr hused
  let cap := workCell storage I (roomBase I v j + endpointCap I south) (caps_fit storage I hcap)
  have hcapraw : (cap.1.val, cap.2.val) ∈ (layout storage I).blockers := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨_, List.mem_append_right _ hcap, rfl⟩
  have hcapframe : cap ∈ (layout storage I).raster ((layout storage I).rack ∪ (layout storage I).blockers) :=
    ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_right _ hcapraw)
  have hcapbox : cap ∈ s.boxes := hs.caps _ hcap cap rfl rfl
  have hraw : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
      atRow storage I (roomBase I v j + endpointOffset I south) := by
    rw [hfirst]
    exact F.signal_raw.trans hsignal
  have hx := congrArg Prod.fst hraw
  have hy := congrArg Prod.snd hraw
  change (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 at hx
  change (r.cell ⟨1, by omega⟩).2.val =
    roomBase I v j + endpointOffset I south + (layout storage I).shift at hy
  apply hs.frame_neighbor_no_slide ht r hn hk hv hb cap hcapframe hcapbox
  rcases hd with rfl | rfl <;> cases south
  · apply Or.inl
    exact ⟨Fin.ext hx.symm, by dsimp [cap, workCell, Layout.point]; simp only [endpointOffset, endpointCap, Bool.false_eq_true, ite_false] at hy ⊢; omega⟩
  · apply Or.inr
    exact ⟨Fin.ext hx, by dsimp [cap, workCell, Layout.point]; simp only [endpointOffset, endpointCap, ite_true] at hy ⊢; omega⟩
  · apply Or.inr
    exact ⟨Fin.ext hx, by dsimp [cap, workCell, Layout.point]; simp only [endpointOffset, endpointCap, Bool.false_eq_true, ite_false] at hy ⊢; omega⟩
  · apply Or.inl
    exact ⟨Fin.ext hx.symm, by dsimp [cap, workCell, Layout.point]; simp only [endpointOffset, endpointCap, ite_true] at hy ⊢; omega⟩

theorem ControlPhase.fault_signal_no_vertical_odd {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C) (hregular : C.signal.Regular)
    (hlocation : source.location ∈ labels I) (F : WireFault storage I C.stock)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    (row : ℕ) (hodd : row % 2 = 1) (hsignal : C.stock.signal = atRow storage I row)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hboxes : s.boxes = F.boxes) (hs : Protected storage I s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ = F.signal) (hd : d = .north ∨ d = .south) : False := by
  cases hphase with
  | junction j p hj hp =>
    have hy := congrArg Prod.snd hsignal
    change inputRow I (rank I source.location) j p + (layout storage I).shift = row + (layout storage I).shift at hy
    have heven := inputRow_even I (rank I source.location) j p
    omega
  | upper j hj hused =>
    exact F.endpoint_signal_no_vertical _ j (rank_bound I hlocation) hj false hused rfl hs ht r hn hk hv hb hfirst hd
  | lower j hj hused =>
    apply F.endpoint_signal_no_vertical _ j (rank_bound I hlocation) hj true hused ?_ hs ht r hn hk hv hb hfirst hd
    have hh := chamberHeight_ge I
    apply Prod.ext
    · rfl
    · change lowerRow I (rank I source.location) j + (layout storage I).shift = _
      simp only [lowerRow, endpointOffset, ite_true, atRow]
      omega
  | junctionWire index corner j p hj hp htarget =>
    have hp := Layout.wirePath_private_x (layout storage I) index (layout storage I).wires[index]
      corner (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.1)
      (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.2)
    have hx := congrArg Prod.fst hsignal
    change (SignalPosition.wire index corner).point.1 = (layout storage I).rackX - 1 at hx
    change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hp
    omega
  | call door channel stored incoming hentry hsession =>
    have hy := congrArg Prod.snd hsignal
    change doorBase door.val + incoming.row + (layout storage I).shift = row + (layout storage I).shift at hy
    have heven := registerRow_even I door (Register.ofSlot incoming)
    rw [Register.row_ofSlot] at heven
    omega
  | result door channel stored incoming keep hentry hsession =>
    cases keep
    · exact F.pair_signal_no_vertical hland door incoming stored (by simp [Control.stock]) rfl hboxes ht r hn hk hv hb hfirst hd
    · exact F.pair_signal_no_vertical hland door stored incoming (by simp [Control.stock]) rfl hboxes ht r hn hk hv hb hfirst hd
  | doorWire door channel stored incoming index corner hentry hsession htarget =>
    have hp := Layout.wirePath_private_x (layout storage I) index (layout storage I).wires[index]
      corner (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.1)
      (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.2)
    have hx := congrArg Prod.fst hsignal
    change (SignalPosition.wire index corner).point.1 = (layout storage I).rackX - 1 at hx
    change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hp
    omega

end PushPuzzle.PushPush.Doors.Source
