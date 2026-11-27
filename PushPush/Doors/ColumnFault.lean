/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PrivateColumnInventory
public import PushPush.Doors.WireReadoutExtendedEngine

/-! Every vertical pin fault and every same-sign attraction exceeds a private-column budget. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem Stock.reverse_vertical_excess {storage : Bool} {I : Instance} (S : Stock I)
    {d : Direction} (signal extra removed near : Cell (layout storage I).width (layout storage I).height)
    (hraw : (signal.1.val, signal.2.val) = S.signal)
    (hc : Wire.Corner d signal extra removed) (ha : Adjacent d signal near)
    (hprivate : signal.1.val < (layout storage I).rackX - 1)
    (hd : d = .north ∨ d = .south) :
    ColumnExcess storage I (insert near ((S.boxes storage).erase removed)) := by
  have hsignal : signal ∈ S.boxes storage :=
    ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_right _ (Finset.mem_singleton.mpr hraw))
  have hsigne : signal ≠ removed := by intro he; have hp := hc.2.2.2; rw [he] at hp; omega
  apply Or.inl
  refine ⟨signal, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsigne, hsignal⟩),
    near, Finset.mem_insert_self _ _, hprivate, ?_, ha.ne⟩
  rcases hd with rfl | rfl <;> exact ha.1.symm

namespace ExtendedFault

variable {storage : Bool} {I : Instance} {S : Stock I}

private theorem excess (E : ExtendedFault storage I S) : ColumnExcess storage I E.fault.boxes := by
  apply Or.inl
  refine ⟨E.signal, E.subset_boxes (by simp [cluster]), E.near,
    E.subset_boxes (by simp [cluster]), E.signal_private, E.signal_near_column, E.nearAdj.ne⟩

private theorem after_slide_excess (E : ExtendedFault storage I S)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner, E.fault.boxes⟩)
    {u : PushFS.State (layout storage I).width (layout storage I).height}
    {d : Direction} {n k : ℕ} (r : Slide d u n k) (hn : 0 < n) (hk : 0 < k)
    (hb : u.boxes = E.fault.boxes) (hv : u.player ∉ u.boxes)
    (ht : Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩) :
    Wire.DeadStock r.boxes (Protected storage I) ∧ ColumnExcess storage I r.boxes := by
  refine ⟨(E.after_slide_dead hregister hprotected r hn hk hb hv ht).1, ?_⟩
  have hfirst := E.fault.slide_first_in_cluster E.signal_private
    (by intro p hp; have he : p = E.near := Finset.mem_singleton.mp hp
        rw [he]; have hm := E.near_margin; omega)
    hregister hprotected E.cluster E.lineClosed (by simp [fault, WireFault.single, cluster])
    (by intro p hp; have he := Finset.mem_singleton.mp hp; simp [he, cluster]) d u n k r hn hk hb hv ht
  have hclosed : Wire.LineClosed E.cluster u.boxes := by rw [hb]; exact E.lineClosed
  have hread := Wire.extended_corner_slide r hn hk ht.interior E.near E.signal E.extra E.remote
    E.extendedCorner E.extraAdj hclosed hfirst
  have hn1 := hread.1
  clear hread
  subst n
  have hread := Wire.extended_corner_slide r hn hk ht.interior E.near E.signal E.extra E.remote
    E.extendedCorner E.extraAdj hclosed hfirst
  let landed := r.cell ⟨1 + k, by omega⟩
  have ha : Adjacent E.forward E.near landed ∨ Adjacent E.forward landed E.remote := by
    rcases hread.2 with ⟨hd, _, ha⟩ | ⟨hd, _, ha⟩
    · exact Or.inr (by simpa only [hd] using ha)
    · apply Or.inl
      have h := ha.reverse
      simpa only [hd, Direction.opposite_opposite] using h
  apply Or.inr
  refine ⟨landed, r.last_mem_boxes hn, (E.landing_info landed ha).1, ?_⟩
  exact ha.elim (E.free_near landed) (E.free_remote landed)

theorem reject_columns (E : ExtendedFault storage I S)
    (hregister : ∀ door, S.register door ≠ .erase)
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (hboxes : s.boxes = insert E.near ((S.boxes storage).erase E.removed))
    (hsuffix : Reachable s final) (hcorridor : ProtectedCorridor storage I s final)
    (hterminal : PrivateColumnInventory storage I final.boxes) : False := by
  have hb : s.boxes = E.fault.boxes := by simpa only [fault, WireFault.single_boxes] using hboxes
  have hprotected : Protected storage I ⟨(layout storage I).corner, E.fault.boxes⟩ :=
    (hcorridor s .refl hsuffix).of_boxes_eq hb.symm
  apply reject_after_next_dead_columns hsuffix hcorridor hterminal (hb ▸ E.excess)
  intro d u n k r hn hk hbox hu ht
  exact E.after_slide_excess hregister hprotected r hn hk (hbox.trans hb) hu ht

end ExtendedFault
end PushPuzzle.PushPush.Doors.Source
