/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.TerminalInventory
public import PushPush.Doors.WireReadoutFault

/-! Private-column budgets reject frozen faults without identifying individual terminal pins. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell)

def columnCount {w h : ℕ} (boxes : Finset (Cell w h)) (x : ℕ) : ℕ :=
  (boxes.filter fun p => p.1.val = x).card

/-- The reader preserves the original number of boxes in each private column. -/
structure PrivateColumnInventory (storage : Bool) (I : Instance)
    (boxes : Finset (Cell (layout storage I).width (layout storage I).height)) : Prop where
  count : ∀ x < (layout storage I).rackX - 1,
    columnCount boxes x = columnCount ((layout storage I).raster (layout storage I).pins) x

/-- Either two boxes occupy one private column, or a box occupies an originally empty column. -/
def ColumnExcess (storage : Bool) (I : Instance)
    (boxes : Finset (Cell (layout storage I).width (layout storage I).height)) : Prop :=
  (∃ p ∈ boxes, ∃ q ∈ boxes,
    p.1.val < (layout storage I).rackX - 1 ∧ p.1 = q.1 ∧ p ≠ q) ∨
  ∃ p ∈ boxes, p.1.val < (layout storage I).rackX - 1 ∧
    ∀ pin ∈ (layout storage I).pins, pin.1 ≠ p.1.val

private theorem pin_column_card_le_one (storage : Bool) (I : Instance) (x : ℕ) :
    columnCount ((layout storage I).raster (layout storage I).pins) x ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hpx⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqx⟩ := Finset.mem_filter.mp hq
  have hp := ((layout storage I).mem_raster _ _).mp hp
  have hq := ((layout storage I).mem_raster _ _).mp hq
  have he := (layout storage I).pins_same_column hp hq (hpx.trans hqx.symm)
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

private theorem PrivateColumnInventory.column_unique {storage : Bool} {I : Instance}
    {boxes : Finset (Cell (layout storage I).width (layout storage I).height)}
    (H : PrivateColumnInventory storage I boxes)
    {p q : Cell (layout storage I).width (layout storage I).height}
    (hp : p ∈ boxes) (hq : q ∈ boxes) (hx : p.1.val < (layout storage I).rackX - 1)
    (hcol : p.1 = q.1) : p = q := by
  have hc : columnCount boxes p.1.val ≤ 1 := by
    rw [H.count p.1.val hx]
    exact pin_column_card_le_one storage I p.1.val
  apply Finset.card_le_one.mp hc p (Finset.mem_filter.mpr ⟨hp, rfl⟩)
    q (Finset.mem_filter.mpr ⟨hq, congrArg Fin.val hcol.symm⟩)

private theorem PrivateColumnInventory.free_column_empty {storage : Bool} {I : Instance}
    {boxes : Finset (Cell (layout storage I).width (layout storage I).height)}
    (H : PrivateColumnInventory storage I boxes)
    {p : Cell (layout storage I).width (layout storage I).height}
    (hx : p.1.val < (layout storage I).rackX - 1)
    (hfree : ∀ pin ∈ (layout storage I).pins, pin.1 ≠ p.1.val) : p ∉ boxes := by
  intro hp
  have hc : 0 < columnCount boxes p.1.val := Finset.card_pos.mpr
    ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  rw [H.count p.1.val hx] at hc
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hc
  obtain ⟨hq, hcol⟩ := Finset.mem_filter.mp hq
  exact hfree _ (((layout storage I).mem_raster _ _).mp hq) hcol

private theorem PrivateColumnInventory.no_excess {storage : Bool} {I : Instance}
    {boxes : Finset (Cell (layout storage I).width (layout storage I).height)}
    (H : PrivateColumnInventory storage I boxes) : ¬ ColumnExcess storage I boxes := by
  rintro (⟨p, hp, q, hq, hx, hcol, hne⟩ | ⟨p, hp, hx, hfree⟩)
  · exact hne (H.column_unique hp hq hx hcol)
  · exact H.free_column_empty hx hfree hp

theorem deadStock_reject_columns {storage : Bool} {I : Instance}
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (hsuffix : Reachable s final) (hprotected : ProtectedCorridor storage I s final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    (hd : Wire.DeadStock s.boxes (Protected storage I))
    (hexcess : ColumnExcess storage I s.boxes) : False := by
  have hb := hd.reachable_boxes rfl hsuffix hprotected
  exact hterminal.no_excess (hb.symm ▸ hexcess)

/-- A temporary fault can perform arbitrarily many walks; its first push must
leave a dead stock with an excessive private-column count. -/
theorem reject_after_next_dead_columns {storage : Bool} {I : Instance}
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (hsuffix : Reachable s final) (hprotected : ProtectedCorridor storage I s final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    (hexcess : ColumnExcess storage I s.boxes)
    (hnext : ∀ (d : PushFS.Direction)
      (u : PushFS.State (layout storage I).width (layout storage I).height) (n k : ℕ)
      (r : Slide d u n k) (hn : 0 < n) (hk : 0 < k), u.boxes = s.boxes → u.player ∉ u.boxes →
      Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ →
      Wire.DeadStock r.boxes (Protected storage I) ∧ ColumnExcess storage I r.boxes) : False := by
  have hi : ∀ u, Reachable s u → Reachable u final → u.boxes = s.boxes := by
    intro u hu
    induction hu with
    | refl => exact fun _ => rfl
    | @tail u v hu hstep ih =>
      intro hv
      have hub := ih ((Relation.ReflTransGen.single hstep).trans hv)
      obtain ⟨d, hm⟩ := hstep
      cases hm with
      | walk _ _ _ hb => exact hb.trans hub
      | push hvalid hn hk r hplayer hboxes =>
        have hvpath := hu.tail ⟨d, Move.push hvalid hn hk r hplayer hboxes⟩
        have hprot := hprotected v hvpath hv
        have hprot' : Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ :=
          hprot.of_boxes_eq hboxes.symm
        obtain ⟨hd, he⟩ := hnext d u _ _ r hn hk hub hvalid hprot'
        exact False.elim (deadStock_reject_columns hv (hprotected.tail hvpath) hterminal
          (by rw [hboxes]; exact hd) (by rw [hboxes]; exact he))
  exact hterminal.no_excess ((hi final hsuffix .refl).symm ▸ hexcess)

end PushPuzzle.PushPush.Doors.Source
