/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicErase
public import Push.CyclicInventory
public import Push.Scan
import all Push.CyclicInventory

/-! The entire actual wide room pays erase backups, all old auxiliary cleanup, and future positive quotas. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private def fullRoomCell (r : ColumnScan.Input)
    (q : Fin (r.width + 2 + r.extraWidth) × Fin ((wideReader r).outputHeight - r.height)) :
    Cell (wideReader r).outputWidth (wideReader r).outputHeight :=
  (⟨r.width + 1 + q.1.val, by
    have := q.1.isLt
    change r.width + 1 + q.1.val < r.width + 2 + (r.width + 1 + r.extraWidth)
    omega⟩,
    ⟨r.height + q.2.val, by
      have := q.2.isLt
      have hh : r.height ≤ (wideReader r).outputHeight := by
        change r.height ≤ r.height + (wideReader r).length; omega
      omega⟩)

private def fullRoomEmbed (r : ColumnScan.Input)
    (q : Fin (r.width + 2 + r.extraWidth) × Fin ((wideReader r).outputHeight - r.height)) :
    Cell (nextSource r).width (nextSource r).height :=
  (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells ((dock r).embed (fullRoomCell r q))

private theorem fullRoomEmbed_injective (r : ColumnScan.Input) : Function.Injective (fullRoomEmbed r) := by
  intro a b he
  have h := (dock r).embed_injective ((turnGeometry _ _).cells.injective he)
  have hx := congrArg (fun q => q.1.val) h
  have hy := congrArg (fun q => q.2.val) h
  apply Prod.ext <;> apply Fin.ext
  · change r.width + 1 + a.1.val = r.width + 1 + b.1.val at hx; omega
  · change r.height + a.2.val = r.height + b.2.val at hy; omega

private theorem fullRoom_mem_initial (r : ColumnScan.Input)
    (q : Fin (r.width + 2 + r.extraWidth) × Fin ((wideReader r).outputHeight - r.height)) :
    fullRoomEmbed r q ∈ holes (nextSource r).initial := by
  apply (turn_mem_holes (dock r).compile _).mpr
  apply (dock_mem_holes r _).mpr
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · change r.width < r.width + 1 + q.1.val; omega
  · change r.height ≤ r.height + q.2.val; omega

/-- The original source and every cell of the whole actual east room contribute disjoint initial holes. -/
private theorem initial_inventory_full_room (r : ColumnScan.Input) :
    r.sourceHoles + (r.width + 2 + r.extraWidth) * ((wideReader r).outputHeight - r.height) ≤
      (holes (nextSource r).initial).card := by
  let A := r.initial.empty.image (sourceEmbed r)
  let R := Finset.univ.image (fullRoomEmbed r)
  have hA : A ⊆ holes (nextSource r).initial := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (sourceEmbed_mem_initial r q).mpr hq
  have hR : R ⊆ holes (nextSource r).initial := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact fullRoom_mem_initial r q
  have hd : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun q => q.1.val) he
    have ha := a.2.isLt
    change r.height + b.2.val = a.2.val at hx
    omega
  have hc := Finset.card_le_card (Finset.union_subset hA hR)
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (sourceEmbed_injective r),
    Finset.card_image_of_injective _ (fullRoomEmbed_injective r)] at hc
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ColumnScan.Input.sourceHoles] using hc

end PushPuzzle.Push.Cyclic
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

/-- At least `h` old auxiliary rows are available under the erase staging invariant. -/
private theorem auxiliary_height_ge (r : ColumnScan.Input) (hk : r.height ≤ r.quota) :
    r.height ≤ (wideEraseReader r).outputHeight - r.height := by
  have hs := (wideEraseReader r).separation
  change r.quota + max r.sourceHoles r.width + 4 ≤ (wideEraseReader r).length at hs
  change r.height ≤ r.height + (wideEraseReader r).length - r.height
  omega

/-- The wider erase source retains every one of its `2w+2` room holes on every old auxiliary row. -/
private theorem initial_inventory_lower (r : ColumnScan.Input) :
    r.sourceHoles + (2 * r.width + 2) * ((wideEraseReader r).outputHeight - r.height) ≤
      (holes (Cyclic.turn (eraseDock r).compile).initial).card := by
  have h := Cyclic.initial_inventory_full_room (asReader r)
  change r.sourceHoles + (r.width + 2 + r.width) *
    ((wideEraseReader r).outputHeight - r.height) ≤ _ at h
  rw [show r.width + 2 + r.width = 2 * r.width + 2 by omega] at h
  exact h

/-- The real extra room inventory pays height many north reads for any selected family of original columns. -/
theorem erase_read_budget (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (selected : Finset (Fin r.width)) (future : ℕ) (hfuture : future ≤ r.sourceHoles) :
    future + r.height * selected.card + (r.width + 2) * ((wideEraseReader r).outputHeight - r.height) ≤
      (holes (Cyclic.turn (eraseDock r).compile).initial).card := by
  have hcols : selected.card ≤ r.width := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  have hheight := auxiliary_height_ge r hk
  have hselected := Nat.mul_le_mul_left r.height hcols
  have hroom := Nat.mul_le_mul_right r.width hheight
  have hi := initial_inventory_lower r
  nlinarith

end PushPuzzle.Push.CyclicErase
