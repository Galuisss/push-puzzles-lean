/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasCuts
public import PushPush.Doors.ForwardControl
public import PushPush.Doors.StockGeometry

/-! All parked register assignments have the same remaining column quotas. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell)
open Push.AcceptanceProgram

variable {I : Instance}

/-- The selected physical register cell from every original door. -/
def registerCells (S : Stock I) : Finset (Cell (layout false I).width (layout false I).height) :=
  (layout false I).raster (S.registerPoints false)

theorem registerCells_card (S : Stock I) : S.registerCells.card = I.doors.length := by
  rw [registerCells, (layout false I).raster_card]
  · change (Finset.univ.image (S.registerPoint false)).card = I.doors.length
    rw [Finset.card_image_of_injective _ (S.registerPoint_injective false)]
    simp
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hi := Register.row_bounds (S.register i)
    exact ⟨(doorCell false I i (S.register i).row (by omega)).1.isLt,
      (doorCell false I i (S.register i).row (by omega)).2.isLt⟩

private theorem registerCells_column (S : Stock I)
    {p : Cell (layout false I).width (layout false I).height} (hp : p ∈ S.registerCells) :
    p.1.val = (layout false I).rackX - 1 :=
  S.registerPoints_column false (((layout false I).mem_raster _ _).mp hp)

private theorem registerCells_untouched (S : Stock I)
    {p : Cell (layout false I).width (layout false I).height} (hp : p ∈ S.registerCells) :
    p ∉ allRegions ((layout false I).quotaTemplates.take 6) := by
  obtain ⟨i, _, he⟩ := Finset.mem_image.mp (((layout false I).mem_raster _ _).mp hp)
  apply register_not_quotaPrefix I i (S.register i) p
  · exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.snd he).symm

private theorem registerPoints_disjoint_shared (S : Stock I) :
    Disjoint (layout false I).readerShared (S.registerPoints false) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hbefore := S.registerPoint_before false hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  have hi := Register.row_bounds (S.register i)
  rcases Finset.mem_union.mp hp with hp | hp
  · apply fixed_door_clear false I i
      (doorCell false I i (S.register i).row (by omega)) rfl ?_ ?_ hp
    all_goals dsimp; omega
  · have he := congrArg Prod.snd (Finset.mem_singleton.mp hp)
    have hs := targetRow_lower_bound I
    change 90 * I.doors.length ≤ (layout false I).stop at hs
    dsimp at he hbefore
    omega

theorem registerCells_disjoint_shared (S : Stock I) :
    Disjoint ((layout false I).raster (layout false I).readerShared) S.registerCells :=
  (layout false I).raster_disjoint S.registerPoints_disjoint_shared

theorem boxes_parked (S : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop) :
    S.boxes false = (layout false I).raster (layout false I).readerShared ∪ S.registerCells := by
  ext p
  simp only [boxes, rawBoxes, registerCells, Layout.readerShared, Layout.mem_raster,
    Finset.mem_union, Finset.mem_singleton, hs, atRow]
  tauto

/-- Before the final north round, each door assignment has the same visible prefix holes. -/
theorem prefix_holes_agree (S T : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop)
    (ht : T.signal = atRow false I (layout false I).stop)
    (p : Cell (layout false I).width (layout false I).height)
    (hp : p ∈ allRegions ((layout false I).quotaTemplates.take 6)) :
    p ∈ (S.boxes false)ᶜ ↔ p ∈ (T.boxes false)ᶜ := by
  have hS : p ∉ S.registerCells := fun h => S.registerCells_untouched h hp
  have hT : p ∉ T.registerCells := fun h => T.registerCells_untouched h hp
  rw [S.boxes_parked hs, T.boxes_parked ht]
  simp only [Finset.mem_compl, Finset.mem_union, hS, hT, or_false]

private theorem filter_holes {α : Type} [DecidableEq α] [Fintype α]
    (common registers removed : Finset α) (pred : α → Prop) [DecidablePred pred] :
    ((common ∪ registers)ᶜ \ removed).filter pred = ((commonᶜ \ removed).filter pred) \ registers := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_compl, Finset.mem_union]
  tauto

/-- The remaining holes in any column are independent of all parked register choices. -/
private theorem remaining_column_card (S : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop) (x : ℕ) :
    (((S.boxes false)ᶜ \ allRegions ((layout false I).quotaTemplates.take 6)).filter
      fun p => p.1.val = x).card =
      ((((layout false I).raster (layout false I).readerShared)ᶜ \
        allRegions ((layout false I).quotaTemplates.take 6)).filter fun p => p.1.val = x).card -
        (if x = (layout false I).rackX - 1 then I.doors.length else 0) := by
  let common : Finset (Cell (layout false I).width (layout false I).height) :=
    (((layout false I).raster (layout false I).readerShared)ᶜ \
      allRegions ((layout false I).quotaTemplates.take 6)).filter fun p => p.1.val = x
  have he : ((S.boxes false)ᶜ \ allRegions ((layout false I).quotaTemplates.take 6)).filter
      (fun p => p.1.val = x) = common \ S.registerCells := by
    rw [S.boxes_parked hs]
    exact filter_holes _ _ _ _
  rw [he]
  by_cases hx : x = (layout false I).rackX - 1
  · have hsub : S.registerCells ⊆ common := by
      intro p hp
      have hnot : p ∉ (layout false I).raster (layout false I).readerShared := by
        intro hq
        exact Finset.disjoint_left.mp S.registerCells_disjoint_shared hq hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_compl.mpr hnot, S.registerCells_untouched hp⟩,
        (S.registerCells_column hp).trans hx.symm⟩
    rw [Finset.card_sdiff_of_subset hsub, S.registerCells_card, ite_eq_left hx]
  · have hd : Disjoint common S.registerCells := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      have hp := (Finset.mem_filter.mp hp).2
      have hq := S.registerCells_column hq
      exact hx (hp.symm.trans hq)
    have he' : common \ S.registerCells = common := by
      ext p
      simp only [Finset.mem_sdiff]
      exact ⟨And.left, fun hp => ⟨hp, fun hq => Finset.disjoint_left.mp hd hp hq⟩⟩
    rw [he', ite_eq_right hx, Nat.sub_zero]

theorem remaining_columns_equal (S T : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop)
    (ht : T.signal = atRow false I (layout false I).stop) (x : ℕ) :
    (((S.boxes false)ᶜ \ allRegions ((layout false I).quotaTemplates.take 6)).filter
      fun p => p.1.val = x).card =
    (((T.boxes false)ᶜ \ allRegions ((layout false I).quotaTemplates.take 6)).filter
      fun p => p.1.val = x).card := by
  rw [S.remaining_column_card hs, T.remaining_column_card ht]

end PushPuzzle.PushPush.Doors.Source.Stock
