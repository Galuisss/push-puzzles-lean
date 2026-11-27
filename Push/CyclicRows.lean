/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicOriginalHoles

/-! Next-stage column observations count exactly the same physical original-source rows. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- The physical quarter turn maps each entire old row bijectively to one new column. -/
private theorem turn_column_card {w h : ℕ} (s : State w h) (row : ℕ) :
    ((holes ((turnGeometry w h).state s)).filter fun q => q.1.val = row).card =
      ((holes s).filter fun q => q.2.val = row).card := by
  symm
  apply Finset.card_bij (fun q _ => (turnGeometry w h).cells q)
  · intro q hq
    obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨by simpa only [mem_holes, GridIsometry.mem_boxes] using hq, hy⟩
  · intro p hp q hq he
    exact (turnGeometry w h).cells.injective he
  · intro q hq
    obtain ⟨p, rfl⟩ := (turnGeometry w h).cells.surjective q
    obtain ⟨hp, hy⟩ := Finset.mem_filter.mp hq
    refine ⟨p, Finset.mem_filter.mpr ⟨?_, hy⟩, rfl⟩
    simpa only [mem_holes, GridIsometry.mem_boxes] using hp

namespace Commit

variable {r : ColumnScan.Input} {finish : State (dock r).outputWidth (dock r).outputHeight}
  (c : Commit r finish)

/-- Source rows have no peripheral holes after commitment, so their full counts equal the original-cell counts. -/
private theorem original_row_card {s : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state s) (row : ℕ) (hy : row < r.height) :
    ((originalHoles r s).filter fun q => q.2.val = row).card =
      ((holes s).filter fun q => q.2.val = row).card := by
  have heq : (((originalHoles r s).filter fun q => q.2.val = row).image (unturnedSourceEmbed r)) =
      ((holes s).filter fun q => q.2.val = row) := by
    ext q
    constructor
    · intro hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha, hay⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(mem_originalHoles r s a).mp ha, hay⟩
    · intro hq
      obtain ⟨hq, hqy⟩ := Finset.mem_filter.mp hq
      obtain ⟨hleft, hright⟩ := c.source_row_columns hr q hq (by omega)
      let a : Cell r.width r.height :=
        (⟨q.1.val - 2, by omega⟩, ⟨q.2.val, by omega⟩)
      have he : unturnedSourceEmbed r a = q := by
        apply Prod.ext <;> apply Fin.ext
        · change q.1.val - 2 + 2 = q.1.val
          omega
        · rfl
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨(mem_originalHoles r s a).mpr (he.symm ▸ hq), hqy⟩, he⟩
  have hinj : Function.Injective (unturnedSourceEmbed r) := fun _ _ he =>
    (wideReader r).embed_injective ((dock r).embed_injective he)
  rw [← heq, Finset.card_image_of_injective _ hinj]

include c in
/-- Each next-reader source column observes precisely an original source row of the same committed computation. -/
theorem next_source_row_card (row : ℕ) (hy : row < r.height) :
    ((holes ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state finish)).filter
      fun q => q.1.val = row).card =
      ((originalHoles r finish).filter fun q => q.2.val = row).card := by
  rw [turn_column_card, c.original_row_card c.suffix row hy]

end Commit
end PushPuzzle.Push.Cyclic
