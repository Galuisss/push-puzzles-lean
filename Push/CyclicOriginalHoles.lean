/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicResidual

/-! Exact original-cell residuals at every point of the same physical cyclic suffix. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS ReflectedFrontier ReaderResidual

/-- Restrict the actual dock bitmap to the original source cell names. -/
def originalHoles (r : ColumnScan.Input)
    (s : State (dock r).outputWidth (dock r).outputHeight) : Finset (Cell r.width r.height) :=
  Finset.univ.filter fun q => unturnedSourceEmbed r q ∈ holes s

@[simp] theorem mem_originalHoles (r : ColumnScan.Input)
    (s : State (dock r).outputWidth (dock r).outputHeight) (q : Cell r.width r.height) :
    q ∈ originalHoles r s ↔ unturnedSourceEmbed r q ∈ holes s := by
  simp only [originalHoles, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem original_column_card (r : ColumnScan.Input) (i : Fin r.width)
    (s : State (dock r).outputWidth (dock r).outputHeight) :
    ((originalHoles r s).filter fun q => q.1 = i).card = (sourceColumn r i s).card := by
  have heq : (((originalHoles r s).filter fun q => q.1 = i).image (unturnedSourceEmbed r)) =
      sourceColumn r i s := by
    ext q
    constructor
    · intro hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha, hx⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(mem_originalHoles r s a).mp ha,
        by change a.1.val + 2 = i.val + 2; rw [hx], a.2.isLt⟩
    · intro hq
      obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
      let a : Cell r.width r.height := (i, ⟨q.2.val, hy⟩)
      have he : unturnedSourceEmbed r a = q := by
        apply Prod.ext <;> apply Fin.ext
        · exact hx.symm
        · rfl
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨(mem_originalHoles r s a).mpr (he.symm ▸ hq), rfl⟩, he⟩
  have hinj : Function.Injective (unturnedSourceEmbed r) := fun _ _ he =>
    (wideReader r).embed_injective ((dock r).embed_injective he)
  rw [← heq, Finset.card_image_of_injective _ hinj]

namespace Commit

variable {r : ColumnScan.Input} {finish : State (dock r).outputWidth (dock r).outputHeight}
  (c : Commit r finish)

private theorem original_in_source {s : State (dock r).outputWidth (dock r).outputHeight}
    {q : Cell r.width r.height} (hq : unturnedSourceEmbed r q ∈ holes s) :
    unturnedSourceEmbed r q ∈ source (r.width + 2) r.height s :=
  Finset.mem_filter.mpr ⟨hq, by change q.1.val + 2 < r.width + 2; have := q.1.isLt; omega, q.2.isLt⟩

/-- The exact final original-cell residual is a northern prefix of the same recovered source. -/
theorem original_remainder {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t) :
    BottomRemainder (holes c.sourceState) (originalHoles r t) := by
  have hrem := c.source_remainder hr
  refine ⟨?_, ?_⟩
  · intro q hq
    have hh := hrem.subset (original_in_source (r := r) ((mem_originalHoles r t q).mp hq))
    exact (c.source_hole q).mpr (Finset.mem_filter.mp hh).1
  · intro p hp q hq hx hy
    have hp' := original_in_source (r := r) ((mem_originalHoles r t p).mp hp)
    have hq' := original_in_source (r := r) ((c.source_hole q).mp hq)
    have hh := hrem.northern _ hp' _ hq' (by
      apply Fin.ext
      change q.1.val + 2 = p.1.val + 2
      rw [hx]) hy
    exact (mem_originalHoles r t q).mpr (Finset.mem_filter.mp hh).1

/-- Every first-round quota is consumed in the exact same original-cell bitmap. -/
theorem original_consumed_quotas : ∀ i : Fin r.width,
    r.quotas.getD i.val 0 + ((originalHoles r finish).filter fun q => q.1 = i).card ≤
      ((holes c.sourceState).filter fun q => q.1 = i).card := by
  intro i
  have hb := c.consumed_quotas i
  rwa [← original_column_card r i finish, c.source_column_card i] at hb

end Commit
end PushPuzzle.Push.Cyclic
