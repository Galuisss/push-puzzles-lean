/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanQuotas

/-! A successful ordinary column reader yields one real source corner state paying every quota. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

/-- Cropping preserves the exact live hole count in each original source column. -/
theorem crop_column_card (s : State r.outputWidth r.outputHeight) (i : Fin r.width) :
    (ReadBudgetProjection.sourceCells i.val r.height s).card =
      ((holes (r.cropState s)).filter fun q => q.1 = i).card := by
  have heq : ReadBudgetProjection.sourceCells i.val r.height s =
      ((holes (r.cropState s)).filter fun q => q.1 = i).image r.embed := by
    ext q
    constructor
    · intro hq
      obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
      let a : Cell r.width r.height :=
        (⟨q.1.val, by rw [hx]; exact i.isLt⟩, ⟨q.2.val, hy⟩)
      have he : r.embed a = q := by apply Prod.ext <;> apply Fin.ext <;> rfl
      refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨?_, Fin.ext hx⟩, he⟩
      exact (r.cropState_mem_holes s a).mpr (he.symm ▸ hq)
    · intro hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha, hx⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(r.cropState_mem_holes s a).mp ha,
        congrArg Fin.val hx, a.2.isLt⟩
  rw [heq, Finset.card_image_of_injective _ r.embed_injective]

/-- All column quotas are witnessed by the same reachable source state at its corner. -/
theorem compile_solvable_implies_corner_quotas (hsol : r.compile.Solvable) :
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧
      ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ ((holes s).filter fun q => q.1 = i).card := by
  obtain ⟨finish, hfinish, hp⟩ := hsol
  have hfx : finish.player.1.val = 0 := congrArg (fun q => q.1.val) hp
  have hfy : finish.player.2.val = r.targetLevel := congrArg (fun q => q.2.val) hp
  obtain ⟨s, hpre, hland, hsf⟩ := r.exists_landing_prefix hfinish hfx hfy.ge
  obtain ⟨hs, hcorner, hholes, hcount⟩ := r.landing_source_prefix hpre hsf hfx hfy.ge hland
  refine ⟨r.cropState s, hs, hcorner, ?_⟩
  intro i
  have hq := r.landing_column_quotas hpre hsf hfx hfy hland i
  rwa [r.crop_column_card s i] at hq

end PushPuzzle.Push.ColumnScan.Input
