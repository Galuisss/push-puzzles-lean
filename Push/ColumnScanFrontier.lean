/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScan
public import Push.StripFrontier

/-! The actual reader's western strips have exactly one southern needle per original column. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

private theorem holes_initial : holes r.initialState.toState = r.empty :=
  r.initialState.holes_toState

/-- The initial holes of every western strip are either original source holes or needles. -/
theorem initial_split {cut : ℕ} (hcut : cut ≤ r.width) :
    Split cut r.targetLevel (r.height - 1) r.initialState.toState := by
  intro q hq hx
  rw [holes_initial, empty, Finset.mem_union] at hq
  rcases hq with hs | ha
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
    left
    change a.2.val ≤ r.height - 1
    have := a.2.isLt
    omega
  · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (((he | he | he) | he) | he)
    · have := congrArg (fun q => q.1.val) he
      change q.1.val = r.width at this
      omega
    · have := congrArg (fun q => q.1.val) he
      change q.1.val = r.width at this
      omega
    · have := congrArg (fun q => q.1.val) he
      change q.1.val = r.width at this
      omega
    · have := (Finset.mem_filter.mp he).2.1
      omega
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      right
      exact r.targetLevel_le_needleLevel i

/-- The reader starts north of every western strip's needle band. -/
theorem initial_north (cut : ℕ) : North cut r.targetLevel r.initialState.toState := by
  intro _
  have hy := r.initial.player.2.isLt
  have ht := r.targetLevel_lower
  change r.initial.player.2.val < r.targetLevel
  omega

/-- Every actual initial southern hole is its column's original needle. -/
theorem mem_south_initial {cut : ℕ} (hcut : cut ≤ r.width)
    (q : Cell r.outputWidth r.outputHeight) :
    q ∈ south cut r.targetLevel r.initialState.toState ↔
      ∃ i : Fin r.width, i.val < cut ∧ r.needle i = q := by
  constructor
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    rw [holes_initial, empty, Finset.mem_union] at hq
    rcases hq with hs | ha
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
      have hya := a.2.isLt
      have ht := r.targetLevel_lower
      change r.targetLevel ≤ a.2.val at hy
      omega
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with (((he | he | he) | he) | he)
      · have := congrArg (fun q => q.1.val) he
        change q.1.val = r.width at this
        omega
      · have := congrArg (fun q => q.1.val) he
        change q.1.val = r.width at this
        omega
      · have := congrArg (fun q => q.1.val) he
        change q.1.val = r.width at this
        omega
      · have := (Finset.mem_filter.mp he).2.1
        omega
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
        refine ⟨i, ?_, hi⟩
        have := congrArg (fun q => q.1.val) hi
        change i.val = q.1.val at this
        omega
  · rintro ⟨i, hi, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, hi, r.targetLevel_le_needleLevel i⟩
    rw [holes_initial, empty]
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩))

/-- A cut after `cut` source columns contains exactly `cut` original southern needles. -/
theorem south_initial_card {cut : ℕ} (hcut : cut ≤ r.width) :
    (south cut r.targetLevel r.initialState.toState).card = cut := by
  let pin (i : Fin cut) := r.needle ⟨i.val, i.isLt.trans_le hcut⟩
  have hinj : Function.Injective pin := by
    intro i j hij
    exact Fin.ext (congrArg (fun q => q.1.val) hij)
  have heq : south cut r.targetLevel r.initialState.toState = Finset.univ.image pin := by
    ext q
    rw [r.mem_south_initial hcut]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, rfl⟩
    · intro hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨⟨i.val, i.isLt.trans_le hcut⟩, i.isLt, rfl⟩
  rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Before the first southern visit, no northern hole reaches below the source plus the strip width. -/
theorem north_prefix_split {cut : ℕ} (hcut : cut ≤ r.width)
    {t : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none cut r.targetLevel)
      r.initialState.toState t) :
    Split cut r.targetLevel (r.height - 1 + cut) t := by
  obtain ⟨f, hs, _, _, hb⟩ := reachable_budget (w := r.outputWidth) (h := r.outputHeight)
    hr (r.initial_split hcut) (r.initial_north cut)
  rw [r.south_initial_card hcut] at hb
  intro q hq hx
  exact (hs q hq hx).imp (by omega) id

end PushPuzzle.Push.ColumnScan.Input
