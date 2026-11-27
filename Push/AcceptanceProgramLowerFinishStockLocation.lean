/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramLowerFinishStockColumns
public import Push.AcceptanceProgramLower
import all Push.AcceptanceProgramLayout

/-! Every literal lower finish either selects a nonlive column or follows its own level's row read. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Columns carrying an actual lower-page interlevel marker. -/
@[expose] def lowerLiveColumns (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  (((pageColumns l p .lower).filter fun a => decide (1 ≤ a.level ∧ a.level < p.levels)).map PageColumn.column).toFinset

/-- Actual lower-page metadata columns at one specified level. -/
@[expose] def lowerLevelColumns (l : PortLayout) (p : Scales.Parameters) (j : ℕ) : Finset ℕ :=
  (((pageColumns l p .lower).filter fun a => a.level == j).map PageColumn.column).toFinset

private theorem lowerFinish_columns (p : Scales.Parameters) (a b : Finset ℕ)
    (he : lowerFinish p a = lowerFinish p b) : a = b := by
  have hr := (Template.read.inj he).2
  ext x
  constructor
  · intro hx
    have hm := (mem_prefixRequests a (fun _ => p.D + 1) x (p.D + 1)).mpr ⟨hx, rfl⟩
    rw [hr] at hm
    exact ((mem_prefixRequests b _ _ _).mp hm).1
  · intro hx
    have hm := (mem_prefixRequests b (fun _ => p.D + 1) x (p.D + 1)).mpr ⟨hx, rfl⟩
    rw [← hr] at hm
    exact ((mem_prefixRequests a _ _ _).mp hm).1

private theorem no_lowerFinish_upper (l : PortLayout) (p : Scales.Parameters) (cols : Finset ℕ) :
    lowerFinish p cols ∉ pageChecks l p .upper := by
  simp [pageChecks, lowerFinish, readRows]

private def lowerPairs (l : PortLayout) (p : Scales.Parameters) (ks : List ℕ) : List Template :=
  ks.flatMap fun k => [readRows p .west {p.H - (p.Y (k + 1) + p.Y (k + 2)) / 2},
    lowerFinish p (levelColumns l p .lower (k + 1))]

private theorem pairs_location (l : PortLayout) (p : Scales.Parameters) (ks : List ℕ)
    (before after : List Template) (cols : Finset ℕ) (x : ℕ) (hx : x ∈ cols)
    (hs : lowerPairs l p ks ++ pageChecks l p .upper = before ++ lowerFinish p cols :: after) :
    ∃ k ∈ ks, x ∈ levelColumns l p .lower (k + 1) ∧
      readRows p .west {p.H - (p.Y (k + 1) + p.Y (k + 2)) / 2} ∈ before := by
  induction ks generalizing before with
  | nil =>
    have hm : lowerFinish p cols ∈ pageChecks l p .upper := by
      rw [show pageChecks l p .upper = before ++ lowerFinish p cols :: after from hs]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    exact False.elim (no_lowerFinish_upper l p cols hm)
  | cons k ks ih =>
    cases before with
    | nil => simp [lowerPairs, readRows, lowerFinish] at hs
    | cons b before =>
      cases before with
      | nil =>
        simp only [lowerPairs, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at hs
        have hc := lowerFinish_columns p _ _ hs.2.1
        refine ⟨k, List.mem_cons_self .., hc.symm ▸ hx, ?_⟩
        exact hs.1.symm ▸ List.mem_cons_self ..
      | cons c before =>
        simp only [lowerPairs, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at hs
        obtain ⟨j, hj, hcol, hrow⟩ := ih before hs.2.2
        exact ⟨j, List.mem_cons_of_mem _ hj, hcol, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrow)⟩

/-- At any actual lower-finish occurrence, each selected column is nonlive or its matching row read is already in the prefix. -/
theorem lowerFinish_location (l : PortLayout) (p : Scales.Parameters)
    (before after : List Template) (cols : Finset ℕ)
    (hs : pageChecks l p .lower ++ pageChecks l p .upper = before ++ .read .south (prefixRequests cols fun _ => p.D + 1) :: after)
    (x : ℕ) (hx : x ∈ cols) :
    x ∈ auxiliaries l p \ lowerLiveColumns l p ∨
      ∃ j, 1 ≤ j ∧ j < p.levels ∧ x ∈ lowerLevelColumns l p j ∧
        readRows p .west {p.H - (p.Y j + p.Y (j + 1)) / 2} ∈ before := by
  change (lowerFinish p (auxiliaries l p \ live l p .lower) ::
    readRows p .west {p.H - p.Y 1 / 2} :: .clear .north (cores l p) ::
      lowerPairs l p (List.range (p.levels - 1))) ++ pageChecks l p .upper = _ at hs
  cases before with
  | nil =>
    have he := (List.cons.inj hs).1
    exact Or.inl ((lowerFinish_columns p _ _ he).symm ▸ hx)
  | cons a before =>
    have hs := (List.cons.inj hs).2
    cases before with
    | nil => simp [readRows] at hs
    | cons b before =>
      have hs := (List.cons.inj hs).2
      cases before with
      | nil => simp at hs
      | cons c before =>
        have hs := (List.cons.inj hs).2
        obtain ⟨k, hk, hcol, hrow⟩ := pairs_location l p _ before after cols x hx hs
        have hkm := List.mem_range.mp hk
        exact Or.inr ⟨k + 1, by omega, by omega, hcol,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrow))⟩

end PushPuzzle.Push.AcceptanceProgram
