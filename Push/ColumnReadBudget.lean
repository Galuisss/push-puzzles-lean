/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Seal

/-! One-dimensional reader-frontier advance consumes distinct original source holes. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnReadBudget

open Seal

/-- Holes in the inaccessible source part of the column. -/
def sources (row : ℤ) (E : Finset ℤ) : Finset ℤ := E.filter fun z => row ≤ z

/-- All holes lie behind the reader frontier or in the source. -/
def Split (row frontier : ℤ) (E : Finset ℤ) : Prop :=
  ∀ z ∈ E, z ≤ frontier ∨ row ≤ z

/-- Deletions and complete column transports whose support and new hole remain outside source. -/
inductive Step (row : ℤ) : Finset ℤ → Finset ℤ → Prop
  | erase (E : Finset ℤ) (q : ℤ) (hq : q ∈ E) : Step row E (E.erase q)
  | transport (E : Finset ℤ) (a b q : ℤ) (support : a ∈ E) (destination : q ∈ E)
      (adjacent : b = a + 1 ∨ b = a - 1) (intermediate : Between a q b)
      (occupied : ∀ z ∈ E, ¬ Between a q z) (support_outside : a < row)
      (new_outside : b < row) : Step row E (insert b (E.erase q))

private theorem sources_transport {row b q : ℤ} {E : Finset ℤ} (hb : b < row) :
    sources row (insert b (E.erase q)) = (sources row E).erase q := by
  ext z
  simp only [sources, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  by_cases hz : z = b
  · subst z
    have hn : ¬ row ≤ b := by omega
    simp [hn]
  · simp only [hz, false_or]
    tauto

/-- Arbitrary external deletion preserves the frontier and reduces the source inventory. -/
private theorem delete_budget {row f : ℤ} {E F : Finset ℤ} (hs : Split row f E) (hF : F ⊆ E) :
    Split row f F ∧ (sources row F).card ≤ (sources row E).card := by
  refine ⟨fun z hz => hs z (hF hz), Finset.card_le_card ?_⟩
  intro z hz
  exact Finset.mem_filter.mpr ⟨hF (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩

/-- A new frontier cell lies one step beyond the old frontier and spends a source hole. -/
private theorem transport_budget {row f a b q : ℤ} {E : Finset ℤ}
    (hs : Split row f E) (ha : a ∈ E) (hq : q ∈ E)
    (hadj : b = a + 1 ∨ b = a - 1) (hmid : Between a q b)
    (haout : a < row) (hbout : b < row) :
    ∃ f', Split row f' (insert b (E.erase q)) ∧ f ≤ f' ∧
      f' + ((sources row (insert b (E.erase q))).card : ℤ) ≤
        f + ((sources row E).card : ℤ) := by
  have hsource := sources_transport (E := E) (q := q) hbout
  by_cases hadvance : f < b
  · have haf : a ≤ f := (hs a ha).resolve_right (by omega)
    have hbf : b = f + 1 := by rcases hadj with he | he <;> omega
    have hqsource : q ∈ sources row E := by
      apply Finset.mem_filter.mpr ⟨hq, ?_⟩
      have hfq : f < q := by rcases hmid with hmid | hmid <;> omega
      exact (hs q hq).resolve_left (by omega)
    refine ⟨f + 1, ?_, by omega, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inl hbf.le
      · exact (hs z (Finset.mem_of_mem_erase hz)).imp (by omega) id
    · have hc := Finset.card_erase_add_one hqsource
      rw [hsource]
      omega
  · refine ⟨f, ?_, le_rfl, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inl (by omega)
      · exact hs z (Finset.mem_of_mem_erase hz)
    · rw [hsource]
      have hc := Finset.card_le_card (Finset.erase_subset q (sources row E))
      omega

/-- Every allowed operation preserves the derived frontier-plus-inventory budget. -/
private theorem step_budget {row f : ℤ} {E F : Finset ℤ} (hm : Step row E F) (hs : Split row f E) :
    ∃ f', Split row f' F ∧ f ≤ f' ∧
      f' + ((sources row F).card : ℤ) ≤ f + ((sources row E).card : ℤ) := by
  cases hm with
  | erase q _ =>
    obtain ⟨hs', hc⟩ := delete_budget hs (Finset.erase_subset q _)
    exact ⟨f, hs', le_rfl, by omega⟩
  | transport a b q ha hq hadj hmid _ haout hbout =>
    exact transport_budget hs ha hq hadj hmid haout hbout

/-- No column operation can create a new source hole. -/
theorem sources_subset {row : ℤ} {E F : Finset ℤ}
    (hr : Relation.ReflTransGen (Step row) E F) : sources row F ⊆ sources row E := by
  induction hr with
  | refl => exact Finset.Subset.refl _
  | @tail U V _ hm ih =>
    apply Finset.Subset.trans ?_ ih
    cases hm with
    | erase q _ =>
      intro z hz
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
    | transport a b q _ _ _ _ _ _ hbout =>
      rw [sources_transport hbout]
      exact Finset.erase_subset _ _

/-- The full trajectory budget includes every source deletion and every frontier advance. -/
private theorem reachable_budget {row f : ℤ} {E F : Finset ℤ}
    (hr : Relation.ReflTransGen (Step row) E F) (hs : Split row f E) :
    ∃ f', Split row f' F ∧ f ≤ f' ∧
      f' + ((sources row F).card : ℤ) ≤ f + ((sources row E).card : ℤ) := by
  induction hr with
  | refl => exact ⟨f, hs, le_rfl, le_rfl⟩
  | tail _ hm ih =>
    obtain ⟨g, hg, hfg, hbudget⟩ := ih
    obtain ⟨g', hg', hgg', hbudget'⟩ := step_budget hm hg
    exact ⟨g', hg', hfg.trans hgg', hbudget'.trans hbudget⟩

/-- Each reader-frontier advance is paid by a different original source hole. -/
theorem advance_paid_by_distinct_sources {row f z : ℤ} {E F : Finset ℤ}
    (hr : Relation.ReflTransGen (Step row) E F) (hs : Split row f E)
    (hz : z ∈ F) (hzout : z < row) :
    z - f ≤ ((sources row E \ sources row F).card : ℤ) := by
  obtain ⟨g, hg, _, hbudget⟩ := reachable_budget hr hs
  have hzg := (hg z hz).resolve_right (by omega)
  have hc := Finset.card_sdiff_add_card_eq_card (sources_subset hr)
  omega

end PushPuzzle.Push.ColumnReadBudget
