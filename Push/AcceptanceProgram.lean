/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramLayout

/-! Emission and exhaustion of the actual marked source's compact multilevel acceptance word. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem main_cleanup_mem (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    Template.clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p)) ∈ schedule l p k := by
  simp only [schedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem core_cleanup_mem (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    Template.clear .north (cores l p) ∈ schedule l p k := by
  have hh : Template.clear .north (cores l p) ∈ pageChecks l p .lower := by
    simp only [pageChecks, ite_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  simp only [schedule, List.mem_append]
  exact Or.inl (Or.inr hh)

private theorem upper_cleanup_mem (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    Template.clear .north (auxiliaries l p \ live l p .upper) ∈ schedule l p k := by
  have hh : Template.clear .north (auxiliaries l p \ live l p .upper) ∈ pageChecks l p .upper := by
    simp only [pageChecks, reduceCtorEq, ite_false, List.mem_append, List.mem_singleton]
    exact Or.inl trivial
  simp only [schedule, List.mem_append]
  exact Or.inr hh

private theorem upper_level_cleanup_mem (l : PortLayout) (p : Scales.Parameters) (k j : ℕ)
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    Template.clear .north (levelColumns l p .upper j) ∈ schedule l p k := by
  have hh : Template.clear .north (levelColumns l p .upper j) ∈ pageChecks l p .upper := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
    have he : j - 1 + 1 = j := by omega
    simp only [he, reduceCtorEq, ite_false, List.mem_cons]
    exact Or.inr (Or.inl trivial)
  simp only [schedule, List.mem_append]
  exact Or.inr hh

/-- The concrete cleanup rounds cover every real board column, so no target hole survives. -/
private theorem schedule_remaining_empty (l : PortLayout) (p : Scales.Parameters) (k : ℕ)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) : (emit (schedule l p k) E).remaining = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have hmain := emit_clear_excluded (main_cleanup_mem l p k) hq
  have hcore := emit_clear_excluded (core_cleanup_mem l p k) hq
  have hupper := emit_clear_excluded (upper_cleanup_mem l p k) hq
  change q.1.val ∉ Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p) at hmain
  change q.1.val ∉ cores l p at hcore
  change q.1.val ∉ auxiliaries l p \ live l p .upper at hupper
  have hx : q.1.val ∈ auxiliaries l p ∪ cores l p := by
    by_contra hn
    exact hmain (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.1.isLt, hn⟩)
  have haux : q.1.val ∈ auxiliaries l p := (Finset.mem_union.mp hx).resolve_right hcore
  have hlive : q.1.val ∈ live l p .upper := by
    by_contra hn
    exact hupper (Finset.mem_sdiff.mpr ⟨haux, hn⟩)
  simp only [live, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hlive
  obtain ⟨a, ⟨ha, hlevel⟩, hacol⟩ := hlive
  have hmem : q.1.val ∈ levelColumns l p .upper a.level := by
    simp only [levelColumns, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
    exact ⟨a, ⟨ha, rfl⟩, hacol⟩
  exact emit_clear_excluded (upper_level_cleanup_mem l p k a.level hlevel.1 hlevel.2) hq hmem

/-- The actual emitted rounds and quotas for the same complete canonical target bitmap. -/
def program (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : Emission (p.W + 1) (p.H + 1) :=
  emit (schedule l p (targetHoles l p target \ Boundary.frame).card) (targetHoles l p target)

/-- The actual canonical target pays every emitted prefix quota and ends with no remaining holes. -/
theorem program_accepts_target (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    Scan.eval (instructions (program l p target).rounds) (targetHoles l p target) = some ∅ := by
  rw [program, emit_eval, schedule_remaining_empty]

/-- The complete physical schedule has a constant number of blocks for every fixed level bound. -/
theorem program_rounds_length (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    (program l p target).rounds.length = 4 * p.levels + 25 := by
  rw [program, emit_rounds_length, schedule_length]

/-- Every lost clear hole is explicitly counted in the target's exact payment identity. -/
theorem program_accounting (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    Scan.quota (instructions (w := p.W + 1) (h := p.H + 1) (program l p target).rounds) +
      (program l p target).discarded = (targetHoles l p target).card := by
  have hh := emit_accounting (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target)
  rw [schedule_remaining_empty, Finset.card_empty, Nat.zero_add] at hh
  rw [quota_instructions]
  exact hh

end PushPuzzle.Push.AcceptanceProgram
