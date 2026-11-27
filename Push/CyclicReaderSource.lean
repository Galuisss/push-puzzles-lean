/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderCompiler
public import Push.CyclicSchedulePolyTime

/-! Prepare actual southeast-source program families for the fixed-round ordinary Push-* compiler. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicReader

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM

/-- Actual source games with a computed first south read and a fixed-shape west-leading continuation. -/
structure SourceFamily (α : Type) (enc : α ↪ List Bool) (shapes : List (Bool × Direction)) where
  source : α → Push.Instance
  requests : α → List (ℕ × ℕ)
  rounds : α → List Round
  source_polyTime : ComputableInPolyTime source enc Push.encoding
  requests_polyTime : ComputableInPolyTime requests enc Scan.encRequests
  rounds_polyTime : ComputableInPolyTime rounds enc encRounds
  shapes_eq : ∀ a, (rounds a).map Round.shape = (true, .west) :: shapes
  requests_bounded : ∀ a, ∀ request ∈ requests a, request.1 < (source a).width
  rounds_bounded : ∀ a, Scan.Bounded (instructions (w := (source a).width) (h := (source a).height) (rounds a))
  budget : ∀ a, ((requests a).map Prod.snd).sum +
    Scan.quota (instructions (w := (source a).width) (h := (source a).height) (rounds a)) ≤
      (holes (source a).initial).card
  first_height : ∀ a, (source a).height ≤ ((requests a).map Prod.snd).sum
  target_x : ∀ a, (source a).target.1.val + 1 = (source a).width
  target_y : ∀ a, (source a).target.2.val + 1 = (source a).height

namespace SourceFamily

variable {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
  (F : SourceFamily α enc shapes)

/-- The literal first southern vector obtained by summing its actual sparse source requests. -/
def firstQuotas (a : α) : List ℕ := Scan.denseQuotas .south (F.source a).width (F.source a).height (F.requests a)

theorem firstQuotas_length (a : α) : (F.firstQuotas a).length = (F.source a).width :=
  Scan.denseQuotas_length ..

theorem firstQuotas_sum (a : α) : (F.firstQuotas a).sum = ((F.requests a).map Prod.snd).sum :=
  Scan.denseQuotas_sum _ _ _ _ (F.requests_bounded a)

theorem firstQuotas_budget (a : α) : (F.firstQuotas a).sum ≤ (holes (F.source a).initial).card := by
  rw [F.firstQuotas_sum a]
  have h := F.budget a
  omega

@[fun_prop] theorem firstQuotas_polyTime :
    ComputableInPolyTime F.firstQuotas enc (encList encUnary) := by
  have hw := PushFS.Machine.width_polyTime.comp (Push.Machine.toStorage_polyTime.comp F.source_polyTime)
  have hh := PushFS.Machine.height_polyTime.comp (Push.Machine.toStorage_polyTime.comp F.source_polyTime)
  exact (Scan.denseQuotas_polyTime .south).comp (hw.prod (hh.prod F.requests_polyTime))

/-- The real source board and dense first vector form one literal reader input. -/
def reader (a : α) : ColumnScan.Input :=
  ColumnScan.Input.ofInstance (F.source a) (F.firstQuotas a) (F.firstQuotas_length a) (F.firstQuotas_budget a)

/-- Pad only the fixed continuation, preserving all original instructions and actual quota bounds. -/
def prepare : Family α enc (CyclicSchedule.padShapesFrom .west ((true, .west) :: shapes)) where
  reader := F.reader
  rounds a := CyclicSchedule.padFrom .west (F.rounds a)
  reader_polyTime := ColumnScan.Input.ofInstance_polyTime F.source_polyTime F.firstQuotas_polyTime
    F.firstQuotas_length F.firstQuotas_budget
  rounds_polyTime := CyclicSchedule.padFrom_polyTime .west _ F.rounds_polyTime F.shapes_eq
  shapes_eq a := by rw [CyclicSchedule.padFrom_shapes, F.shapes_eq a]
  bounded a i hi := by
    rw [CyclicSchedule.padFrom_instructions] at hi
    exact (Cyclic.sourceBounded_iff_bounded (F.reader a) i).mpr (F.rounds_bounded a i hi)
  budget a := by
    change (F.firstQuotas a).sum + Scan.quota
      (instructions (w := (F.source a).width) (h := (F.source a).height)
        (CyclicSchedule.padFrom .west (F.rounds a))) ≤ (holes (F.source a).initial).card
    rw [CyclicSchedule.padFrom_instructions, F.firstQuotas_sum a]
    exact F.budget a
  extra_zero _ := rfl
  erase_ready a _ := by
    change (F.source a).height ≤ (F.firstQuotas a).sum
    rw [F.firstQuotas_sum a]
    exact F.first_height a

/-- A complete source computation reaches its actual southeast target and pays the exact original program. -/
def Language (a : α) : Prop :=
  ∃ s : State (F.source a).width (F.source a).height,
    Reachable (F.source a).board none (F.source a).initial s ∧ s.player = (F.source a).target ∧
      Scan.Accepts (Scan.lines .south (F.requests a) ++ instructions (F.rounds a)) (holes s)

private theorem accepts_prepare_iff (a : α) (E : Finset (Cell (F.source a).width (F.source a).height)) :
    Scan.Accepts (Scan.columns (Scan.ofQuotas (F.firstQuotas a)) ++
      instructions (CyclicSchedule.padFrom .west (F.rounds a))) E ↔
      Scan.Accepts (Scan.lines .south (F.requests a) ++ instructions (F.rounds a)) E := by
  rw [CyclicSchedule.padFrom_instructions]
  simp only [Scan.Accepts, Scan.eval_append, Scan.columns,
    Scan.eval_normalize .south (F.source a).width (F.source a).height (F.requests a) (F.requests_bounded a),
    firstQuotas]

/-- Preparing the source family preserves the same complete original source computation language. -/
private theorem prepare_language_iff (a : α) :
    Cyclic.Language (F.prepare.reader a) (F.prepare.rounds a) ↔ F.Language a := by
  have hi : (F.reader a).initial.toState = (F.source a).initial := ColumnScan.Input.ofInstance_initial ..
  have hc : (F.reader a).sourceCorner = (F.source a).target :=
    ColumnScan.Input.ofInstance_corner _ _ _ _ (F.target_x a) (F.target_y a)
  constructor
  · rintro ⟨s, hr, hp, ha⟩
    have hreach : Reachable (F.source a).board none (F.reader a).initial.toState s := hr.reboard rfl
    rw [hi] at hreach
    exact ⟨s, hreach, hp.trans hc, (F.accepts_prepare_iff a _).mp ha⟩
  · rintro ⟨s, hr, hp, ha⟩
    have hreach := hr.reboard (B' := (F.reader a).sourceBoard) rfl
    rw [← hi] at hreach
    exact ⟨s, hreach, hp.trans hc.symm, (F.accepts_prepare_iff a _).mpr ha⟩

/-- The actual computed source program has one standard polynomial-time ordinary Push-* point compiler. -/
theorem compile {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
    (F : SourceFamily α enc shapes) :
    ∃ compile : α → Push.Instance, ComputableInPolyTime compile enc Push.encoding ∧
      ∀ a, (compile a).Solvable ↔ F.Language a := by
  obtain ⟨compile, hpt, hcorrect⟩ := compile_family
    (CyclicSchedule.padShapesFrom .west ((true, .west) :: shapes))
    (CyclicSchedule.padShapesFrom_aligned .west _) rfl F.prepare
  exact ⟨compile, hpt, fun a => (hcorrect a).trans (F.prepare_language_iff a)⟩

end SourceFamily
end PushPuzzle.Push.CyclicReader
