/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderFamilyNormal
public import Push.CyclicReaderFamilyErase

/-! Fixed-round read/clear source families reduce to ordinary player-target Push-* by actual physical compilation. -/

public section
namespace PushPuzzle.Push.CyclicReader

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM

/-- The first future block, when present, is an ordinary read. -/
@[expose] def FirstRead : List (Bool × Direction) → Prop
  | [] => True
  | shape :: _ => shape.1 = true

private theorem compile_family_of_potential {α : Type} {enc : α ↪ List Bool} (n : ℕ) :
    ∀ (shapes : List (Bool × Direction)), CyclicSchedule.potential shapes = n →
      CyclicSchedule.Aligned .west shapes → FirstRead shapes →
      ∀ F : Family α enc shapes, ∃ compile : α → Push.Instance,
        ComputableInPolyTime compile enc Push.encoding ∧
          ∀ a, (compile a).Solvable ↔ Cyclic.Language (F.reader a) (F.rounds a) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro shapes hp halign hfirst F
    cases shapes with
    | nil =>
      refine ⟨fun a => (F.reader a).compile, Cyclic.reader_base_nil_polyTime F.reader_polyTime, ?_⟩
      intro a
      have hr : F.rounds a = [] := List.map_eq_nil_iff.mp (F.shapes_eq a)
      rw [hr]
      exact Cyclic.compile_solvable_iff_language_nil _
    | cons shape shapes =>
      rcases shape with ⟨tag, side⟩
      have htag : tag = true := hfirst
      have hside : side = .west := halign.1
      subst tag side
      cases shapes with
      | nil =>
        refine ⟨fun a => (Cyclic.nextInput (F.reader a) (Cyclic.rowQuotas (F.reader a) (F.requests a))
          (Cyclic.rowQuotas_length _ _) (F.requests_budget a)).compile,
          Cyclic.reader_base_west_polyTime F.reader_polyTime F.requests_polyTime F.requests_budget, ?_⟩
        intro a
        have ht : F.remaining a = [] := List.map_eq_nil_iff.mp (F.read_decomposition a).2
        have hr := (F.read_decomposition a).1
        rw [ht] at hr
        rw [hr]
        exact Cyclic.twoRound_solvable_iff_language_west _ _ (F.requests_bounded a) _
      | cons shape shapes =>
        rcases shape with ⟨tag, side⟩
        have hside : side = .north := halign.2.1
        subst side
        cases tag with
        | true =>
          have hdecrease : CyclicSchedule.potential
              (CyclicSchedule.normalSuffix ((true, .west) :: (true, .north) :: shapes)) < n := by
            rw [← hp]
            exact CyclicSchedule.normalSuffix_decreases _ _
          obtain ⟨compile, hpt, hcorrect⟩ := ih _ hdecrease _ rfl
            (CyclicSchedule.normalSuffix_aligned _ halign) rfl F.normal
          exact ⟨compile, hpt, fun a => (hcorrect a).trans (F.normal_language_iff a)⟩
        | false =>
          have hdecrease : CyclicSchedule.potential (CyclicSchedule.eraseSuffix shapes) < n := by
            rw [← hp]
            exact CyclicSchedule.eraseSuffix_decreases _
          obtain ⟨compile, hpt, hcorrect⟩ := ih _ hdecrease _ rfl
            (CyclicSchedule.eraseSuffix_aligned _ halign) rfl F.erase
          exact ⟨compile, hpt, fun a => (hcorrect a).trans (F.erase_language_iff a)⟩

/-- Every actual polynomial-time family with a fixed finite cyclic read/clear skeleton has a standard PT point compiler. -/
theorem compile_family {α : Type} {enc : α ↪ List Bool} (shapes : List (Bool × Direction))
    (halign : CyclicSchedule.Aligned .west shapes) (hfirst : FirstRead shapes)
    (F : Family α enc shapes) :
    ∃ compile : α → Push.Instance, ComputableInPolyTime compile enc Push.encoding ∧
      ∀ a, (compile a).Solvable ↔ Cyclic.Language (F.reader a) (F.rounds a) :=
  compile_family_of_potential _ shapes rfl halign hfirst F

end PushPuzzle.Push.CyclicReader
