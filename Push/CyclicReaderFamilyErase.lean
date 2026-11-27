/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderFamilyRead
public import Push.CyclicEraseRoundPolyTime
public import Push.CyclicEraseRoundValid

/-! One actual erase replacement preserves certified fixed-shape polynomial-time reader families. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicReader.Family

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
  (F : Family α enc ((true, .west) :: (false, .north) :: shapes))

/-- The actual raw source columns selected by the impending clear. -/
def lanes (a : α) : Finset ℕ := firstLanes (F.remaining a)

/-- The computed source blocks following the impending clear. -/
def afterClear (a : α) : List Round := (F.remaining a).tail

@[fun_prop] theorem lanes_polyTime : ComputableInPolyTime F.lanes enc encLaneSet :=
  firstLanes_polyTime.comp F.remaining_polyTime

@[fun_prop] theorem afterClear_polyTime : ComputableInPolyTime F.afterClear enc encRounds := by
  have ht := F.remaining_polyTime
  unfold afterClear encRounds
  fun_prop

theorem clear_decomposition (a : α) :
    F.remaining a = .clear .north (F.lanes a) :: F.afterClear a ∧
      (F.afterClear a).map Round.shape = shapes :=
  clear_cons_of_shapes _ _ _ (F.read_decomposition a).2

private theorem lanes_bounded (a : α) : ∀ lane ∈ F.lanes a, lane < (F.reader a).width := by
  have hb := F.remaining_bounded a (.clear .north (F.lanes a))
  apply hb
  rw [(F.clear_decomposition a).1]
  exact List.mem_cons_self ..

theorem afterClear_bounded (a : α) :
    ∀ i ∈ instructions (F.afterClear a), Cyclic.SourceBounded (F.reader a) i := by
  intro i hi
  apply F.remaining_bounded a i
  rw [(F.clear_decomposition a).1]
  exact List.mem_cons_of_mem _ hi

theorem erase_budget (a : α) : Cyclic.Budget (F.reader a)
    (.read .west (F.requests a) :: .clear .north (F.lanes a) :: F.afterClear a) := by
  rw [← (F.clear_decomposition a).1]
  exact F.read_budget a

/-- Prepare real backups and replace the impending clear by the actual six-read cyclic expansion. -/
def erase : Family α enc (CyclicSchedule.eraseSuffix shapes) where
  reader a := CyclicErase.nextInput (F.reader a) (Cyclic.rowQuotas (F.reader a) (F.requests a))
    (Cyclic.rowQuotas_length _ _) (F.requests_budget a)
  rounds a := CyclicErase.suffixRounds (F.reader a) (CyclicErase.selectColumns (F.reader a) (F.lanes a))
    (F.afterClear a)
  reader_polyTime := CyclicErase.nextInput_polyTime F.reader_polyTime
    (Cyclic.rowQuotas_family_polyTime F.reader_polyTime F.requests_polyTime)
    (fun a => Cyclic.rowQuotas_length _ _) F.requests_budget
  rounds_polyTime := CyclicErase.suffixRounds_polyTime F.reader_polyTime F.lanes_polyTime F.afterClear_polyTime
  shapes_eq a := by rw [CyclicErase.suffixRounds_shapes, (F.clear_decomposition a).2]
  bounded a := CyclicErase.suffixRounds_sourceBounded _ _ _ _ _ _ (F.afterClear_bounded a)
  budget a := CyclicErase.round_step_budget _ (F.erase_ready a rfl) _ (F.requests_bounded a)
    _ _ (F.erase_budget a)
  extra_zero _ := rfl
  erase_ready _ h := by simp only [CyclicSchedule.eraseSuffix, List.cons_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, Bool.true_eq_false,
    false_and] at h

/-- The backed transformed family preserves exactly the accepted original source computations. -/
theorem erase_language_iff (a : α) :
    Cyclic.Language (F.erase.reader a) (F.erase.rounds a) ↔ Cyclic.Language (F.reader a) (F.rounds a) := by
  have he := CyclicErase.round_step_language_iff (F.reader a) (F.erase_ready a rfl)
    (F.requests a) (F.requests_bounded a) (F.lanes a) (F.lanes_bounded a) (F.afterClear a)
    (F.afterClear_bounded a) (F.requests_budget a)
  rw [← (F.clear_decomposition a).1, ← (F.read_decomposition a).1] at he
  exact he

end PushPuzzle.Push.CyclicReader.Family
