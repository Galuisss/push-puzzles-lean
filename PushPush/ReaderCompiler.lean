/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.BlockLanguage
public import PushPush.BlockPeeling

/-! Standard polynomial-time compilation along a finite cyclic list of read blocks. -/

@[expose] public section
namespace PushPuzzle.PushPush.CyclicReader

open PushFS (Direction)
open Push.AcceptanceProgram Push.CyclicReader
open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

private theorem compile_family_induction
    (semantics : Push.ColumnScan.Input → List Round → Prop)
    (base : ∀ r, PushPush.Instance.Solvable r.compile ↔ semantics r [])
    (peel : ∀ shapes (F : Family α enc ((true, .west) :: shapes)) a,
      semantics ((advance F).reader a) ((advance F).rounds a) ↔ semantics (F.reader a) (F.rounds a))
    (n : ℕ) : ∀ (shapes : List (Bool × Direction)), shapes.length = n →
      Push.CyclicSchedule.Aligned .west shapes → (∀ shape ∈ shapes, shape.1 = true) →
      ∀ F : Family α enc shapes, ∃ compile : α → Push.Instance,
        ComputableInPolyTime compile enc Push.encoding ∧
          ∀ a, PushPush.Instance.Solvable (compile a) ↔ semantics (F.reader a) (F.rounds a) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro shapes hn halign hreads F
    cases shapes with
    | nil =>
      refine ⟨fun a => (F.reader a).compile, Push.Cyclic.reader_base_nil_polyTime F.reader_polyTime, ?_⟩
      intro a
      have hr : F.rounds a = [] := List.map_eq_nil_iff.mp (F.shapes_eq a)
      rw [hr]
      exact base _
    | cons shape shapes =>
      rcases shape with ⟨tag, side⟩
      have ht : tag = true := hreads _ (List.mem_cons_self ..)
      have hs : side = .west := halign.1
      subst tag side
      have hdec : (Push.CyclicSchedule.turnShapes shapes).length < n := by
        rw [Push.CyclicSchedule.turnShapes_length]
        change shapes.length + 1 = n at hn
        omega
      have ha : Push.CyclicSchedule.Aligned .west (Push.CyclicSchedule.turnShapes shapes) :=
        Push.CyclicSchedule.normalSuffix_aligned shapes halign
      have ht : ∀ shape ∈ Push.CyclicSchedule.turnShapes shapes, shape.1 = true := by
        intro shape hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        exact hreads old (List.mem_cons_of_mem _ hold)
      obtain ⟨compile, hpt, hcorrect⟩ := ih _ hdec _ rfl ha ht (advance F)
      exact ⟨compile, hpt, fun a => (hcorrect a).trans (peel shapes F a)⟩

private theorem advance_language_iff {shapes : List (Bool × Direction)}
    (F : Family α enc ((true, .west) :: shapes)) (a : α) :
    Language ((advance F).reader a) ((advance F).rounds a) ↔ Language (F.reader a) (F.rounds a) := by
  have h := next_language_iff (F.reader a) (F.requests a) (F.requests_budget a)
    (F.remaining a) (F.remaining_bounded a)
  rw [← (F.read_decomposition a).1] at h
  exact h

/-- A fixed finite cyclic family of read blocks has a standard maximum-game point compiler. -/
theorem compile_family (shapes : List (Bool × Direction))
    (halign : Push.CyclicSchedule.Aligned .west shapes)
    (hreads : ∀ shape ∈ shapes, shape.1 = true) (F : Family α enc shapes) :
    ∃ compile : α → PushPush.Instance, ComputableInPolyTime compile enc PushPush.encoding ∧
      ∀ a, PushPush.Instance.Solvable (compile a) ↔ Language (F.reader a) (F.rounds a) :=
  compile_family_induction Language compile_nil_iff
    (fun _ F a => advance_language_iff F a) shapes.length shapes rfl halign hreads F

/-- Compile an actual source game with its entire literal cyclic whole-round program. -/
theorem compile_source_family {shapes : List (Bool × Direction)}
    (F : SourceFamily α enc shapes)
    (halign : Push.CyclicSchedule.Aligned .west ((true, .west) :: shapes))
    (hreads : ∀ shape ∈ (true, .west) :: shapes, shape.1 = true) :
    ∃ compile : α → PushPush.Instance, ComputableInPolyTime compile enc PushPush.encoding ∧
      ∀ a, PushPush.Instance.Solvable (compile a) ↔ SourceLanguage F a := by
  obtain ⟨compile, hpt, hcorrect⟩ := compile_family _ halign hreads (direct F)
  exact ⟨compile, hpt, fun a => (hcorrect a).trans (direct_language_iff F a)⟩

end PushPuzzle.PushPush.CyclicReader
