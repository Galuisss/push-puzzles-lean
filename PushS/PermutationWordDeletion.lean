/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Foundations.GroupTheory.Perm.ListSplice
public import CslibFrontier.Foundations.GroupTheory.Perm.InsertTwo

/-! Removing an actual point from a directed cyclic word retains the exact remaining word order. -/

public section
namespace PushPuzzle.List


open _root_.List

open Equiv

private theorem formPerm_map_apply {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (word : List α) (point : α) :
    (word.map f).formPerm (f point) = f (word.formPerm point) := by
  induction word using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp
  | cons_cons a b word _ ih =>
    simp only [List.map_cons, List.formPerm_cons_cons, Equiv.Perm.mul_apply]
    have h := ih b
    simp only [List.map_cons] at h
    rw [h]
    exact hf.swap_apply a b _

/-- Include a whole directed word in the retained option points without changing its permutation. -/
theorem formPerm_map_some {α : Type} [DecidableEq α] (word : List α) :
    (word.map some).formPerm = word.formPerm.optionCongr := by
  apply Equiv.ext
  intro point
  cases point with
  | none => exact List.formPerm_apply_of_notMem (by simp)
  | some point => exact formPerm_map_apply some (Option.some_injective _) word point

/-- Changing all directed word coordinates gives the same actual conjugate permutation. -/
theorem formPerm_map_equiv {α β : Type} [DecidableEq α] [DecidableEq β] (word : List α) (e : α ≃ β) :
    (word.map e).formPerm = e.permCongr word.formPerm := by
  apply Equiv.ext
  intro point
  obtain ⟨point, rfl⟩ := e.surjective point
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact formPerm_map_apply e e.injective word point

private theorem removeNone_formPerm_append {α : Type} [DecidableEq α] (word : List α) :
    Equiv.removeNone ((word.map some ++ [none]).formPerm) = word.formPerm := by
  cases word with
  | nil =>
    apply Equiv.ext
    intro point
    simp [Equiv.removeNone, Equiv.removeNoneAux]
  | cons point word =>
    have hnot : ((point :: word).map some).getLast (by simp) ∉ [none] := by
      rw [List.getLast_map]
      simp
    rw [List.formPerm_append_of_last_notMem _ _ (by simp) (by simp) hnot,
      List.formPerm_singleton, mul_one, formPerm_map_some]
    simp only [List.getLast_map]
    exact Equiv.Perm.Insertion.removeNone_insertAfter _ _

private theorem option_word_eq_map {α : Type} (word : List (Option α)) (hn : none ∉ word) :
    word = (word.filterMap id).map some := by
  induction word with
  | nil => rfl
  | cons head word ih =>
    have htail : none ∉ word := fun h => hn (List.mem_cons_of_mem _ h)
    cases head with
    | none => exact False.elim (hn (by simp))
    | some head => simpa only [List.filterMap_cons, id_eq, List.map_cons] using congrArg (some head :: ·) (ih htail)

/-- Deleting one point from a genuine directed cycle preserves exactly its remaining literal word. -/
theorem removeNone_formPerm {α : Type} [DecidableEq α] (word : List (Option α)) (hn : word.Nodup) :
    Equiv.removeNone word.formPerm = (word.filterMap id).formPerm := by
  have hfiltered : (word.filterMap id).Nodup := List.Nodup.filterMap
    (fun _ _ _ ha hb => (Option.mem_def.mp ha).trans (Option.mem_def.mp hb).symm) hn
  by_cases hm : none ∈ word
  · obtain ⟨left, right, rfl⟩ := List.append_of_mem hm
    have hrot : (left ++ none :: right) ~r ((right ++ left) ++ [none]) := by
      have h := List.isRotated_append (l := left ++ [none]) (l' := right)
      rw [List.append_assoc, List.singleton_append] at h
      simpa only [List.append_assoc] using h
    have hperm := List.formPerm_eq_of_isRotated hn hrot
    have hrotN := hrot.perm.nodup_iff.mp hn
    have hnone : none ∉ right ++ left := by
      intro h
      exact List.disjoint_left.mp (List.nodup_append'.mp hrotN).2.2 h (by simp)
    have hfree := option_word_eq_map (right ++ left) hnone
    have hfilterRot : ((left ++ none :: right).filterMap id) ~r ((right ++ left).filterMap id) := by
      simpa only [List.filterMap_append, List.filterMap_cons, id_eq] using
        List.isRotated_append (l := left.filterMap id) (l' := right.filterMap id)
    calc
      _ = Equiv.removeNone (((right ++ left) ++ [none]).formPerm) := congrArg Equiv.removeNone hperm
      _ = Equiv.removeNone ((((right ++ left).filterMap id).map some ++ [none]).formPerm) := by rw [← hfree]
      _ = ((right ++ left).filterMap id).formPerm := removeNone_formPerm_append _
      _ = _ := (List.formPerm_eq_of_isRotated hfiltered hfilterRot).symm
  · have hfree := option_word_eq_map word hm
    calc
      _ = Equiv.removeNone (((word.filterMap id).map some).formPerm) := by rw [← hfree]
      _ = (word.filterMap id).formPerm := by
        rw [formPerm_map_some]
        apply Equiv.ext
        intro point
        simp [Equiv.removeNone, Equiv.removeNoneAux]

/-- Deleting two actual points retains the exact twice-filtered directed source word. -/
theorem removeNone_twice_formPerm {α : Type} [DecidableEq α] (word : List (Option (Option α))) (hn : word.Nodup) :
    Equiv.removeNone (Equiv.removeNone word.formPerm) = ((word.filterMap id).filterMap id).formPerm := by
  rw [removeNone_formPerm word hn]
  exact removeNone_formPerm _ (List.Nodup.filterMap
    (fun _ _ _ ha hb => (Option.mem_def.mp ha).trans (Option.mem_def.mp hb).symm) hn)

end PushPuzzle.List
