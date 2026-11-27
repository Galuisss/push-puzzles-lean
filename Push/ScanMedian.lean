/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanEmbedding

/-! Two reads from either end of a five-hole line retain exactly its middle hole. -/

public section
namespace PushPuzzle.Push.Scan

/-- A two-hole read from each end of a five-hole line leaves its third hole and every off-line hole. -/
theorem five_hole_middle {α : Type*} [DecidableEq α] (cells : List α) (E : Finset α)
    (hn : cells.Nodup) (a b c d e : α)
    (hholes : cells.filter (fun q => decide (q ∈ E)) = [a, b, c, d, e]) :
    ((consume cells 2 E).bind (consume cells.reverse 2)) =
      some (insert c (E.filter fun q => q ∉ cells)) := by
  have hmem (q : α) : q ∈ E ∧ q ∈ cells ↔ q ∈ [a, b, c, d, e] := by
    rw [← hholes]
    simp only [List.mem_filter, decide_eq_true_eq, and_comm]
  have hE (q : α) (hq : q ∈ [a, b, c, d, e]) : q ∈ E := ((hmem q).mpr hq).1
  have hdistinct : [a, b, c, d, e].Nodup := hholes ▸ hn.filter _
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hdistinct
  have hab : b ≠ a := by tauto
  have hae : e ≠ a := by tauto
  have hbe : e ≠ b := by tauto
  have had : d ≠ a := by tauto
  have hbd : d ≠ b := by tauto
  have hed : d ≠ e := by tauto
  have hfirst : consume cells 2 E = some ((E.erase a).erase b) := by
    rw [← consume_filter (fun q => decide (q ∈ E)) cells 2 E (by intros; simp_all), hholes]
    have ha := hE a (by simp)
    have hb : b ∈ E.erase a := by simp only [Finset.mem_erase]; exact ⟨hab, hE b (by simp)⟩
    simp only [consume, ite_eq_left ha, ite_eq_left hb]
  have hsecond : consume cells.reverse 2 ((E.erase a).erase b) =
      some ((((E.erase a).erase b).erase e).erase d) := by
    rw [← consume_filter (fun q => decide (q ∈ E)) cells.reverse 2 ((E.erase a).erase b) (by
      intro q _ hq
      exact decide_eq_true ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _) hq)),
      List.filter_reverse, hholes]
    have he : e ∈ (E.erase a).erase b := by
      simp only [Finset.mem_erase]
      exact ⟨hbe, hae, hE e (by simp)⟩
    have hd : d ∈ ((E.erase a).erase b).erase e := by
      simp only [Finset.mem_erase]
      exact ⟨hed, hbd, had, hE d (by simp)⟩
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, consume,
      ite_eq_left he, ite_eq_left hd]
  rw [hfirst, Option.bind_some, hsecond]
  congr 1
  ext q
  have hh := hmem q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_filter]
  have hcE := hE c (by simp)
  have hcL := ((hmem c).mpr (by simp)).2
  by_cases hqc : q = c
  · subst q
    tauto
  · tauto

end PushPuzzle.Push.Scan
