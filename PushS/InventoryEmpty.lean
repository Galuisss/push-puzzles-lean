/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Inventory

/-! A region with nondecreasing box inventory is empty along any suffix ending empty. -/

public section

namespace PushPuzzle.PushS.Inventory


open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h} {R : Finset (Cell w h)}

private theorem forwardStep_of_mono (hm : Step B cap s t) (hmono : count R s ≤ count R t) :
    ForwardStep B cap R s t := by
  refine ⟨hm, ?_⟩
  intro d n run hn _ hb hfirst
  by_contra hlast
  have hc := push_accounting (R := R) run hn hb
  simp only [hfirst, hlast, ite_true, ite_false] at hc
  omega

/-- A real move is forward for the region when its possible pushes never export a first box.
Only runs in the actual direction and matching the actual target are checked. -/
theorem forwardStep_of_move (hm : Move B cap d s t)
    (hretain : ∀ (n : ℕ) (run : Run B d s n), 0 < n →
      t.player = run.cell 1 →
      t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)) →
      run.cell 1 ∈ R → run.cell ⟨n + 1, by omega⟩ ∈ R) : ForwardStep B cap R s t := by
  apply forwardStep_of_mono ⟨d, hm⟩
  cases hm with
  | walk _ _ _ _ hb => simp only [count, hb, le_rfl]
  | @push n _ hn _ run hp hb =>
    have hc := push_accounting (R := R) run hn hb
    by_cases hfirst : run.cell 1 ∈ R
    · have hlast := hretain n run hn hp hb hfirst
      simp only [hfirst, hlast, ite_true] at hc
      omega
    · simp only [hfirst, ite_false] at hc
      split at hc <;> omega

private theorem count_zero_iff (R : Finset (Cell w h)) (s : State w h) :
    count R s = 0 ↔ Disjoint s.boxes R := by
  simp [count_eq_card, Finset.filter_mem_eq_inter, Finset.disjoint_iff_inter_eq_empty]

/-- If boxes cannot leave a region, emptiness at the end of a suffix forces emptiness at its start. -/
theorem reachable_source_empty (hr : Relation.ReflTransGen (ForwardStep B cap R) s t)
    (ht : Disjoint t.boxes R) : Disjoint s.boxes R := by
  apply (count_zero_iff R s).mp
  have hmono := reachable_mono hr
  have hz := (count_zero_iff R t).mpr ht
  omega

end PushPuzzle.PushS.Inventory
