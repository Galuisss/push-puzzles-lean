/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ReflectedFrontier

/-! Once the player leaves a source rectangle, its remaining holes can only be deleted. -/

public section
namespace PushPuzzle.Push.ReaderResidual

open PushFS PushS ReflectedFrontier

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {d : Direction} {s t : State w h}
  {cut height n : ℕ}

/-- A complete real push removes its first source hole and creates no source hole. -/
theorem source_push (run : Run B d s n) (hn : 0 < n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (ht : t.player.1.val < cut → height ≤ t.player.2.val) :
    source cut height t = (source cut height s).erase (run.cell ⟨n + 1, by omega⟩) := by
  have hfirst : ¬((run.cell 1).1.val < cut ∧ (run.cell 1).2.val < height) := by
    rw [← hp]
    rintro ⟨hx, hy⟩
    have := ht hx
    omega
  simp only [source, holes_push run hn hb, Finset.filter_insert, ite_eq_right hfirst,
    Finset.filter_erase]

/-- An inaccessible source never gains a hole from any walk or complete pushing move. -/
private theorem source_subset (hm : Move B cap d s t)
    (ht : t.player.1.val < cut → height ≤ t.player.2.val) :
    source cut height t ⊆ source cut height s := by
  cases hm with
  | walk _ _ _ _ hb => simp only [source, holes, hb, Finset.Subset.refl]
  | push _ hn _ run hp hb =>
    rw [source_push run hn hp hb ht]
    exact Finset.erase_subset _ _

/-- Every suffix of a source-avoiding physical run has a smaller remaining source hole set. -/
theorem reachable_source_subset
    (hr : Relation.ReflTransGen (fun a b => Step B cap a b ∧
      (b.player.1.val < cut → height ≤ b.player.2.val)) s t) :
    source cut height t ⊆ source cut height s := by
  induction hr with
  | refl => exact Finset.Subset.refl _
  | tail _ hm ih => exact (source_subset hm.1.choose_spec hm.2).trans ih

end PushPuzzle.Push.ReaderResidual
