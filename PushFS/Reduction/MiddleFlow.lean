/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.TranslateFlow

/-! Each actual source-star arm and middle-band bypass is a complete directed unit path. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

private theorem gridStar_unitFlow {a b : ℕ} (e : Fin a ⊕ Fin b) :
    UnitFlow (segments (GridStar.path e))
      (e.elim (fun i=>(i.val,0)) (fun _=>(GridStar.center a,1)))
      (e.elim (fun _=>(GridStar.center a,1)) (fun j=>(j.val,2))) := by
  cases e with
  | inl i =>
    change UnitFlow ([⟨(i.val,0),(i.val,1)⟩]++[⟨(i.val,1),(GridStar.center a,1)⟩]) _ _
    apply UnitFlow.append (Segment.unitFlow _ (Or.inl rfl)) (Segment.unitFlow _ (Or.inr rfl))
    intro p hp hq
    rw [hasPoint_singleton] at hp hq
    have hpB := Segment.coordinate_bounds hp
    have hqB := Segment.coordinate_bounds hq
    simp only [Nat.min_self,Nat.max_self] at hpB hqB
    apply Prod.ext <;> dsimp only at hpB hqB ⊢ <;> omega
  | inr j =>
    change UnitFlow ([⟨(GridStar.center a,1),(j.val,1)⟩]++[⟨(j.val,1),(j.val,2)⟩]) _ _
    apply UnitFlow.append (Segment.unitFlow _ (Or.inr rfl)) (Segment.unitFlow _ (Or.inl rfl))
    intro p hp hq
    rw [hasPoint_singleton] at hp hq
    have hpB := Segment.coordinate_bounds hp
    have hqB := Segment.coordinate_bounds hq
    simp only [Nat.min_self,Nat.max_self] at hpB hqB
    apply Prod.ext <;> dsimp only at hpB hqB ⊢ <;> omega

private theorem middle_unitFlow {k a b r : ℕ} (e : GridLayout.Strand k a b r) :
    UnitFlow (segments (GridLayout.middlePath e)) (GridLayout.middleStart e) (GridLayout.middleEnd e) := by
  rcases e with i | ((i | j) | j)
  · exact Segment.unitFlow ⟨(4*i.val,0),(4*i.val,2)⟩ (Or.inl rfl)
  · change UnitFlow (segments ((GridStar.path (Sum.inl i : Fin a ⊕ Fin b)).translate (4*k) 0))
      (i.val+4*k,0) (GridStar.center a+4*k,1)
    rw [segments_translate]
    simpa only [Sum.elim_inl,Nat.add_zero] using
      (gridStar_unitFlow (Sum.inl i : Fin a ⊕ Fin b)).translate (4*k) 0
  · change UnitFlow (segments ((GridStar.path (Sum.inr j : Fin a ⊕ Fin b)).translate (4*k) 0))
      (GridStar.center a+4*k,1) (j.val+4*k,2)
    rw [segments_translate]
    simpa only [Sum.elim_inr,Nat.add_zero] using
      (gridStar_unitFlow (Sum.inr j : Fin a ⊕ Fin b)).translate (4*k) 0
  · exact Segment.unitFlow ⟨(4*k+4+4*j.val,0),(4*k+4+4*j.val,2)⟩ (Or.inl rfl)

/-- Any middle strand that actually starts at the top cut has only its own endpoint on that row. -/
theorem middle_top_unique {k a b r : ℕ} (e : GridLayout.Strand k a b r)
    (hy : (GridLayout.middleStart e).2=0) {p : GridRouting.Point}
    (hp : HasPoint (segments (GridLayout.middlePath e)) p) (hpY : p.2=0) : p=GridLayout.middleStart e := by
  have hp' := (GridLayout.middlePath_contains_iff e p).mp ((mem_segments_iff _ _).mp hp)
  rcases e with i | ((i | j) | j)
  all_goals
    simp only [GridLayout.middleStart,GridLayout.MiddleContains,GridStar.Contains] at hy hp' ⊢
    apply Prod.ext <;> dsimp only at hy hp' ⊢ <;> omega

namespace Plan

/-- The exact serialized middle fragments selected by the actual numbered source compiler have the unit-path contract. -/
theorem Layer.strand_unitFlow (l : Layer) (e : l.Strand) :
    UnitFlow (l.strandRoute e).path
      ((GridLayout.middleStart e).1,(GridLayout.middleStart e).2+l.middleY)
      ((GridLayout.middleEnd e).1,(GridLayout.middleEnd e).2+l.middleY) := by
  rw [l.strandRoute_path]
  simpa only [Layer.strandPath,segments_translate,Nat.add_zero] using
    (middle_unitFlow e).translate 0 l.middleY

end Plan
end PushPuzzle.PushFS.Reduction
