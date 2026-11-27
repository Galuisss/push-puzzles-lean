/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Foundations.Geometry.Polygonal.Join
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Consecutive indexed pieces of the existing polygonal route retain their actual parameters. -/

public section
namespace PushPuzzle.Polygonal.Route

open Cslib

open Cslib.Polygonal Cslib.Polygonal.Route


/-- Retain exactly the original consecutive listed points from `first` through `last`. -/
@[expose] def subroute (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last) : Route where
  bends := last.val - first.val - 1
  point i := p.point ⟨first.val + i.val, by have := first.isLt; have := last.isLt; have := i.isLt; omega⟩

/-- The number of retained segments is the difference of the two actual node positions. -/
theorem segments_subroute (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last) :
    ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments = last.val - first.val := by
  dsimp only [subroute, segments]
  have h : first.val < last.val := hlt
  omega

/-- The selected source nodes are the literal endpoints of the consecutive piece. -/
theorem endpoint_subroute (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last) (side : Bool) :
    ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).endpoint side = p.point (if side then last else first) := by
  cases side
  · change p.point ⟨first.val + 0, _⟩ = p.point first
    rfl
  · change p.point ⟨first.val + (((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments), _⟩ = p.point last
    apply congrArg p.point
    apply Fin.ext
    change first.val + ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments = last.val
    have hi : first.val < last.val := hlt
    have hlen := segments_subroute p first last hlt
    omega

/-- Every piece segment retains its exact original source segment index. -/
@[expose] def subrouteIndex (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last)
    (i : Fin ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments) : Fin p.segments :=
  ⟨first.val + i.val, by
    have hi := i.isLt
    have hlen := segments_subroute p first last hlt
    have hlast := last.isLt
    have h : first.val < last.val := hlt
    dsimp only [segments]
    omega⟩

/-- Evaluation on a retained segment is literally evaluation on that source segment. -/
theorem eval_subroute (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last)
    (i : Fin ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments) (t : ℝ) :
    ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).eval i t = p.eval ((PushPuzzle.Polygonal.Route.subrouteIndex p) first last hlt i) t := rfl

/-- Piece positions differ from their original route positions by the fixed first-node offset. -/
theorem position_subroute (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last)
    (i : Fin ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments) (t : ℝ) :
    p.position ((PushPuzzle.Polygonal.Route.subrouteIndex p) first last hlt i) t =
      (first.val : ℝ) + ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).position i t := by
  simp only [position, subrouteIndex, Nat.cast_add, add_assoc]

/-- Every point of the exact consecutive piece remains on the original polygonal route. -/
theorem support_subroute_subset (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last) :
    ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).support ⊆ p.support := by
  intro z hz
  obtain ⟨i, t, ht, rfl⟩ := (((PushPuzzle.Polygonal.Route.subroute p) first last hlt).mem_support_iff z).mp hz
  rw [eval_subroute]
  exact p.at_mem_support _ ht

/-- A retained parameter at an original endpoint is at the matching endpoint of its piece. -/
theorem atEnd_subroute_of_source (p : Route) (first last : Fin (p.bends + 2)) (hlt : first < last)
    (i : Fin ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments) (t : ℝ) (ht : t ∈ Set.Icc 0 1) (side : Bool)
    (he : p.AtEnd ((PushPuzzle.Polygonal.Route.subrouteIndex p) first last hlt i) t side) :
    ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).AtEnd i t side := by
  have hb := ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).position_mem i ht
  have hfirst : (0 : ℝ) ≤ first.val := Nat.cast_nonneg _
  have hlast : (last.val : ℝ) ≤ p.segments := by exact_mod_cast Nat.le_sub_one_of_lt last.isLt
  have hlen : (((PushPuzzle.Polygonal.Route.subroute p) first last hlt).segments : ℝ) = (last.val : ℝ) - first.val := by
    rw [segments_subroute, Nat.cast_sub (Nat.le_of_lt hlt)]
  cases side <;> simp only [AtEnd, Bool.false_eq_true, ite_false, ite_true] at he ⊢ <;>
    rw [position_subroute] at he <;> linarith [hb.1, hb.2]

/-- Consecutive indexed pieces of a simple source route are themselves simple. -/
theorem IsSimple.subroute {p : Route} (hp : p.IsSimple)
    (first last : Fin (p.bends + 2)) (hlt : first < last) : ((PushPuzzle.Polygonal.Route.subroute p) first last hlt).IsSimple := by
  intro i j s t hs ht he
  rw [eval_subroute, eval_subroute] at he
  rcases hp _ _ s t hs ht he with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    rw [position_subroute, position_subroute] at h
    linarith
  · right; left
    exact ⟨(PushPuzzle.Polygonal.Route.atEnd_subroute_of_source p) first last hlt i s hs false ha,
      (PushPuzzle.Polygonal.Route.atEnd_subroute_of_source p) first last hlt j t ht true hb⟩
  · right; right
    exact ⟨(PushPuzzle.Polygonal.Route.atEnd_subroute_of_source p) first last hlt i s hs true ha,
      (PushPuzzle.Polygonal.Route.atEnd_subroute_of_source p) first last hlt j t ht false hb⟩

/-- Ordered pieces of an open simple source route meet only at their shared boundary node. -/
theorem IsSimple.subroute_contact {p : Route} (hp : p.IsSimple) (hne : p.start ≠ p.finish)
    (a b c d : Fin (p.bends + 2)) (hab : a < b) (hcd : c < d) (hbc : b ≤ c)
    (i : Fin ((PushPuzzle.Polygonal.Route.subroute p) a b hab).segments) (j : Fin ((PushPuzzle.Polygonal.Route.subroute p) c d hcd).segments)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : ((PushPuzzle.Polygonal.Route.subroute p) a b hab).eval i s = ((PushPuzzle.Polygonal.Route.subroute p) c d hcd).eval j t) :
    b = c ∧ ((PushPuzzle.Polygonal.Route.subroute p) a b hab).AtEnd i s true ∧ ((PushPuzzle.Polygonal.Route.subroute p) c d hcd).AtEnd j t false := by
  rw [eval_subroute, eval_subroute] at he
  have hpos := hp.position_eq_of_eval_eq hne _ _ hs ht he
  rw [position_subroute, position_subroute] at hpos
  have his := ((PushPuzzle.Polygonal.Route.subroute p) a b hab).position_mem i hs
  have hjt := ((PushPuzzle.Polygonal.Route.subroute p) c d hcd).position_mem j ht
  have hl : (((PushPuzzle.Polygonal.Route.subroute p) a b hab).segments : ℝ) = (b.val : ℝ) - a.val := by
    rw [segments_subroute, Nat.cast_sub (Nat.le_of_lt hab)]
  have hle : (b.val : ℝ) ≤ c.val := by exact_mod_cast hbc
  have hbeq : b = c := by
    apply Fin.ext
    have heq : (b.val : ℝ) = c.val := by linarith [his.2, hjt.1]
    exact_mod_cast heq
  refine ⟨hbeq, ?_, ?_⟩
  · simp only [AtEnd, ite_true]
    have hbval := congrArg Fin.val hbeq
    linarith [his.2, hjt.1]
  · simp only [AtEnd, Bool.false_eq_true, ite_false]
    have hbval := congrArg Fin.val hbeq
    linarith [his.2, hjt.1]

private theorem node_sample (p : Route) (k : Fin (p.bends + 2)) :
    ∃ (i : Fin p.segments) (t : ℝ), t ∈ Set.Icc 0 1 ∧ p.eval i t = p.point k ∧ p.position i t = k.val := by
  induction k using Fin.lastCases with
  | last =>
    refine ⟨Fin.last p.bends, 1, ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
    · simp only [eval, AffineMap.lineMap_apply_one, Fin.succ_last]
    · simp only [position, Fin.val_last, segments, Nat.cast_add, Nat.cast_one]
  | cast k =>
    refine ⟨k, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · simp only [eval, AffineMap.lineMap_apply_zero]
    · simp only [position, add_zero, Fin.val_castSucc]

/-- The listed node coordinates of an open simple route uniquely identify their actual indices. -/
theorem IsSimple.point_injective {p : Route} (hp : p.IsSimple) (hne : p.start ≠ p.finish) :
    Function.Injective p.point := by
  intro i j he
  obtain ⟨a, s, hs, has, hpa⟩ := node_sample p i
  obtain ⟨b, t, ht, hbt, hpb⟩ := node_sample p j
  have hpos := hp.position_eq_of_eval_eq hne a b hs ht (has.trans (he.trans hbt.symm))
  rw [hpa, hpb] at hpos
  apply Fin.ext
  exact_mod_cast hpos

/-- A route fragment between consecutive listed cuts meets a listed cut only at its own ends. -/
theorem IsSimple.subroute_cut_contact {p : Route} (hp : p.IsSimple) (hne : p.start ≠ p.finish)
    {n : ℕ} (cuts : Fin (n + 2) → Fin (p.bends + 2)) (hm : StrictMono cuts)
    (piece : Fin (n + 1)) (cut : Fin (n + 2))
    (i : Fin ((PushPuzzle.Polygonal.Route.subroute p) (cuts piece.castSucc) (cuts piece.succ) (hm Fin.castSucc_lt_succ)).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : ((PushPuzzle.Polygonal.Route.subroute p) (cuts piece.castSucc) (cuts piece.succ) (hm Fin.castSucc_lt_succ)).eval i t =
      p.point (cuts cut)) :
    ∃ side, ((PushPuzzle.Polygonal.Route.subroute p) (cuts piece.castSucc) (cuts piece.succ) (hm Fin.castSucc_lt_succ)).AtEnd i t side ∧
      cut = if side then piece.succ else piece.castSucc := by
  obtain ⟨j, s, hs, hj, hpos⟩ := node_sample p (cuts cut)
  rw [eval_subroute] at he
  have heq := hp.position_eq_of_eval_eq hne _ j ht hs (he.trans hj.symm)
  rw [position_subroute, hpos] at heq
  have hb := ((PushPuzzle.Polygonal.Route.subroute p) (cuts piece.castSucc) (cuts piece.succ) (hm Fin.castSucc_lt_succ)).position_mem i ht
  have hlen : (((PushPuzzle.Polygonal.Route.subroute p) (cuts piece.castSucc) (cuts piece.succ) (hm Fin.castSucc_lt_succ)).segments : ℝ) =
      ((cuts piece.succ).val : ℝ) - (cuts piece.castSucc).val := by
    rw [segments_subroute, Nat.cast_sub (Nat.le_of_lt (hm Fin.castSucc_lt_succ))]
  have hlo : cuts piece.castSucc ≤ cuts cut := by
    change (cuts piece.castSucc).val ≤ (cuts cut).val
    exact_mod_cast (show ((cuts piece.castSucc).val : ℝ) ≤ (cuts cut).val by linarith [hb.1])
  have hhi : cuts cut ≤ cuts piece.succ := by
    change (cuts cut).val ≤ (cuts piece.succ).val
    exact_mod_cast (show ((cuts cut).val : ℝ) ≤ (cuts piece.succ).val by linarith [hb.2])
  have hklo := hm.le_iff_le.mp hlo
  have hkhi := hm.le_iff_le.mp hhi
  have hk : cut = piece.castSucc ∨ cut = piece.succ := by
    apply or_iff_not_imp_left.mpr
    intro hne
    apply Fin.ext
    have hne' : cut.val ≠ piece.val := fun h => hne (Fin.ext h)
    change piece.val ≤ cut.val at hklo
    change cut.val ≤ piece.val + 1 at hkhi
    change cut.val = piece.val + 1
    omega
  rcases hk with rfl | rfl
  · refine ⟨false, ?_, rfl⟩
    change _ = 0
    linarith
  · refine ⟨true, ?_, rfl⟩
    simp only [AtEnd, ite_true]
    linarith

end PushPuzzle.Polygonal.Route
