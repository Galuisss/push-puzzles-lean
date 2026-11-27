/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Frontier

/-!
# Local slices of the actual strip sweep

Processing one grid site removes exactly its incoming unit arcs and inserts exactly its outgoing
unit arcs. Higher and lower frontier labels remain in the same order. The local lists are computed
from the actual carrier enumeration.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Slice`: the unchanged prefix/suffix and the two local port lists.
* `PushPuzzle.NCL.Strip.Sweep.slice`: the actual slice at a grid site.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.slice_before`, `PushPuzzle.NCL.Strip.Sweep.slice_after`: exact actual frontier decompositions.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

namespace Arc

open Cslib.Complexity Cslib.Complexity.NCL

/-- A single scan step removes arcs ending at its site and inserts arcs starting there. -/
private theorem active_succ_iff {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) (a : Arc R) :
    Active R (level K p + 1) a ↔
      (Active R (level K p) a ∧ a.upper R ≠ p) ∨ a.lower R = p := by
  have hi := a.level_lt R
  constructor
  · intro ha
    by_cases hl : level K (a.lower R) = level K p
    · exact Or.inr (level_injective (a.band R).1 hp hl)
    · left
      refine ⟨⟨by have := ha.1; omega, by have := ha.2; omega⟩, ?_⟩
      intro he
      have := ha.2
      rw [he] at this
      omega
  · rintro (⟨ha, hu⟩ | hl)
    · have hne : level K (a.upper R) ≠ level K p :=
        fun he => hu (level_injective (a.band R).2 hp he)
      exact ⟨by have := ha.1; omega, by have := ha.2; omega⟩
    · rw [hl] at hi
      exact ⟨by rw [hl]; omega, by omega⟩

private theorem vertical_before {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K)
    (a : Arc R) (ha : Active R (level K p) a)
    (hh : (a.lower R).2 ≠ (a.upper R).2) : a.upper R = p := by
  have hs := (a.shape R).resolve_left (fun h => hh (congrArg Prod.snd h).symm)
  have he : level K (a.upper R) = level K p := by
    simp only [Active, level, hs] at ha ⊢
    omega
  exact level_injective (a.band R).2 hp he

private theorem vertical_after {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K)
    (a : Arc R) (ha : Active R (level K p + 1) a)
    (hh : (a.lower R).2 ≠ (a.upper R).2) : a.lower R = p := by
  have hs := (a.shape R).resolve_left (fun h => hh (congrArg Prod.snd h).symm)
  have he : level K (a.lower R) = level K p := by
    simp only [Active, level, hs] at ha ⊢
    omega
  exact level_injective (a.band R).1 hp he

private theorem horizontal_before {p : Point} (a : Arc R) (ha : Active R (level K p) a)
    (hh : (a.lower R).2 = (a.upper R).2) (hy : (a.lower R).2 = p.2) : a.upper R = p := by
  have hs := (a.shape R).resolve_right (fun h => by have := congrArg Prod.snd h; omega)
  have hm : (0 : ℤ) < (height K + 1 : ℕ) := by omega
  have hl : (a.lower R).1 < p.1 := (Int.mul_lt_mul_left hm).mp (by
    simpa only [level, hy, add_lt_add_iff_right] using ha.1)
  have hu : p.1 ≤ (a.lower R).1 + 1 := (Int.mul_le_mul_left hm).mp (by
    simpa only [level, hs, hy, add_le_add_iff_right] using ha.2)
  rw [hs]
  exact Prod.ext (by dsimp only; omega) hy

private theorem horizontal_after {p : Point} (a : Arc R) (ha : Active R (level K p + 1) a)
    (hh : (a.lower R).2 = (a.upper R).2) (hy : (a.lower R).2 = p.2) : a.lower R = p := by
  have hs := (a.shape R).resolve_right (fun h => by have := congrArg Prod.snd h; omega)
  have hm : (0 : ℤ) < (height K + 1 : ℕ) := by omega
  have hm₁ : (1 : ℤ) ≤ (height K + 1 : ℕ) := by omega
  have hla : (height K + 1 : ℕ) * (a.lower R).1 ≤ (height K + 1 : ℕ) * p.1 := by
    have := ha.1
    simp only [level, hy] at this
    omega
  have hl : (a.lower R).1 ≤ p.1 := (Int.mul_le_mul_left hm).mp hla
  have hu : p.1 < (a.lower R).1 + 1 := (Int.mul_lt_mul_left hm).mp (by
    have := ha.2
    simp only [level, hs, hy] at this
    omega)
  exact Prod.ext (by omega) hy

/-- The local middle block of the preceding frontier is exactly the incoming port list. -/
private theorem middle_before {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K)
    (a : Arc R) (ha : Active R (level K p) a) :
    (2 * p.2 - 2 < a.position R ∧ a.position R ≤ 2 * p.2 + 1) ↔ a.upper R = p := by
  by_cases hh : (a.lower R).2 = (a.upper R).2
  · simp only [position, hh, ↓reduceIte]
    constructor
    · intro hm
      exact horizontal_before R a ha hh (by omega)
    · intro hu
      have hy := congrArg Prod.snd hu
      omega
  · have hu := vertical_before R hp a ha hh
    have hy := congrArg Prod.snd hu
    simp only [position, hh, ↓reduceIte]
    exact ⟨fun _ => hu, fun _ => by omega⟩

/-- The local middle block of the following frontier is exactly the outgoing port list. -/
private theorem middle_after {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K)
    (a : Arc R) (ha : Active R (level K p + 1) a) :
    (2 * p.2 - 2 < a.position R ∧ a.position R ≤ 2 * p.2 + 1) ↔ a.lower R = p := by
  by_cases hh : (a.lower R).2 = (a.upper R).2
  · simp only [position, hh, ↓reduceIte]
    constructor
    · intro hm
      exact horizontal_after R a ha hh (by omega)
    · intro hl
      have hy := congrArg Prod.snd hl
      omega
  · have hl := vertical_after R hp a ha hh
    have hs := (a.shape R).resolve_left (fun h => hh (congrArg Prod.snd h).symm)
    rw [position, ite_eq_right hh]
    constructor
    · intro _
      exact hl
    · intro _
      simp only [hs, hl]
      omega

end Arc

private theorem split_sorted {α : Type*} (key : α → ℤ) (z : ℤ) (l : List α)
    (hs : l.Pairwise (fun a b => key b ≤ key a)) :
    l = l.filter (fun a => decide (z < key a)) ++ l.filter (fun a => decide (key a ≤ z)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : z < key a
    · simpa [ha, not_le.mpr ha] using congrArg (List.cons a) (ih hs.of_cons)
    · have hb : ∀ b ∈ l, key b ≤ z := fun b hb =>
        (List.rel_of_pairwise_cons hs hb).trans (le_of_not_gt ha)
      have he : l.filter (fun a => decide (z < key a)) = [] :=
        List.filter_eq_nil_iff.mpr (by simpa only [decide_eq_true_eq, not_lt] using hb)
      have hf : l.filter (fun a => decide (key a ≤ z)) = l :=
        List.filter_eq_self.mpr (by simpa only [decide_eq_true_eq] using hb)
      simp [ha, le_of_not_gt ha, he, hf]

private theorem split_three {α : Type*} (key : α → ℤ) (lo hi : ℤ) (hle : lo ≤ hi)
    (l : List α) (hs : l.Pairwise (fun a b => key b ≤ key a)) :
    l = l.filter (fun a => decide (hi < key a)) ++
      l.filter (fun a => decide (lo < key a ∧ key a ≤ hi)) ++
      l.filter (fun a => decide (key a ≤ lo)) := by
  have h := split_sorted key hi l hs
  have ht := split_sorted key lo (l.filter (fun a => decide (key a ≤ hi)))
    (hs.sublist List.filter_sublist)
  have hm : (l.filter (fun a => decide (key a ≤ hi))).filter (fun a => decide (lo < key a)) =
      l.filter (fun a => decide (lo < key a ∧ key a ≤ hi)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    simp only [Bool.decide_and, Bool.and_comm]
  have hb : (l.filter (fun a => decide (key a ≤ hi))).filter (fun a => decide (key a ≤ lo)) =
      l.filter (fun a => decide (key a ≤ lo)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    simp only [← Bool.decide_and]
    congr 1
    exact propext ⟨fun h => h.1, fun h => ⟨h, h.trans hle⟩⟩
  rw [ht, hm, hb, ← List.append_assoc] at h
  exact h

/-- A local sweep edit, with the unchanged context kept explicitly. -/
structure Slice where
  /-- Higher frontier arcs, unchanged by processing the site. -/
  above : List (Arc R)
  /-- Actual unit arcs ending at the processed site. -/
  incoming : List (Arc R)
  /-- Actual unit arcs starting at the processed site. -/
  outgoing : List (Arc R)
  /-- Lower frontier arcs, unchanged by processing the site. -/
  below : List (Arc R)

/-- The actual local edit at a lattice site. -/
@[expose] def slice (es : List E) (p : Point) : Slice R where
  above := (frontier R es (level K p)).filter (fun a => decide (2 * p.2 + 1 < a.position R))
  incoming := (frontier R es (level K p)).filter (fun a => decide (a.upper R = p))
  outgoing := (frontier R es (level K p + 1)).filter (fun a => decide (a.lower R = p))
  below := (frontier R es (level K p)).filter (fun a => decide (a.position R ≤ 2 * p.2 - 2))

/-- The preceding actual frontier consists of context, incoming ports, and context. -/
theorem slice_before (es : List E) {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) :
    frontier R es (level K p) =
      (slice R es p).above ++ (slice R es p).incoming ++ (slice R es p).below := by
  have hm : (frontier R es (level K p)).filter
      (fun a => decide (2 * p.2 - 2 < a.position R ∧ a.position R ≤ 2 * p.2 + 1)) =
      (slice R es p).incoming := by
    apply List.filter_congr
    intro a ha
    exact decide_eq_decide.mpr (PushPuzzle.NCL.Strip.Sweep.Arc.middle_before R hp a ((mem_frontier R es _ a).mp ha).2)
  simpa only [hm, slice] using split_three (PushPuzzle.NCL.Strip.Sweep.Arc.position R) (2 * p.2 - 2) (2 * p.2 + 1)
    (by omega) (frontier R es (level K p)) (frontier_sorted R es _)

private theorem context_unchanged {es : List E} (hes : es.Nodup) {p : Point}
    (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) (P : Arc R → Bool)
    (hout : ∀ a, P a → ¬(2 * p.2 - 2 < a.position R ∧ a.position R ≤ 2 * p.2 + 1)) :
    (frontier R es (level K p)).filter P = (frontier R es (level K p + 1)).filter P := by
  have hactive (a : Arc R) (hP : P a) :
      PushPuzzle.NCL.Strip.Sweep.Arc.Active R (level K p) a ↔ PushPuzzle.NCL.Strip.Sweep.Arc.Active R (level K p + 1) a := by
    constructor
    · intro ha
      apply (PushPuzzle.NCL.Strip.Sweep.Arc.active_succ_iff R hp a).mpr
      left
      exact ⟨ha, fun hu => hout a hP ((PushPuzzle.NCL.Strip.Sweep.Arc.middle_before R hp a ha).mpr hu)⟩
    · intro ha
      rcases (PushPuzzle.NCL.Strip.Sweep.Arc.active_succ_iff R hp a).mp ha with ha' | ha'
      · exact ha'.1
      · exact False.elim (hout a hP ((PushPuzzle.NCL.Strip.Sweep.Arc.middle_after R hp a ha).mpr ha'))
  have hmem (a : Arc R) :
      a ∈ (frontier R es (level K p)).filter P ↔
        a ∈ (frontier R es (level K p + 1)).filter P := by
    simp only [List.mem_filter, mem_frontier]
    exact ⟨fun h => ⟨⟨h.1.1, (hactive a h.2).mp h.1.2⟩, h.2⟩,
      fun h => ⟨⟨h.1.1, (hactive a h.2).mpr h.1.2⟩, h.2⟩⟩
  apply List.Perm.eq_of_pairwise (le := fun a b : Arc R => b.position R ≤ a.position R)
  · intro a b ha hb hab hba
    apply PushPuzzle.NCL.Strip.Sweep.Arc.position_injective_on R (level K p)
      ((mem_frontier R es _ a).mp (List.mem_filter.mp ha).1).2
      ((mem_frontier R es _ b).mp (List.mem_filter.mp ((hmem b).mpr hb)).1).2
    exact le_antisymm hba hab
  · exact (frontier_sorted R es _).sublist List.filter_sublist
  · exact (frontier_sorted R es _).sublist List.filter_sublist
  · exact (List.perm_ext_iff_of_nodup ((frontier_nodup R hes _).filter P)
      ((frontier_nodup R hes _).filter P)).mpr hmem

/-- The following frontier has the same context and exactly the outgoing local port block. -/
theorem slice_after {es : List E} (hes : es.Nodup) {p : Point}
    (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) :
    frontier R es (level K p + 1) =
      (slice R es p).above ++ (slice R es p).outgoing ++ (slice R es p).below := by
  have hm : (frontier R es (level K p + 1)).filter
      (fun a => decide (2 * p.2 - 2 < a.position R ∧ a.position R ≤ 2 * p.2 + 1)) =
      (slice R es p).outgoing := by
    apply List.filter_congr
    intro a ha
    exact decide_eq_decide.mpr (PushPuzzle.NCL.Strip.Sweep.Arc.middle_after R hp a ((mem_frontier R es _ a).mp ha).2)
  have ht := context_unchanged R hes hp (fun a => decide (2 * p.2 + 1 < a.position R)) (by
    intro a ha hm
    simp only [decide_eq_true_eq] at ha
    omega)
  have hb := context_unchanged R hes hp (fun a => decide (a.position R ≤ 2 * p.2 - 2)) (by
    intro a ha hm
    simp only [decide_eq_true_eq] at ha
    omega)
  have h := split_three (PushPuzzle.NCL.Strip.Sweep.Arc.position R) (2 * p.2 - 2) (2 * p.2 + 1)
    (by omega) (frontier R es (level K p + 1)) (frontier_sorted R es _)
  rw [← ht, hm, ← hb] at h
  exact h

/-- Incoming slice ports are exactly declared arcs ending at the current site. -/
theorem mem_slice_incoming (es : List E) (p : Point) (a : Arc R) :
    a ∈ (slice R es p).incoming ↔ a.edge ∈ es ∧ a.upper R = p := by
  simp only [slice, List.mem_filter, mem_frontier, decide_eq_true_eq]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨he, hu⟩
    refine ⟨⟨he, ?_⟩, hu⟩
    have hlt := a.level_lt R
    rw [hu] at hlt
    exact ⟨hlt, by rw [hu]⟩

/-- Outgoing slice ports are exactly declared arcs starting at the current site. -/
theorem mem_slice_outgoing (es : List E) (p : Point) (a : Arc R) :
    a ∈ (slice R es p).outgoing ↔ a.edge ∈ es ∧ a.lower R = p := by
  simp only [slice, List.mem_filter, mem_frontier, decide_eq_true_eq]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨he, hl⟩
    refine ⟨⟨he, ?_⟩, hl⟩
    have hlt := a.level_lt R
    rw [hl] at hlt
    exact ⟨by rw [hl]; omega, by omega⟩

/-- Incoming ports occupy the left and bottom geometric positions. -/
private theorem incoming_position (es : List E) (p : Point) {a : Arc R}
    (ha : a ∈ (slice R es p).incoming) :
    a.position R = 2 * p.2 ∨ a.position R = 2 * p.2 - 1 := by
  have hu := ((mem_slice_incoming R es p a).mp ha).2
  by_cases hh : (a.lower R).2 = (a.upper R).2
  · left
    rw [PushPuzzle.NCL.Strip.Sweep.Arc.position, ite_eq_left hh]
    simp only [hh, hu]
  · right
    rw [PushPuzzle.NCL.Strip.Sweep.Arc.position, ite_eq_right hh, hu]

/-- Outgoing ports occupy the top and right geometric positions. -/
private theorem outgoing_position (es : List E) (p : Point) {a : Arc R}
    (ha : a ∈ (slice R es p).outgoing) :
    a.position R = 2 * p.2 + 1 ∨ a.position R = 2 * p.2 := by
  have hl := ((mem_slice_outgoing R es p a).mp ha).2
  by_cases hh : (a.lower R).2 = (a.upper R).2
  · right
    rw [PushPuzzle.NCL.Strip.Sweep.Arc.position, ite_eq_left hh, hl]
  · left
    have hs := (a.shape R).resolve_left (fun h => hh (congrArg Prod.snd h).symm)
    rw [PushPuzzle.NCL.Strip.Sweep.Arc.position, ite_eq_right hh]
    simp only [hs, hl]
    omega

/-- Each actual incoming local port list has at most two labels. -/
private theorem incoming_length_le {es : List E} (hes : es.Nodup) (p : Point) :
    (slice R es p).incoming.length ≤ 2 := by
  have hn : ((slice R es p).incoming.map (PushPuzzle.NCL.Strip.Sweep.Arc.position R)).Nodup := by
    apply ((frontier_nodup R hes _).filter _).map_on
    intro a ha b hb hab
    exact PushPuzzle.NCL.Strip.Sweep.Arc.position_injective_on R (level K p)
      ((mem_frontier R es _ a).mp (List.mem_filter.mp ha).1).2
      ((mem_frontier R es _ b).mp (List.mem_filter.mp hb).1).2 hab
  have hsub : ((slice R es p).incoming.map (PushPuzzle.NCL.Strip.Sweep.Arc.position R)) ⊆ [2 * p.2, 2 * p.2 - 1] := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using incoming_position R es p ha
  have h := hn.length_le_of_subset hsub
  simpa only [List.length_map, List.length_cons, List.length_nil] using h

/-- Each actual outgoing local port list has at most two labels. -/
private theorem outgoing_length_le {es : List E} (hes : es.Nodup) (p : Point) :
    (slice R es p).outgoing.length ≤ 2 := by
  have hn : ((slice R es p).outgoing.map (PushPuzzle.NCL.Strip.Sweep.Arc.position R)).Nodup := by
    apply ((frontier_nodup R hes _).filter _).map_on
    intro a ha b hb hab
    exact PushPuzzle.NCL.Strip.Sweep.Arc.position_injective_on R (level K p + 1)
      ((mem_frontier R es _ a).mp (List.mem_filter.mp ha).1).2
      ((mem_frontier R es _ b).mp (List.mem_filter.mp hb).1).2 hab
  have hsub : ((slice R es p).outgoing.map (PushPuzzle.NCL.Strip.Sweep.Arc.position R)) ⊆ [2 * p.2 + 1, 2 * p.2] := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using outgoing_position R es p ha
  have h := hn.length_le_of_subset hsub
  simpa only [List.length_map, List.length_cons, List.length_nil] using h

private theorem eq_pair_of_sorted {α : Type*} (key : α → ℤ) {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hk : key b < key a) (hlen : l.length ≤ 2)
    (hs : l.Pairwise (fun a b => key b ≤ key a)) : l = [a, b] := by
  cases l with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons c l =>
    cases l with
    | nil =>
      simp only [List.mem_singleton] at ha hb
      rw [ha, hb] at hk
      omega
    | cons d l =>
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hlen
        omega)
      subst l
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      have hdc : key d ≤ key c := List.rel_of_pairwise_cons hs (by simp)
      rcases ha with ha | ha <;> rcases hb with hb | hb
      all_goals subst_vars
      all_goals first | rfl | omega

/-- Two distinct ordered incoming positions exhaust the actual incoming local block. -/
theorem incoming_eq_pair {es : List E} (hes : es.Nodup) {p : Point} {a b : Arc R}
    (ha : a ∈ (slice R es p).incoming) (hb : b ∈ (slice R es p).incoming)
    (hk : b.position R < a.position R) : (slice R es p).incoming = [a, b] :=
  eq_pair_of_sorted (PushPuzzle.NCL.Strip.Sweep.Arc.position R) ha hb hk (incoming_length_le R hes p)
    ((frontier_sorted R es _).sublist List.filter_sublist)

/-- Two distinct ordered outgoing positions exhaust the actual outgoing local block. -/
theorem outgoing_eq_pair {es : List E} (hes : es.Nodup) {p : Point} {a b : Arc R}
    (ha : a ∈ (slice R es p).outgoing) (hb : b ∈ (slice R es p).outgoing)
    (hk : b.position R < a.position R) : (slice R es p).outgoing = [a, b] :=
  eq_pair_of_sorted (PushPuzzle.NCL.Strip.Sweep.Arc.position R) ha hb hk (outgoing_length_le R hes p)
    ((frontier_sorted R es _).sublist List.filter_sublist)

end PushPuzzle.NCL.Strip.Sweep
