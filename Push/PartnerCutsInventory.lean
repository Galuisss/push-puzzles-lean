/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCuts

/-! Exact old and fresh endpoint inventories of the actual common-cut compiler. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

private def freshWord (cut count : ℕ) : List ℕ :=
  (List.range count).flatMap fun j => [left cut count j, right cut count j]

private theorem mem_freshWord (cut count x : ℕ) :
    x ∈ freshWord cut count ↔ cut ≤ x ∧ x < cut + 2 * count := by
  simp only [freshWord, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨j, hj, rfl | rfl⟩
    · have := left_bounds (cut := cut) hj
      omega
    · have := right_bounds (cut := cut) hj
      omega
  · rintro ⟨hlo, hhi⟩
    by_cases h : x < cut + count
    · refine ⟨count - 1 - (x - cut), by omega, Or.inl ?_⟩
      unfold left
      omega
    · refine ⟨x - cut - count, by omega, Or.inr ?_⟩
      unfold right
      omega

private theorem freshWord_nodup (cut count : ℕ) : (freshWord cut count).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro j hj
    have h := left_lt_right (cut := cut) (List.mem_range.mp hj)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true, not_false_eq_true]
    exact ne_of_lt h
  · apply List.pairwise_iff_get.mpr
    intro i j hij
    have hi : i.val < count := by simpa only [List.length_range] using i.isLt
    have hj : j.val < count := by simpa only [List.length_range] using j.isLt
    simp only [List.get_eq_getElem, List.getElem_range]
    apply List.disjoint_left.mpr
    intro x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, left, right] at hx hy
    omega

private theorem shift_range_perm (cut count n : ℕ) (hc : cut ≤ n) :
    ((List.range n).map (shift cut count) ++ freshWord cut count).Perm (List.range (n + 2 * count)) := by
  have hn : ((List.range n).map (shift cut count) ++ freshWord cut count).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.Nodup.map (shift_injective cut count) List.nodup_range, freshWord_nodup cut count, ?_⟩
    intro a ha b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact fun he => shift_ne_fresh cut count i ((mem_freshWord cut count b).mp hb) he
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr
  intro x
  simp only [List.mem_append, List.mem_map, List.mem_range, mem_freshWord]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨hlo, hhi⟩)
    · exact shift_lt cut count hi
    · omega
  · intro hx
    by_cases hf : cut ≤ x ∧ x < cut + 2 * count
    · exact Or.inr hf
    apply Or.inl
    by_cases h : x < cut
    · exact ⟨x, by omega, by simp only [shift, ite_eq_left h]⟩
    · refine ⟨x - 2 * count, by omega, ?_⟩
      have hsub : ¬x - 2 * count < cut := by omega
      simp only [shift, ite_eq_right hsub]
      omega

private theorem interleave_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap fun x => f x ++ g x).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons a rest ih =>
    have hp := (List.Perm.refl (f a ++ g a)).append ih
    apply Multiset.coe_eq_coe.mp
    have he := Multiset.coe_eq_coe.mpr hp
    simp only [List.flatMap_cons, ← Multiset.coe_add] at he ⊢
    rw [he]
    ac_rfl

private theorem zipIdx_flatMap_fst {α β : Type} (xs : List α) (f : α → List β) :
    (xs.zipIdx.flatMap fun p => f p.1) = xs.flatMap f := by
  rw [← List.flatMap_map, List.zipIdx_map_fst]

private theorem zipIdx_flatMap_snd {α β : Type} (xs : List α) (f : ℕ → List β) :
    (xs.zipIdx.flatMap fun p => f p.2) = (List.range xs.length).flatMap f := by
  rw [← List.flatMap_map, List.zipIdx_map_snd, ← List.range_eq_range']

private theorem split_upper_word (xs : List (ℕ × ℕ)) (cut count : ℕ) :
    ((xs.zipIdx.flatMap (upperPiece cut count)).flatMap pairPorts).Perm
      ((xs.flatMap pairPorts).map (shift cut count) ++
        (List.range xs.length).flatMap fun j => [left cut count j, right cut count j]) := by
  rw [List.flatMap_assoc]
  have hp := List.Perm.flatMap_left xs.zipIdx (f := fun p => (upperPiece cut count p).flatMap pairPorts)
    (g := fun p => (pairPorts p.1).map (shift cut count) ++ [left cut count p.2, right cut count p.2]) (by
      intro p _
      simp only [upperPiece, List.flatMap_cons, List.flatMap_nil, pairPorts, List.map_cons,
        List.map_nil, List.append_nil]
      exact (((List.Perm.swap (shift cut count p.1.2) (right cut count p.2) []).cons
        (left cut count p.2)).trans
        (List.Perm.swap (shift cut count p.1.2) (left cut count p.2) [right cut count p.2])).cons
        (shift cut count p.1.1))
  have hi := interleave_perm xs.zipIdx (fun p => (pairPorts p.1).map (shift cut count))
    (fun p => [left cut count p.2, right cut count p.2])
  apply hp.trans
  have hf := zipIdx_flatMap_fst xs (fun ab => (pairPorts ab).map (shift cut count))
  have hg := zipIdx_flatMap_snd xs (fun j => [left cut count j, right cut count j])
  rw [hf, hg, ← List.map_flatMap] at hi
  exact hi

private theorem mapGroup_ports {l : PortLayout} {cut count : ℕ} (hs : SafeCut l cut)
    (g : LowerGroup) (hg : g ∈ l.lowerGroups) :
    groupPorts (mapGroup cut count g) = (groupPorts g).map (shift cut count) := by
  cases g with
  | wire a b => rfl
  | gate kind first =>
    obtain ⟨h₁, h₂⟩ := shift_gate (count := count) (hs kind first hg)
    simp only [groupPorts, mapGroup, List.map_cons, List.map_nil, h₁, h₂]

/-- The emitted upper arcs contain exactly the shifted original endpoints and the complete fresh block. -/
private theorem upper_word (l : PortLayout) (cut : ℕ) :
    ((compile l cut).upperPairs.flatMap pairPorts).Perm
      ((l.upperPairs.flatMap pairPorts).map (shift cut (active l cut).length) ++ freshWord cut (active l cut).length) := by
  let xs := active l cut
  let count := xs.length
  have hp := (split_upper_word xs cut count).append_right
    (((passive l cut).map (mapPair cut count)).flatMap pairPorts)
  have hpassive : (((passive l cut).map (mapPair cut count)).flatMap pairPorts) =
      ((passive l cut).flatMap pairPorts).map (shift cut count) := by
    simp only [List.flatMap_map, List.map_flatMap]
    rfl
  have horiginal := ((active_passive_perm l cut).flatMap_right pairPorts).map (shift cut count)
  apply Multiset.coe_eq_coe.mp
  have he := Multiset.coe_eq_coe.mpr hp
  have ho := Multiset.coe_eq_coe.mpr horiginal
  simp only [compile, List.flatMap_append] at he ⊢
  rw [he, hpassive]
  simp only [List.flatMap_append, List.map_append, ← Multiset.coe_add] at ho
  simp only [← Multiset.coe_add]
  rw [← ho]
  ac_rfl

/-- The actual lower word is the shifted original inventory followed by the nested fresh wires. -/
private theorem lower_word (l : PortLayout) (cut : ℕ) (hs : SafeCut l cut) :
    (compile l cut).lowerGroups.flatMap groupPorts =
      (l.lowerGroups.flatMap groupPorts).map (shift cut (active l cut).length) ++ freshWord cut (active l cut).length := by
  simp only [compile, List.flatMap_append, List.flatMap_map]
  congr 1
  · rw [List.map_flatMap]
    apply List.flatMap_congr
    intro g hg
    exact mapGroup_ports hs g hg
  · simpa only [lowerPiece, groupPorts, freshWord] using zipIdx_flatMap_snd (active l cut)
      (fun j => [left cut (active l cut).length j, right cut (active l cut).length j])

/-- The literal common cut preserves the complete standard finite port inventory on both pages. -/
theorem compile_inventory {l : PortLayout} (hl : PortInventory l) (cut : ℕ)
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) : PortInventory (compile l cut) := by
  have hr := shift_range_perm cut (active l cut).length l.portCount hc
  constructor
  · exact (upper_word l cut).trans (((hl.upper.map _).append_right _).trans hr)
  · rw [lower_word l cut hs]
    exact ((hl.lower.map _).append_right _).trans hr

end PushPuzzle.Push.Partner.Cuts
