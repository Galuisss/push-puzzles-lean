/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesEarUpper
public import Push.PartnerResourcesGrowth
import all Push.PartnerCutsValidity
import all Push.PartnerResourcesCuts

/-! Descending common cuts spend the upper active budget only once in the lower page. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS PageLevels

private theorem lower_test_shift {l : PortLayout} {cut count : ℕ} (hs : SafeCut l cut)
    {g : LowerGroup} (hg : g ∈ l.lowerGroups) (gap : ℕ) :
    gapTest gap ((Cuts.mapGroup cut count g).shape.left, (Cuts.mapGroup cut count g).shape.right) =
      gapTest gap (Cuts.mapPair cut count (g.shape.left, g.shape.right)) := by
  rw [Cuts.mapGroup_left, Cuts.mapGroup_right hs g hg]
  rfl

private theorem cut_lower_fresh_before (l : PortLayout) {cut gap : ℕ} (hg : gap < cut) :
    (((Cuts.active l cut).zipIdx.map (Cuts.lowerPiece cut (Cuts.active l cut).length)).countP
      (fun g => gapTest gap (g.shape.left, g.shape.right))) = 0 := by
  apply List.countP_eq_zero.mpr
  intro g hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hb := Cuts.left_bounds (cut := cut) hj
  simp only [Cuts.lowerPiece, LowerGroup.shape, Group.left, Group.right, gapTest]
  intro h
  have := of_decide_eq_true h
  omega

private theorem cut_lower_fresh_after (l : PortLayout) {cut gap : ℕ}
    (hg : cut + 2 * (Cuts.active l cut).length ≤ gap) :
    (((Cuts.active l cut).zipIdx.map (Cuts.lowerPiece cut (Cuts.active l cut).length)).countP
      (fun g => gapTest gap (g.shape.left, g.shape.right))) = 0 := by
  apply List.countP_eq_zero.mpr
  intro g hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hb := Cuts.right_bounds (cut := cut) hj
  simp only [Cuts.lowerPiece, LowerGroup.shape, Group.left, Group.right, gapTest]
  intro h
  have := of_decide_eq_true h
  omega

private theorem cut_lowerLoad_before {l : PortLayout} {cut gap : ℕ} (hs : SafeCut l cut)
    (hg : gap < cut) :
    lowerLoad (Cuts.compile l cut) gap = lowerLoad l gap := by
  unfold lowerLoad
  change ((l.lowerGroups.map (Cuts.mapGroup cut (Cuts.active l cut).length) ++
    (Cuts.active l cut).zipIdx.map (Cuts.lowerPiece cut (Cuts.active l cut).length))).countP _ = _
  rw [List.countP_append, cut_lower_fresh_before l hg, Nat.add_zero, List.countP_map]
  apply List.countP_congr
  intro g hm
  rw [Function.comp_apply, lower_test_shift hs hm gap, gapTest_shift_before cut _ gap hg]

private theorem cut_lowerLoad_after {l : PortLayout} {cut gap : ℕ} (hs : SafeCut l cut)
    (hg : cut + 2 * (Cuts.active l cut).length ≤ gap) :
    lowerLoad (Cuts.compile l cut) gap = lowerLoad l (gap - 2 * (Cuts.active l cut).length) := by
  unfold lowerLoad
  change ((l.lowerGroups.map (Cuts.mapGroup cut (Cuts.active l cut).length) ++
    (Cuts.active l cut).zipIdx.map (Cuts.lowerPiece cut (Cuts.active l cut).length))).countP _ = _
  rw [List.countP_append, cut_lower_fresh_after l hg, Nat.add_zero, List.countP_map]
  apply List.countP_congr
  intro g hm
  rw [Function.comp_apply, lower_test_shift hs hm gap, gapTest_shift_after cut _ gap hg]

private theorem cut_lowerLoad_inside {l : PortLayout} {cut gap : ℕ} (hs : SafeCut l cut)
    (hc : 0 < cut)
    (hg : cut ≤ gap ∧ gap < cut + 2 * (Cuts.active l cut).length) :
    lowerLoad (Cuts.compile l cut) gap ≤ lowerLoad l (cut - 1) + (Cuts.active l cut).length := by
  have hold : (l.lowerGroups.map (Cuts.mapGroup cut (Cuts.active l cut).length)).countP
      (fun g => gapTest gap (g.shape.left, g.shape.right)) = lowerLoad l (cut - 1) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro g hm
    rw [Function.comp_apply, lower_test_shift hs hm gap]
    simp only [gapTest, Cuts.mapPair, decide_eq_true_eq]
    unfold Cuts.shift
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  have hnew := List.countP_le_length (p := fun g : LowerGroup => gapTest gap (g.shape.left, g.shape.right))
    (l := (Cuts.active l cut).zipIdx.map (Cuts.lowerPiece cut (Cuts.active l cut).length))
  simp only [List.length_map, List.length_zipIdx] at hnew
  unfold lowerLoad
  change ((l.lowerGroups.map (Cuts.mapGroup cut (Cuts.active l cut).length) ++
    (Cuts.active l cut).zipIdx.map (Cuts.lowerPiece cut (Cuts.active l cut).length))).countP _ ≤ _
  rw [List.countP_append, hold]
  exact Nat.add_le_add_left hnew _

private theorem cutAt_lower_budget (s : BufferState) {base load cut : ℕ}
    (hu : ∀ gap, upperLoad s.layout gap ≤ load)
    (hg : ∀ gap, lowerLoad s.layout gap ≤ base + load)
    (hp : ∀ gap < cut, lowerLoad s.layout gap ≤ base) :
    (∀ gap, lowerLoad (Cuts.cutAt s cut).layout gap ≤ base + load) ∧
      (∀ gap < cut, lowerLoad (Cuts.cutAt s cut).layout gap ≤ base) := by
  unfold Cuts.cutAt
  split_ifs with hsafe
  · have hs := (Cuts.safeTest_eq_true s.layout cut).mp hsafe
    refine ⟨?_, ?_⟩
    · intro gap
      by_cases hbefore : gap < cut
      · rw [cut_lowerLoad_before hs hbefore]
        exact (hp gap hbefore).trans (by omega)
      by_cases hafter : cut + 2 * (Cuts.active s.layout cut).length ≤ gap
      · rw [cut_lowerLoad_after hs hafter]
        exact hg _
      have hc : 0 < cut := by
        by_contra hnot
        have he : cut = 0 := by omega
        rw [he, cut_active_zero] at hafter
        omega
      have ht := cut_active_le_of_load hu cut
      exact (cut_lowerLoad_inside hs hc ⟨by omega, by omega⟩).trans
        (Nat.add_le_add (hp _ (by omega)) ht)
    · intro gap hgap
      rw [cut_lowerLoad_before hs hgap]
      exact hp gap hgap
  · exact ⟨hg, hp⟩

/-- A descending scan inserts its nested lower blocks below distinct old gaps. -/
theorem cut_scan_range_lowerLoad (s : BufferState) (n : ℕ) {base load : ℕ}
    (hu : ∀ gap, upperLoad s.layout gap ≤ load)
    (hg : ∀ gap, lowerLoad s.layout gap ≤ base + load)
    (hp : ∀ gap < n, lowerLoad s.layout gap ≤ base) :
    ∀ gap, lowerLoad (Cuts.scan s (List.range n).reverse).layout gap ≤ base + load := by
  induction n generalizing s with
  | zero => exact hg
  | succ n ih =>
    have hb := cutAt_lower_budget s (cut := n) hu hg (fun gap hgap => hp gap (by omega))
    have hupper (gap : ℕ) : upperLoad (Cuts.cutAt s n).layout gap ≤ load := by
      unfold Cuts.cutAt
      split_ifs
      · exact cut_upperLoad_le hu n gap
      · exact hu gap
    have h := ih (Cuts.cutAt s n) hupper hb.1 hb.2
    simpa only [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      Cuts.scan, List.foldl_cons] using h

end PushPuzzle.Push.Partner.Resources
