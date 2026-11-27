/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesCutLower
import all Push.PartnerValidity
import all Push.PartnerInventory
import all Push.PartnerInternal

/-! Literal internal ears preserve the complete lower active-interval budget. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS PageLevels

private theorem lower_left_mem (g : LowerGroup) : g.shape.left ∈ groupPorts g := by
  cases g <;> simp [LowerGroup.shape, Group.left, groupPorts]

private theorem lower_right_mem (g : LowerGroup) : g.shape.right ∈ groupPorts g := by
  cases g <;> simp [LowerGroup.shape, Group.right, groupPorts]

private theorem lowerGroups_nodup {l : PortLayout} (hl : PortInventory l) : l.lowerGroups.Nodup := by
  have hn := hl.lower.nodup_iff.mpr List.nodup_range
  apply (List.nodup_flatMap.mp hn).2.imp
  intro g k hd he
  subst k
  exact (List.disjoint_left.mp hd) (a := g.shape.left) (lower_left_mem g) (lower_left_mem g)

private theorem lower_gate_surroundings {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) {g : LowerGroup}
    (hm : g ∈ l.lowerGroups.erase (.gate kind first)) :
    g.shape.right < first ∨ first + 2 < g.shape.left ∨
      (g.shape.left < first ∧ first + 2 < g.shape.right) := by
  have hi := inventory_of_pages hl
  have hmem := List.mem_of_mem_erase hm
  have hne : g ≠ .gate kind first := by
    rintro rfl
    exact (lowerGroups_nodup hi).not_mem_erase hm
  have hleft : ¬(first ≤ g.shape.left ∧ g.shape.left ≤ first + 2) := by
    intro hb
    exact hne (shared_lower hi hmem hg (lower_left_mem g) (by simp [groupPorts]; omega))
  have hright : ¬(first ≤ g.shape.right ∧ g.shape.right ≤ first + 2) := by
    intro hb
    exact hne (shared_lower hi hmem hg (lower_right_mem g) (by simp [groupPorts]; omega))
  have hbound := page_bound_mem hl.lower (List.mem_map.mpr ⟨g, hmem, rfl⟩)
  have hcomp := page_compatible_mem hl.lower (List.mem_map.mpr ⟨g, hmem, rfl⟩)
    (List.mem_map.mpr ⟨.gate kind first, hg, rfl⟩) (by
      intro he
      have he' := congrArg Group.left he
      change g.shape.left = first at he'
      omega)
  simp only [Compatible, Group.Contains, LowerGroup.shape, Group.left, Group.right] at hcomp
  omega

private theorem ear_lower_test_shift {l : PortLayout} {cut : ℕ} (hs : SafeCut l cut)
    {g : LowerGroup} (hg : g ∈ l.lowerGroups) (gap : ℕ) :
    gapTest gap ((mapGroup cut g).shape.left, (mapGroup cut g).shape.right) =
      gapTest gap (mapPair cut (g.shape.left, g.shape.right)) := by
  rw [mapGroup_left, mapGroup_right hs g hg]
  rfl

private theorem ear_lower_before {l : PortLayout} {cut gap : ℕ} (hs : SafeCut l cut) (hg : gap < cut)
    (ab : ℕ × ℕ) : lowerLoad (ear l cut ab) gap = lowerLoad l gap := by
  have hwire : gapTest gap (cut, cut + 1) = false := by
    simp only [gapTest, decide_eq_false_iff_not]
    omega
  unfold lowerLoad
  change (l.lowerGroups.map (mapGroup cut) ++ [LowerGroup.wire cut (cut + 1)]).countP _ = _
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp only [LowerGroup.shape, Group.left, Group.right, hwire, Bool.false_eq_true, ite_false, Nat.add_zero,
    List.countP_map]
  apply List.countP_congr
  intro g hm
  change gapTest gap ((mapGroup cut g).shape.left, (mapGroup cut g).shape.right) = true ↔
    gapTest gap (g.shape.left, g.shape.right) = true
  rw [ear_lower_test_shift hs hm gap]
  apply Iff.of_eq
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [gapTest, mapPair, decide_eq_true_eq]
  unfold shift
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

private theorem ear_lower_after {l : PortLayout} {cut gap : ℕ} (hs : SafeCut l cut) (hg : cut + 2 ≤ gap)
    (ab : ℕ × ℕ) : lowerLoad (ear l cut ab) gap = lowerLoad l (gap - 2) := by
  have hwire : gapTest gap (cut, cut + 1) = false := by
    simp only [gapTest, decide_eq_false_iff_not]
    omega
  unfold lowerLoad
  change (l.lowerGroups.map (mapGroup cut) ++ [LowerGroup.wire cut (cut + 1)]).countP _ = _
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp only [LowerGroup.shape, Group.left, Group.right, hwire, Bool.false_eq_true, ite_false, Nat.add_zero,
    List.countP_map]
  apply List.countP_congr
  intro g hm
  change gapTest gap ((mapGroup cut g).shape.left, (mapGroup cut g).shape.right) = true ↔
    gapTest (gap - 2) (g.shape.left, g.shape.right) = true
  rw [ear_lower_test_shift hs hm gap]
  apply Iff.of_eq
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [gapTest, mapPair, decide_eq_true_eq]
  unfold shift
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

private theorem ear_lower_inside {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first cut gap : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hc : cut = first ∨ cut = first + 3)
    (hs : SafeCut l cut) (hgap : cut ≤ gap ∧ gap < cut + 2) (ab : ℕ × ℕ) :
    lowerLoad (ear l cut ab) gap ≤ lowerLoad l first := by
  let pred : LowerGroup → Bool := fun g => gapTest first (g.shape.left, g.shape.right)
  let pred' : LowerGroup → Bool := fun g => gapTest gap ((mapGroup cut g).shape.left, (mapGroup cut g).shape.right)
  have hgtest : pred (.gate kind first) = true := by
    change decide (first ≤ first ∧ first < first + 2) = true
    exact decide_eq_true (by omega)
  have hgtest' : pred' (.gate kind first) = false := by
    rcases hc with hc | hc <;> subst cut
    all_goals
      simp only [pred', mapGroup, LowerGroup.shape, Group.left, Group.right, gapTest,
        shift, Nat.lt_irrefl, ite_false, show first < first + 3 by omega, ite_true,
        decide_eq_false_iff_not]
      omega
  have hr : (l.lowerGroups.erase (.gate kind first)).countP pred' =
      (l.lowerGroups.erase (.gate kind first)).countP pred := by
    apply List.countP_congr
    intro g hm
    have hpos := lower_gate_surroundings hl hg hm
    change gapTest gap ((mapGroup cut g).shape.left, (mapGroup cut g).shape.right) = true ↔ _
    rw [ear_lower_test_shift hs (List.mem_of_mem_erase hm) gap]
    rcases hc with hc | hc <;> subst cut
    all_goals
      simp only [pred, gapTest, mapPair, decide_eq_true_eq]
      unfold shift
      split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  have hold := List.Perm.countP_eq pred (List.perm_cons_erase hg)
  have hnew := List.Perm.countP_eq pred' (List.perm_cons_erase hg)
  simp only [List.countP_cons, hgtest, hgtest', ite_true, Bool.false_eq_true, ite_false, Nat.add_zero] at hold hnew
  rw [hr] at hnew
  unfold lowerLoad
  change (l.lowerGroups.map (mapGroup cut) ++ [LowerGroup.wire cut (cut + 1)]).countP _ ≤ _
  rw [List.countP_append, List.countP_map, List.countP_cons, List.countP_nil]
  change l.lowerGroups.countP pred' + (0 + if gapTest gap (cut, cut + 1) = true then 1 else 0) ≤ l.lowerGroups.countP pred
  split_ifs <;> omega

private theorem ear_lowerLoad_le {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hb : ∀ gap, lowerLoad l gap ≤ bound) {kind : Shuttle.Kind} {first cut : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hc : cut = first ∨ cut = first + 3) (ab : ℕ × ℕ)
    (gap : ℕ) : lowerLoad (ear l cut ab) gap ≤ bound := by
  have hs : SafeCut l cut := hc.elim (fun he => he ▸ (gate_boundary_safe hl hg).1)
    (fun he => he ▸ (gate_boundary_safe hl hg).2)
  by_cases hbefore : gap < cut
  · rw [ear_lower_before hs hbefore]
    exact hb _
  by_cases hafter : cut + 2 ≤ gap
  · rw [ear_lower_after hs hafter]
    exact hb _
  exact (ear_lower_inside hl hg hc hs ⟨by omega, by omega⟩ ab).trans (hb first)

private theorem bufferAt_lowerLoad (s : BufferState) (first : ℕ) (hs : s.layout.pages.Valid) {bound : ℕ}
    (hb : ∀ gap, lowerLoad s.layout gap ≤ bound) : ∀ gap, lowerLoad (s.bufferAt first).layout gap ≤ bound := by
  unfold BufferState.bufferAt
  split_ifs with hg hp hq
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    exact ear_lowerLoad_le hs hb hgate (Or.inl rfl) _
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    exact ear_lowerLoad_le hs hb hgate (Or.inr rfl) _
  all_goals exact hb

private theorem internal_scan_lowerLoad (s : BufferState) (positions : List ℕ)
    (hs : s.layout.pages.Valid) {bound : ℕ}
    (hb : ∀ gap, lowerLoad s.layout gap ≤ bound) : ∀ gap, lowerLoad (s.scan positions).layout gap ≤ bound := by
  induction positions generalizing s with
  | nil => exact hb
  | cons first rest ih => exact ih (s.bufferAt first) (s.bufferAt_valid first hs) (bufferAt_lowerLoad s first hs hb)

/-- All internal ears preserve the source lower nesting budget. -/
private theorem internal_lowerLoad_le {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hb : l.pages.lowerPage.maxActive ≤ bound) (gap : ℕ) : lowerLoad (bufferInternal l).layout gap ≤ bound :=
  internal_scan_lowerLoad (BufferState.start l) _ hl (fun i => (lowerLoad_le_maxActive hl i).trans hb) gap

/-- The full repair's lower nesting budget is the old lower budget plus the repaired upper budget. -/
theorem repair_lower_maxActive {l : PortLayout} (hl : l.pages.Valid) {upper lower : ℕ}
    (hu : l.pages.upperPage.maxActive ≤ upper) (hb : l.pages.lowerPage.maxActive ≤ lower) :
    (Cuts.repair l).layout.pages.lowerPage.maxActive ≤ lower + upper + 1 := by
  have hlow := internal_lowerLoad_le hl hb
  have h := cut_scan_range_lowerLoad (bufferInternal l) (bufferInternal l).layout.portCount
    (internal_upperLoad_le hl hu) (fun gap => (hlow gap).trans (by omega)) (fun gap _ => hlow gap)
  apply lower_maxActive_le
  intro gap
  change lowerLoad (Cuts.scan (bufferInternal l) (List.range (bufferInternal l).layout.portCount).reverse).layout gap ≤ _
  have := h gap
  omega

end PushPuzzle.Push.Partner.Resources
