/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerValidity
import all Push.PartnerValidity
import all Push.PartnerInventory

/-! The two actual upper ears are nested and preserve every surrounding original upper arc. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS PageLevels

private theorem upperPairs_nodup {l : PortLayout} (hl : PortInventory l) : l.upperPairs.Nodup := by
  have hn := hl.upper.nodup_iff.mpr List.nodup_range
  apply (List.nodup_flatMap.mp hn).2.imp
  intro ab xy hd he
  subst xy
  exact (List.disjoint_left.mp hd) (a := ab.1) (by simp [pairPorts]) (by simp [pairPorts])

private theorem shared_upper {l : PortLayout} (hl : PortInventory l) {ab xy : ℕ × ℕ}
    (hab : ab ∈ l.upperPairs) (hxy : xy ∈ l.upperPairs) {i : ℕ}
    (hi : i ∈ pairPorts ab) (hj : i ∈ pairPorts xy) : ab = xy := by
  have hn := hl.upper.nodup_iff.mpr List.nodup_range
  have hd := (List.nodup_flatMap.mp hn).2
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp hab
  obtain ⟨b, hb⟩ := List.mem_iff_get.mp hxy
  by_cases he : a = b
  · exact ha.symm.trans ((congrArg (fun x => l.upperPairs.get x) he).trans hb)
  rcases lt_or_gt_of_ne he with hab | hba
  · have hdisj := List.pairwise_iff_get.mp hd a b hab
    exact (List.disjoint_left.mp hdisj (ha.symm ▸ hi) (hb.symm ▸ hj)).elim
  · have hdisj := List.pairwise_iff_get.mp hd b a hba
    exact (List.disjoint_left.mp hdisj (hb.symm ▸ hj) (ha.symm ▸ hi)).elim

private theorem adjacent_pair_surroundings {l : PortLayout} (hl : l.pages.Valid) {a : ℕ}
    (hp : (a, a + 1) ∈ l.upperPairs) {xy : ℕ × ℕ} (hxy : xy ∈ l.upperPairs.erase (a, a + 1)) :
    xy.2 < a ∨ a + 1 < xy.1 ∨ (xy.1 < a ∧ a + 1 < xy.2) := by
  have hi := inventory_of_pages hl
  have hm := List.mem_of_mem_erase hxy
  have hne : xy ≠ (a, a + 1) := by
    rintro rfl
    exact (upperPairs_nodup hi).not_mem_erase hxy
  have hxa : xy.1 ≠ a := by
    intro he
    exact hne (shared_upper hi hm hp (i := xy.1) (by simp [pairPorts]) (by simp [pairPorts, he]))
  have hxb : xy.1 ≠ a + 1 := by
    intro he
    exact hne (shared_upper hi hm hp (i := xy.1) (by simp [pairPorts]) (by simp [pairPorts, he]))
  have hya : xy.2 ≠ a := by
    intro he
    exact hne (shared_upper hi hm hp (i := xy.2) (by simp [pairPorts]) (by simp [pairPorts, he]))
  have hyb : xy.2 ≠ a + 1 := by
    intro he
    exact hne (shared_upper hi hm hp (i := xy.2) (by simp [pairPorts]) (by simp [pairPorts, he]))
  have hbound := page_bound_mem hl.upper (List.mem_map.mpr ⟨xy, hm, rfl⟩)
  have hcomp := page_compatible_mem hl.upper (List.mem_map.mpr ⟨xy, hm, rfl⟩)
    (List.mem_map.mpr ⟨(a, a + 1), hp, rfl⟩) (by
      intro he
      exact hne (by cases xy; cases he; rfl))
  simp only [Compatible, Group.Contains, Group.left, Group.right] at hcomp hbound
  omega

private theorem ear_upper_members (l : PortLayout) (a cut : ℕ) (hc : cut = a ∨ cut = a + 2)
    (xy : ℕ × ℕ) :
    xy ∈ (ear l cut (a, a + 1)).upperPairs ↔
      xy = (a + 1, a + 2) ∨ xy = (a, a + 3) ∨
        xy ∈ (l.upperPairs.erase (a, a + 1)).map (mapPair cut) := by
  rcases hc with hc | hc
  · subst cut
    simp only [ear, shift, Nat.lt_irrefl, ite_false, show ¬a + 1 < a by omega,
      Nat.add_assoc, sortPair, min_eq_right (by omega : a + 1 ≤ a + 2),
      max_eq_left (by omega : a + 1 ≤ a + 2), min_eq_right (by omega : a ≤ a + 3),
      max_eq_left (by omega : a ≤ a + 3), List.mem_cons]
  · subst cut
    simp only [ear, shift, show a < a + 2 by omega, show a + 1 < a + 2 by omega,
      ite_true, Nat.add_assoc, sortPair, min_eq_left (by omega : a ≤ a + 3),
      max_eq_right (by omega : a ≤ a + 3), min_eq_left (by omega : a + 1 ≤ a + 2),
      max_eq_right (by omega : a + 1 ≤ a + 2), List.mem_cons]
    tauto

private theorem ear_new_old_compatible {l : PortLayout} (hl : l.pages.Valid) {a cut : ℕ}
    (hp : (a, a + 1) ∈ l.upperPairs) (hc : cut = a ∨ cut = a + 2)
    {xy : ℕ × ℕ} (hxy : xy ∈ l.upperPairs.erase (a, a + 1)) :
    Compatible (.wire (a + 1) (a + 2)) (.wire (shift cut xy.1) (shift cut xy.2)) ∧
      Compatible (.wire a (a + 3)) (.wire (shift cut xy.1) (shift cut xy.2)) := by
  have hpos := adjacent_pair_surroundings hl hp hxy
  rcases hc with rfl | rfl
  all_goals
    unfold Compatible Group.Contains
    simp only [Group.left, Group.right]
    unfold shift
    split_ifs <;> omega

private theorem ear_upper_word {l : PortLayout} (hl : PortInventory l) {cut : ℕ} {ab : ℕ × ℕ}
    (hc : cut ≤ l.portCount) (hp : ab ∈ l.upperPairs) :
    (pageWord (ear l cut ab).pages.upperPage).Perm (List.range (l.portCount + 2)) := by
  have he : pageWord (ear l cut ab).pages.upperPage = (ear l cut ab).upperPairs.flatMap pairPorts := by
    simp only [pageWord, PortLayout.pages, Pages.upperPage, List.flatMap_map]
    rfl
  rw [he]
  exact (ear_upper_ports l cut ab hp).trans
    (((hl.upper.map (shift cut)).append_right _).trans (shift_range_perm cut l.portCount hc))

/-- Either external two-port ear on a literal adjacent pair preserves the standard upper page. -/
private theorem ear_upper_valid {l : PortLayout} (hl : l.pages.Valid) {a cut : ℕ}
    (hp : (a, a + 1) ∈ l.upperPairs) (hc : cut = a ∨ cut = a + 2) :
    (ear l cut (a, a + 1)).pages.upperPage.Valid := by
  have hbound := page_bound_mem hl.upper (List.mem_map.mpr ⟨(a, a + 1), hp, rfl⟩)
  change a < a + 1 ∧ a + 1 < l.portCount at hbound
  have hcut : cut ≤ l.portCount := by rcases hc with rfl | rfl <;> omega
  apply page_valid_of_word (hw := ear_upper_word (inventory_of_pages hl) hcut hp)
  · intro g hg
    obtain ⟨xy, hxy, rfl⟩ := List.mem_map.mp hg
    rcases (ear_upper_members l a cut hc xy).mp hxy with rfl | rfl | hxy
    · simp only [Group.left, Group.right, ear, PortLayout.pages, Pages.upperPage]
      omega
    · simp only [Group.left, Group.right, ear, PortLayout.pages, Pages.upperPage]
      omega
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hxy
      have hb := page_bound_mem hl.upper (List.mem_map.mpr ⟨old, List.mem_of_mem_erase hold, rfl⟩)
      exact ⟨shift_strictMono cut hb.1, shift_lt cut hb.2⟩
  · intro g hg k hk hne
    obtain ⟨xy, hxy, rfl⟩ := List.mem_map.mp hg
    obtain ⟨uv, huv, rfl⟩ := List.mem_map.mp hk
    rcases (ear_upper_members l a cut hc xy).mp hxy with rfl | rfl | hxy
    · rcases (ear_upper_members l a cut hc uv).mp huv with rfl | rfl | huv
      · exact (hne rfl).elim
      · unfold Compatible Group.Contains
        simp only [Group.left, Group.right]
        omega
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp huv
        exact (ear_new_old_compatible hl hp hc hold).1
    · rcases (ear_upper_members l a cut hc uv).mp huv with rfl | rfl | huv
      · unfold Compatible Group.Contains
        simp only [Group.left, Group.right]
        omega
      · exact (hne rfl).elim
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp huv
        exact (ear_new_old_compatible hl hp hc hold).2
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hxy
      rcases (ear_upper_members l a cut hc uv).mp huv with rfl | rfl | huv
      · exact (ear_new_old_compatible hl hp hc hold).1.symm
      · exact (ear_new_old_compatible hl hp hc hold).2.symm
      · obtain ⟨other, hother, rfl⟩ := List.mem_map.mp huv
        have hneq : Group.wire old.1 old.2 ≠ .wire other.1 other.2 := by
          intro he
          have hpairs : old = other := by cases old; cases other; cases he; rfl
          exact hne (hpairs ▸ rfl)
        have hcomp := page_compatible_mem hl.upper
          (List.mem_map.mpr ⟨old, List.mem_of_mem_erase hold, rfl⟩)
          (List.mem_map.mpr ⟨other, List.mem_of_mem_erase hother, rfl⟩) hneq
        exact compatible_shift hcomp rfl rfl rfl rfl

/-- The actual left ear preserves both complete standard noncrossing pages. -/
theorem leftEar_valid {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hp : (first, first + 1) ∈ l.upperPairs) :
    (leftEar l first).pages.Valid := by
  have hb := inventory_gate_bound (inventory_of_pages hl) hg
  refine ⟨ear_upper_valid hl hp (Or.inl rfl),
    ear_lower_valid hl (by omega) (gate_boundary_safe hl hg).1 hp, ?_⟩
  intro i
  obtain ⟨ab, _, he⟩ := List.mem_map.mp (List.get_mem (leftEar l first).pages.upperPage.groups i)
  exact ⟨ab.1, ab.2, he.symm⟩

/-- The reflected right ear preserves both complete standard noncrossing pages. -/
theorem rightEar_valid {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hp : (first + 1, first + 2) ∈ l.upperPairs) :
    (rightEar l first).pages.Valid := by
  have hb := inventory_gate_bound (inventory_of_pages hl) hg
  have hpair : (first + 1, (first + 1) + 1) ∈ l.upperPairs := by simpa only [Nat.add_assoc] using hp
  have hu := ear_upper_valid hl hpair (cut := first + 3) (Or.inr (by omega))
  refine ⟨by simpa only [rightEar, Nat.add_assoc] using hu,
    ear_lower_valid hl hb (gate_boundary_safe hl hg).2 hp, ?_⟩
  intro i
  obtain ⟨ab, _, he⟩ := List.mem_map.mp (List.get_mem (rightEar l first).pages.upperPage.groups i)
  exact ⟨ab.1, ab.2, he.symm⟩

end PushPuzzle.Push.Partner
