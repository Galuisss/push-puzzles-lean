/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerInternal
import all Push.PartnerInventory

/-! Standard page validity of literal lower-page ear insertions. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS PageLevels

private def Compatible (g k : Group) : Prop :=
  g.right < k.left ∨ k.right < g.left ∨ g.Contains k ∨ k.Contains g

private theorem Compatible.symm {g k : Group} (h : Compatible g k) : Compatible k g := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

private theorem page_bound_mem {p : Page} (hp : p.Valid) {g : Group} (hg : g ∈ p.groups) :
    g.left < g.right ∧ g.right < p.portCount := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  simpa only [Page.group, hi] using hp.bounded i

private theorem page_compatible_mem {p : Page} (hp : p.Valid) {g k : Group}
    (hg : g ∈ p.groups) (hk : k ∈ p.groups) (hne : g ≠ k) : Compatible g k := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hk
  have hij : i ≠ j := by
    intro he
    exact hne (hi.symm.trans ((congrArg (fun x => p.groups.get x) he).trans hj))
  simpa only [Page.group, hi, hj, Compatible] using hp.noncrossing i j hij

private theorem word_owner_unique {p : Page} (hw : (pageWord p).Perm (List.range p.portCount))
    {i j : p.Index} {k : ℕ} (hi : k ∈ (p.group i).ports) (hj : k ∈ (p.group j).ports) : i = j := by
  have hn := hw.nodup_iff.mpr List.nodup_range
  have hd := (List.nodup_flatMap.mp hn).2
  by_contra he
  rcases lt_or_gt_of_ne he with hij | hji
  · have hdisj := List.pairwise_iff_get.mp hd i j hij
    exact List.disjoint_left.mp hdisj ((mem_shapePorts _ _).mpr hi) ((mem_shapePorts _ _).mpr hj)
  · have hdisj := List.pairwise_iff_get.mp hd j i hji
    exact List.disjoint_left.mp hdisj ((mem_shapePorts _ _).mpr hj) ((mem_shapePorts _ _).mpr hi)

/-- The exact finite port word supplies the indexed partition required by standard page validity. -/
private theorem page_valid_of_word {p : Page}
    (hb : ∀ g ∈ p.groups, g.left < g.right ∧ g.right < p.portCount)
    (hw : (pageWord p).Perm (List.range p.portCount))
    (hc : ∀ g ∈ p.groups, ∀ k ∈ p.groups, g ≠ k → Compatible g k) : p.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hb (p.group i) (List.get_mem p.groups i)
  · intro k hk
    have hm := hw.mem_iff.mpr (List.mem_range.mpr hk)
    obtain ⟨g, hg, hkg⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
    have hki : k ∈ (p.group i).ports := by
      simpa only [Page.group, hi] using (mem_shapePorts g k).mp hkg
    exact ⟨i, hki, fun j hkj => word_owner_unique hw hkj hki⟩
  · intro i j hij
    have hne : p.group i ≠ p.group j := by
      intro he
      have hleft : (p.group i).left ∈ (p.group i).ports := by
        cases p.group i <;> simp [Group.left, Group.ports]
      exact hij (word_owner_unique hw hleft (he ▸ hleft))
    exact hc _ (List.get_mem p.groups i) _ (List.get_mem p.groups j) hne

private def mapShape (cut : ℕ) : Group → Group
  | .wire a b => .wire (shift cut a) (shift cut b)
  | .triple a => .triple (shift cut a)

private theorem mapGroup_shape (cut : ℕ) (g : LowerGroup) :
    (mapGroup cut g).shape = mapShape cut g.shape := by cases g <;> rfl

private theorem mapGroup_left (cut : ℕ) (g : LowerGroup) :
    (mapGroup cut g).shape.left = shift cut g.shape.left := by cases g <;> rfl

private theorem mapGroup_right {l : PortLayout} {cut : ℕ} (hs : SafeCut l cut)
    (g : LowerGroup) (hg : g ∈ l.lowerGroups) :
    (mapGroup cut g).shape.right = shift cut g.shape.right := by
  cases g with
  | wire a b => rfl
  | gate kind first => exact (shift_gate (hs kind first hg)).2.symm

private theorem compatible_shift {g k g' k' : Group} {cut : ℕ} (hc : Compatible g k)
    (hgl : g'.left = shift cut g.left) (hgr : g'.right = shift cut g.right)
    (hkl : k'.left = shift cut k.left) (hkr : k'.right = shift cut k.right) : Compatible g' k' := by
  have hm := shift_strictMono cut
  rcases hc with h | h | h | h
  · exact Or.inl (hgr ▸ hkl ▸ hm h)
  · exact Or.inr (Or.inl (hkr ▸ hgl ▸ hm h))
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    rcases h with ⟨hl, hr, hs⟩
    refine ⟨hgl ▸ hkl ▸ hm.monotone hl, hkr ▸ hgr ▸ hm.monotone hr, ?_⟩
    rcases hs with h | h
    · exact Or.inl (hgl ▸ hkl ▸ hm h)
    · exact Or.inr (hkr ▸ hgr ▸ hm h)
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    rcases h with ⟨hl, hr, hs⟩
    refine ⟨hkl ▸ hgl ▸ hm.monotone hl, hgr ▸ hkr ▸ hm.monotone hr, ?_⟩
    rcases hs with h | h
    · exact Or.inl (hkl ▸ hgl ▸ hm h)
    · exact Or.inr (hgr ▸ hkr ▸ hm h)

private theorem fresh_wire_compatible {g g' : Group} {cut : ℕ}
    (hgl : g'.left = shift cut g.left) (hgr : g'.right = shift cut g.right) :
    Compatible (.wire cut (cut + 1)) g' := by
  unfold Compatible Group.Contains
  rw [hgl, hgr]
  simp only [Group.left, Group.right]
  unfold shift
  split_ifs <;> omega

private theorem ear_lower_word {l : PortLayout} (hl : PortInventory l) {cut : ℕ} {ab : ℕ × ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) (hp : ab ∈ l.upperPairs) :
    (pageWord (ear l cut ab).pages.lowerPage).Perm (List.range (l.portCount + 2)) := by
  have he : pageWord (ear l cut ab).pages.lowerPage = (ear l cut ab).lowerGroups.flatMap groupPorts := by
    simp only [pageWord, PortLayout.pages, Pages.lowerPage, List.flatMap_map]
    apply List.flatMap_congr
    intro g _
    cases g <;> rfl
  rw [he]
  exact (ear_inventory hl cut ab hc hs hp).lower

/-- A safe ear insertion preserves the complete standard validity of the actual lower page. -/
theorem ear_lower_valid {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} {ab : ℕ × ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) (hp : ab ∈ l.upperPairs) :
    (ear l cut ab).pages.lowerPage.Valid := by
  apply page_valid_of_word (hw := ear_lower_word (inventory_of_pages hl) hc hs hp)
  · intro g hg
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hg
    rcases List.mem_append.mp hraw with hold | hnew
    · obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hold
      have hb := page_bound_mem hl.lower (List.mem_map.mpr ⟨old, hmem, rfl⟩)
      rw [mapGroup_left, mapGroup_right hs old hmem]
      exact ⟨shift_strictMono cut hb.1, shift_lt cut hb.2⟩
    · have he := List.mem_singleton.mp hnew
      subst raw
      simp only [LowerGroup.shape, Group.left, Group.right, ear, PortLayout.pages, Pages.lowerPage]
      omega
  · intro g hg k hk hne
    obtain ⟨rawg, hrawg, rfl⟩ := List.mem_map.mp hg
    obtain ⟨rawk, hrawk, rfl⟩ := List.mem_map.mp hk
    rcases List.mem_append.mp hrawg with hg | hg
    · obtain ⟨oldg, holdg, rfl⟩ := List.mem_map.mp hg
      rcases List.mem_append.mp hrawk with hk | hk
      · obtain ⟨oldk, holdk, rfl⟩ := List.mem_map.mp hk
        have he : oldg.shape ≠ oldk.shape := by
          intro he
          exact hne (by rw [mapGroup_shape, mapGroup_shape, he])
        have hcomp := page_compatible_mem hl.lower (List.mem_map.mpr ⟨oldg, holdg, rfl⟩)
          (List.mem_map.mpr ⟨oldk, holdk, rfl⟩) he
        exact compatible_shift hcomp (mapGroup_left cut oldg) (mapGroup_right hs oldg holdg)
          (mapGroup_left cut oldk) (mapGroup_right hs oldk holdk)
      · have he := List.mem_singleton.mp hk
        subst rawk
        exact (fresh_wire_compatible (mapGroup_left cut oldg) (mapGroup_right hs oldg holdg)).symm
    · have he := List.mem_singleton.mp hg
      subst rawg
      rcases List.mem_append.mp hrawk with hk | hk
      · obtain ⟨oldk, holdk, rfl⟩ := List.mem_map.mp hk
        exact fresh_wire_compatible (mapGroup_left cut oldk) (mapGroup_right hs oldk holdk)
      · have he := List.mem_singleton.mp hk
        subst rawk
        exact (hne rfl).elim

end PushPuzzle.Push.Partner
