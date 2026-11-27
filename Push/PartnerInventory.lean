/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerEar

/-! Exact finite port inventories of valid pages and their actual ear subdivisions. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS PageLevels

private def shapePorts : Group → List ℕ
  | .wire a b => [a, b]
  | .triple a => [a, a + 1, a + 2]

private theorem mem_shapePorts (g : Group) (i : ℕ) : i ∈ shapePorts g ↔ i ∈ g.ports := by
  cases g <;> simp only [shapePorts, Group.ports, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_insert, Finset.mem_singleton]

private theorem shapePorts_nodup {g : Group} (hg : g.left < g.right) : (shapePorts g).Nodup := by
  cases g <;> simp only [Group.left, Group.right] at hg <;>
    simp only [shapePorts, List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      or_false, and_true, not_or, not_false_eq_true] <;> omega

private def pageWord (p : Page) : List ℕ := p.groups.flatMap shapePorts

private theorem page_port_bound {p : Page} (hp : p.Valid) (i : p.Index) {k : ℕ}
    (hk : k ∈ (p.group i).ports) : k < p.portCount := by
  have hb := hp.bounded i
  cases hg : p.group i <;> simp only [hg, Group.left, Group.right, Group.ports,
    Finset.mem_insert, Finset.mem_singleton] at hk hb <;> omega

private theorem pageWord_nodup {p : Page} (hp : p.Valid) : (pageWord p).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro g hg
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
    apply shapePorts_nodup
    simpa only [Page.group, hi] using (hp.bounded i).1
  · apply List.pairwise_iff_get.mpr
    intro i j hij
    apply List.disjoint_left.mpr
    intro k hi hj
    have hi' : k ∈ (p.group i).ports := (mem_shapePorts _ k).mp hi
    have hj' : k ∈ (p.group j).ports := (mem_shapePorts _ k).mp hj
    have he := (hp.partition k (page_port_bound hp i hi')).unique hi' hj'
    exact (ne_of_lt hij) he

private theorem pageWord_perm {p : Page} (hp : p.Valid) : (pageWord p).Perm (List.range p.portCount) := by
  apply (List.perm_ext_iff_of_nodup (pageWord_nodup hp) List.nodup_range).mpr
  intro k
  rw [List.mem_range]
  constructor
  · intro hk
    obtain ⟨g, hg, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
    apply page_port_bound hp i
    simpa only [Page.group, hi] using (mem_shapePorts g k).mp hk
  · intro hk
    obtain ⟨i, hi, _⟩ := hp.partition k hk
    exact List.mem_flatMap.mpr ⟨p.group i, List.get_mem p.groups i, (mem_shapePorts _ _).mpr hi⟩

/-- Both actual page words enumerate every declared port exactly once. -/
structure PortInventory (l : PortLayout) : Prop where
  upper : (l.upperPairs.flatMap pairPorts).Perm (List.range l.portCount)
  lower : (l.lowerGroups.flatMap groupPorts).Perm (List.range l.portCount)

/-- Standard page validity supplies the literal upper and labelled lower inventories. -/
theorem inventory_of_pages {l : PortLayout} (hl : l.pages.Valid) : PortInventory l := by
  constructor
  · have he : pageWord l.pages.upperPage = l.upperPairs.flatMap pairPorts := by
      simp only [pageWord, PortLayout.pages, Pages.upperPage, List.flatMap_map]
      rfl
    rw [← he]
    exact pageWord_perm hl.upper
  · have he : pageWord l.pages.lowerPage = l.lowerGroups.flatMap groupPorts := by
      simp only [pageWord, PortLayout.pages, Pages.lowerPage, List.flatMap_map]
      apply List.flatMap_congr
      intro g _
      cases g <;> rfl
    rw [← he]
    exact pageWord_perm hl.lower

private theorem shared_lower {l : PortLayout} (hl : PortInventory l) {g k : LowerGroup}
    (hg : g ∈ l.lowerGroups) (hk : k ∈ l.lowerGroups) {i : ℕ}
    (hi : i ∈ groupPorts g) (hj : i ∈ groupPorts k) : g = k := by
  have hnodup := hl.lower.nodup_iff.mpr List.nodup_range
  have hdisjoint := (List.nodup_flatMap.mp hnodup).2
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp hg
  obtain ⟨b, hb⟩ := List.mem_iff_get.mp hk
  by_cases he : a = b
  · exact ha.symm.trans ((congrArg (fun x => l.lowerGroups.get x) he).trans hb)
  rcases lt_or_gt_of_ne he with hab | hba
  · have hd := List.pairwise_iff_get.mp hdisjoint a b hab
    apply False.elim
    exact List.disjoint_left.mp hd (ha.symm ▸ hi) (hb.symm ▸ hj)
  · have hd := List.pairwise_iff_get.mp hdisjoint b a hba
    apply False.elim
    exact List.disjoint_left.mp hd (hb.symm ▸ hj) (ha.symm ▸ hi)

/-- The actual finite lower inventory makes both boundaries of every gate safe. -/
theorem inventory_gate_boundary_safe {l : PortLayout} (hl : PortInventory l)
    {kind : Shuttle.Kind} {first : ℕ} (hg : LowerGroup.gate kind first ∈ l.lowerGroups) :
    SafeCut l first ∧ SafeCut l (first + 3) := by
  constructor
  · intro other start hs
    by_cases h : first ≤ start
    · exact Or.inl h
    apply Or.inr
    by_contra hbad
    have he := shared_lower hl hg hs (i := first)
      (by simp [groupPorts]) (by simp [groupPorts]; omega)
    cases he
    omega
  · intro other start hs
    by_cases h : first + 3 ≤ start
    · exact Or.inl h
    apply Or.inr
    by_contra hbad
    have he := shared_lower hl hg hs (i := start)
      (by simp [groupPorts]; omega) (by simp [groupPorts])
    cases he
    omega

/-- Both actual gate boundaries lie in the declared port interval. -/
theorem inventory_gate_bound {l : PortLayout} (hl : PortInventory l)
    {kind : Shuttle.Kind} {first : ℕ} (hg : LowerGroup.gate kind first ∈ l.lowerGroups) :
    first + 3 ≤ l.portCount := by
  have hm : first + 2 ∈ l.lowerGroups.flatMap groupPorts :=
    List.mem_flatMap.mpr ⟨_, hg, by simp [groupPorts]⟩
  have h := List.mem_range.mp (hl.lower.mem_iff.mp hm)
  omega

/-- Standard valid pages give safe boundaries for their actual labelled gate triples. -/
theorem gate_boundary_safe {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) :
    SafeCut l first ∧ SafeCut l (first + 3) := inventory_gate_boundary_safe (inventory_of_pages hl) hg

/-- A two-port insertion preserves the exact port word of the expanded interval. -/
theorem shift_range_perm (cut n : ℕ) (hc : cut ≤ n) :
    ((List.range n).map (shift cut) ++ [cut, cut + 1]).Perm (List.range (n + 2)) := by
  have hnodup : ((List.range n).map (shift cut) ++ [cut, cut + 1]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.Nodup.map (shift_injective cut) List.nodup_range, ?_, ?_⟩
    · simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil, or_false,
        and_true, not_false_eq_true]
      omega
    · intro a ha b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb
      · exact fun he => shift_ne_cut cut i (he.trans hb)
      · exact fun he => shift_ne_cut_succ cut i (he.trans hb)
  apply (List.perm_ext_iff_of_nodup hnodup List.nodup_range).mpr
  intro k
  have he := congrArg (fun s : Finset ℕ => k ∈ s) (shift_range cut n hc)
  simpa only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] using he.to_iff

/-- The actual ear keeps both page partitions, including every original incidence once. -/
theorem ear_inventory {l : PortLayout} (hl : PortInventory l) (cut : ℕ) (ab : ℕ × ℕ)
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) (hp : ab ∈ l.upperPairs) :
    PortInventory (ear l cut ab) := by
  have hr := shift_range_perm cut l.portCount hc
  constructor
  · exact (ear_upper_ports l cut ab hp).trans ((hl.upper.map (shift cut)).append_right _ |>.trans hr)
  · rw [ear_lower_ports l cut ab hs]
    exact ((hl.lower.map (shift cut)).append_right _).trans hr

end PushPuzzle.Push.Partner
