/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Partner
public import PushS.PortEndpointIndexing
public import PushS.PortEndpointEnumeration
public import CslibFrontier.Foundations.Data.List.Lookup
import all PushS.PortEndpointIndexing

/-! Actual repaired partners and level parity separate every middle-axis probe row from ordinary gate outer axes. -/

public section
namespace PushPuzzle.Push.AcceptanceProbe

open PushS PushS.PortLayout PageLevels

/-- The level allocator's lower-middle port set is exactly the original lower gate-middle incidences. -/
private theorem mem_middlePorts_iff (l : PortLayout) (k : ℕ) :
    k ∈ l.pages.lowerPage.middlePorts ↔ Partner.Middle l k := by
  simp only [Page.middlePorts, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    have hg : l.pages.lowerPage.group i ∈ l.lowerGroups.map LowerGroup.shape := List.get_mem _ _
    obtain ⟨g, hg, hshape⟩ := List.mem_map.mp hg
    rw [← hshape] at hi
    cases g with
    | wire a b => simp only [LowerGroup.shape, Group.middles, Finset.notMem_empty] at hi
    | gate kind first =>
      simp only [LowerGroup.shape, Group.middles, Finset.mem_singleton] at hi
      exact ⟨kind, first, hg, hi⟩
  · rintro ⟨kind, first, hg, rfl⟩
    have hm : Group.triple first ∈ l.pages.lowerPage.groups := List.mem_map.mpr ⟨_, hg, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine ⟨i, ?_⟩
    change first + 1 ∈ (l.pages.lowerPage.groups.get i).middles
    rw [hi]
    exact Finset.mem_singleton_self _

private theorem upper_level_eq (l : PortLayout) (i : l.pages.upperPage.Index) :
    l.upperLevel i.val = l.pages.upperLevel i := by
  change (List.ofFn l.pages.upperLevel).getD i.val 0 = _
  rw [List.getD_ofFn_of_lt _ i.isLt 0]

private theorem upper_pair_at (l : PortLayout) (i : l.pages.upperPage.Index) :
    ∃ a b, (a, b) ∈ l.upperPairs ∧ l.pages.upperPage.group i = .wire a b := by
  have hm : l.pages.upperPage.group i ∈ l.upperPairs.map (fun ab => Group.wire ab.1 ab.2) := List.get_mem _ _
  obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.mp hm
  exact ⟨a, b, hab, he.symm⟩

/-- Any actual endpoint on an even upper level is middle or belongs to an ordinary lower WIRE. -/
private theorem upper_even_middle_or_wire (l : PortLayout) (hl : l.pages.Valid)
    (hpartners : Partner.ReaderPartners l)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .upper) (heven : e.level % 2 = 0) :
    Partner.Middle l e.port ∨ Partner.Ordinary l e.port := by
  obtain ⟨i, hip, _, _, hlevel, _⟩ := upper_endpoint_owner l hl he hs
  have heveni : l.pages.upperLevel i % 2 = 0 := by
    rw [← upper_level_eq, ← hlevel]
    exact heven
  have hused : l.pages.UsesMiddle i := by
    by_contra hn
    have hodd := l.pages.upperLevel_odd hl hn
    omega
  obtain ⟨k, hkm⟩ := hused
  obtain ⟨hk, hm⟩ := Finset.mem_inter.mp hkm
  obtain ⟨a, b, hab, hgroup⟩ := upper_pair_at l i
  have hmid : Partner.Middle l k := (mem_middlePorts_iff l k).mp hm
  simp only [hgroup, Group.ports, Finset.mem_insert, Finset.mem_singleton] at hk hip
  rcases hip with rfl | rfl <;> rcases hk with rfl | rfl
  · exact Or.inl hmid
  · exact hpartners.right hab hmid
  · exact hpartners.left hab hmid
  · exact Or.inl hmid

/-- Every actual middle incidence lies on an even upper probe level. -/
private theorem upper_middle_even (l : PortLayout) (hl : l.pages.Valid)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .upper) (hmiddle : Partner.Middle l e.port) :
    e.level % 2 = 0 := by
  obtain ⟨i, hip, _, _, hlevel, _⟩ := upper_endpoint_owner l hl he hs
  have hused : l.pages.UsesMiddle i :=
    ⟨e.port, Finset.mem_inter.mpr ⟨hip, (mem_middlePorts_iff l e.port).mpr hmiddle⟩⟩
  rw [hlevel, upper_level_eq]
  exact l.pages.upperLevel_even hused

/-- Select the actual unique upper endpoint of an original finite port. -/
noncomputable def upperEndpoint (l : PortLayout) (hl : l.pages.Valid) (i : Fin l.portCount) : Endpoint :=
  Classical.choose (l.endpoints_upper_exists hl i.isLt)

theorem upperEndpoint_spec (l : PortLayout) (hl : l.pages.Valid) (i : Fin l.portCount) :
    upperEndpoint l hl i ∈ l.endpoints ∧ (upperEndpoint l hl i).side = .upper ∧
      (upperEndpoint l hl i).port = i.val := Classical.choose_spec (l.endpoints_upper_exists hl i.isLt)

/-- The actual upper probe level of each original finite port. -/
noncomputable def level (l : PortLayout) (hl : l.pages.Valid) (i : Fin l.portCount) : ℕ :=
  (upperEndpoint l hl i).level

theorem level_middle_even (l : PortLayout) (hl : l.pages.Valid) (i : Fin l.portCount)
    (hm : Partner.Middle l i.val) : level l hl i % 2 = 0 := by
  obtain ⟨he, hs, hp⟩ := upperEndpoint_spec l hl i
  exact upper_middle_even l hl he hs (hp.symm ▸ hm)

theorem level_even_wire (l : PortLayout) (hl : l.pages.Valid) (hpartners : Partner.ReaderPartners l)
    (i : Fin l.portCount) (heven : level l hl i % 2 = 0) (hm : ¬ Partner.Middle l i.val) :
    Partner.Ordinary l i.val := by
  obtain ⟨he, hs, hp⟩ := upperEndpoint_spec l hl i
  have hclass := upper_even_middle_or_wire l hl hpartners he hs heven
  rw [hp] at hclass
  exact hclass.resolve_left hm

end PushPuzzle.Push.AcceptanceProbe
