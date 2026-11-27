/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSourceOrder
public import PushS.CombLower
import all PushS.CombTopology
import all PushS.CombLower
import all PushS.CombUpperPartition
import all PushS.CombCore

/-! Inserting the actual adjacent rotation ears preserves the source contour's noncrossing. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private def Crosses (rank : Token → ℕ) (p q : Token × Token) : Prop :=
  min (rank p.1) (rank p.2) < min (rank q.1) (rank q.2) ∧
    min (rank q.1) (rank q.2) < max (rank p.1) (rank p.2) ∧
    max (rank p.1) (rank p.2) < max (rank q.1) (rank q.2)

private theorem pairwise_idxOf_lt_iff {xs : List Token} {rank : Token → ℕ}
    (ho : xs.Pairwise (fun a b => rank a < rank b)) {a b : Token}
    (ha : a ∈ xs) (hb : b ∈ xs) : xs.idxOf a < xs.idxOf b ↔ rank a < rank b := by
  have hforward {x y : Token} (hx : x ∈ xs) (hy : y ∈ xs)
      (hxy : xs.idxOf x < xs.idxOf y) : rank x < rank y := by
    have hh := List.pairwise_iff_getElem.mp ho _ _
      (List.idxOf_lt_length_of_mem hx) (List.idxOf_lt_length_of_mem hy) hxy
    simpa only [List.getElem_idxOf] using hh
  refine ⟨hforward ha hb, ?_⟩
  intro hab
  rcases lt_trichotomy (xs.idxOf a) (xs.idxOf b) with h | h | h
  · exact h
  · have he := (List.idxOf_inj ha).mp h
    subst b
    omega
  · have hh := hforward hb ha h
    omega

private theorem sourcePair_isSource (width : ℕ) (input : Input) {p : Token × Token}
    (hp : p ∈ sourcePairs width input) : p.1.isSource = true ∧ p.2.isSource = true := by
  obtain ⟨re, _, hp⟩ := List.mem_flatMap.mp hp
  have hmem (t : Token) (ht : t = p.1 ∨ t = p.2) : t ∈ edgeVisits width input.drawing re.2 := by
    rw [← edgeVisits_pairOff_tokens width input.drawing re.2]
    exact List.mem_flatMap.mpr ⟨p, hp, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using ht⟩
  have hsource (t : Token) (ht : t ∈ edgeVisits width input.drawing re.2) : t.isSource = true := by
    rcases (edgeVisits_mem width input.drawing re.2 t).mp ht with rfl | rfl | ⟨c, _, _, rfl | rfl⟩ <;> rfl
  exact ⟨hsource _ (hmem _ (Or.inl rfl)), hsource _ (hmem _ (Or.inr rfl))⟩

private theorem sourcePair_mem_upper (width : ℕ) (input : Input) {p : Token × Token}
    (hp : p ∈ sourcePairs width input) : p ∈ (cut width input).upper :=
  List.mem_append_left _ hp

private theorem core_upper_contiguous (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    {p : Token × Token} : p ∈ (coreTemplate vertex ports).upper →
      ∃ before after, (coreTemplate vertex ports).order = before ++ [p.1, p.2] ++ after := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;> intro hp <;> simp only [List.mem_singleton, List.not_mem_nil] at hp
  · subst p
    exact ⟨[ta, tb, tc], [], rfl⟩
  · subst p
    exact ⟨[], [ta, tb, tc], rfl⟩

private theorem vertex_upper_contiguous (width : ℕ) (input : Input) (vertex : ℕ)
    {p : Token × Token} (hp : p ∈ (vertexBlock width input vertex).upper) :
    ∃ before after, (vertexBlock width input vertex).order = before ++ [p.1, p.2] ++ after := by
  obtain ⟨before, after, horder⟩ := core_upper_contiguous vertex (fan width input vertex) hp
  refine ⟨(toothCrossings width input.drawing vertex).map (fun c => c.token false) ++ before,
    after ++ (toothCrossings width input.drawing vertex).reverse.map (fun c => c.token true), ?_⟩
  change _ ++ (coreTemplate vertex (fan width input vertex)).order ++ _ = _
  rw [horder]
  simp only [List.append_assoc]

private theorem cut_ear_contiguous (width : ℕ) (input : Input) {p : Token × Token}
    (hp : p ∈ ((vertexOrder width input.drawing).map fun sv => vertexBlock width input sv.2).flatMap Block.upper) :
    ∃ before after, (cut width input).order = before ++ [p.1, p.2] ++ after := by
  let blocks := (vertexOrder width input.drawing).map fun sv => vertexBlock width input sv.2
  change p ∈ blocks.flatMap Block.upper at hp
  obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
  have hlocal : ∃ before after, b.order = before ++ [p.1, p.2] ++ after := by
    obtain ⟨sv, _, rfl⟩ := List.mem_map.mp hb
    exact vertex_upper_contiguous width input sv.2 hp
  change ∃ before after, blocks.flatMap Block.order = before ++ [p.1, p.2] ++ after
  exact flatMap_contiguous Block.order hb hlocal

private theorem adjacent_pair_ranks {c : Cut} (hn : c.order.Nodup) {a b : Token}
    {before after : List Token} (ht : c.order = before ++ [a, b] ++ after) :
    c.rank b = c.rank a + 1 := by
  have ha : before.length < c.order.length := by
    simp only [ht, List.length_append, List.length_cons, List.length_nil]
    omega
  have hb : before.length + 1 < c.order.length := by
    simp only [ht, List.length_append, List.length_cons, List.length_nil]
    omega
  have hia := hn.idxOf_getElem before.length ha
  have hib := hn.idxOf_getElem (before.length + 1) hb
  have hh := And.intro hia hib
  have he : c.rank a = before.length ∧ c.rank b = before.length + 1 := by
    simpa [ht, List.getElem_append, Cut.rank] using hh
  omega

variable (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
  (hcount : input.drawing.1.length = input.graph.vertices.length)
  (hedges : input.drawing.2.length = input.graph.edgeCount)

include hg hcount hedges

private theorem sourcePair_mem_order {p : Token × Token} (hp : p ∈ sourcePairs width input) :
    p.1 ∈ sourceOrder width input ∧ p.2 ∈ sourceOrder width input := by
  have hm := cut_upper_pair_mem width input hg hcount hedges (sourcePair_mem_upper width input hp)
  have hs := sourcePair_isSource width input hp
  exact ⟨List.mem_filter.mpr ⟨hm.1, hs.1⟩, List.mem_filter.mpr ⟨hm.2, hs.2⟩⟩

/-- An empty actual vertex array emits no source fragments in the contour. -/
theorem sourceNoncrossing_of_drawing_empty (hempty : input.drawing.1 = []) :
    SourceNoncrossing width input := by
  have hv : vertexOrder width input.drawing = [] := List.length_eq_zero_iff.mp (by
    simpa only [prepare, List.length_map, List.length_zipIdx, hempty, List.length_nil] using
      (vertexOrder_perm width input.drawing).length_eq)
  have ho : (cut width input).order = [] := by simp only [cut, hv, List.map_nil, List.flatMap_nil]
  dsimp only [SourceNoncrossing]
  intro p hp
  have hm := (cut_upper_pair_mem width input hg hcount hedges (sourcePair_mem_upper width input hp)).1
  rw [ho] at hm
  exact False.elim (List.not_mem_nil hm)

omit hedges in
private theorem sourceOrder_rank_lt_iff {a b : Token}
    (ha : a ∈ sourceOrder width input) (hb : b ∈ sourceOrder width input) :
    (sourceOrder width input).idxOf a < (sourceOrder width input).idxOf b ↔
      (cut width input).rank a < (cut width input).rank b := by
  exact pairwise_idxOf_lt_iff
    ((rank_pairwise _ (cut_order_nodup width input hg hcount)).filter Token.isSource) ha hb

private theorem source_pairs_not_cross (hnc : SourceNoncrossing width input)
    {p q : Token × Token} (hp : p ∈ sourcePairs width input) (hq : q ∈ sourcePairs width input) :
    ¬Crosses (cut width input).rank p q := by
  have hm := sourcePair_mem_order width input hg hcount hedges hp
  have hn := sourcePair_mem_order width input hg hcount hedges hq
  have hab := sourceOrder_rank_lt_iff width input hg hcount hm.1 hm.2
  have hba := sourceOrder_rank_lt_iff width input hg hcount hm.2 hm.1
  have hac := sourceOrder_rank_lt_iff width input hg hcount hm.1 hn.1
  have had := sourceOrder_rank_lt_iff width input hg hcount hm.1 hn.2
  have hbc := sourceOrder_rank_lt_iff width input hg hcount hm.2 hn.1
  have hbd := sourceOrder_rank_lt_iff width input hg hcount hm.2 hn.2
  have hca := sourceOrder_rank_lt_iff width input hg hcount hn.1 hm.1
  have hcb := sourceOrder_rank_lt_iff width input hg hcount hn.1 hm.2
  have hda := sourceOrder_rank_lt_iff width input hg hcount hn.2 hm.1
  have hdb := sourceOrder_rank_lt_iff width input hg hcount hn.2 hm.2
  have hcd := sourceOrder_rank_lt_iff width input hg hcount hn.1 hn.2
  have hdc := sourceOrder_rank_lt_iff width input hg hcount hn.2 hn.1
  have hh := hnc p hp q hq
  dsimp only at hh
  unfold Crosses
  omega

private theorem upper_pairs_not_cross (hnc : SourceNoncrossing width input)
    {p q : Token × Token} (hp : p ∈ (cut width input).upper) (hq : q ∈ (cut width input).upper) :
    ¬Crosses (cut width input).rank p q := by
  have hn := cut_order_nodup width input hg hcount
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hq with hq | hq
    · exact source_pairs_not_cross width input hg hcount hedges hnc hp hq
    · obtain ⟨before, after, horder⟩ := cut_ear_contiguous width input hq
      have hh := adjacent_pair_ranks hn horder
      unfold Crosses
      omega
  · obtain ⟨before, after, horder⟩ := cut_ear_contiguous width input hp
    have hh := adjacent_pair_ranks hn horder
    unfold Crosses
    omega

omit hg hcount hedges in
private theorem endpoints_mem_ports (g : PageLevels.Group) : g.left ∈ g.ports ∧ g.right ∈ g.ports := by
  cases g <;> simp [PageLevels.Group.left, PageLevels.Group.right, PageLevels.Group.ports]

/-- The actual source nonalternation and adjacent local ears give the complete original upper page. -/
theorem compile_upper_valid_of_sourceNoncrossing (hnc : SourceNoncrossing width input) :
    (compile width input).pages.upperPage.Valid where
  bounded := compile_upper_bounded width input hg hcount hedges
  partition := compile_upper_partition width input hg hcount hedges
  noncrossing i j hij := by
    let page := (compile width input).pages.upperPage
    have hbi := compile_upper_bounded width input hg hcount hedges i
    have hbj := compile_upper_bounded width input hg hcount hedges j
    change (page.group i).left < (page.group i).right ∧ (page.group i).right < page.portCount at hbi
    change (page.group j).left < (page.group j).right ∧ (page.group j).right < page.portCount at hbj
    have hmi := endpoints_mem_ports (page.group i)
    have hmj := endpoints_mem_ports (page.group j)
    have hshared {k : ℕ} (hk : k < page.portCount)
        (hi : k ∈ (page.group i).ports) (hj : k ∈ (page.group j).ports) : False := by
      obtain ⟨owner, _, howner⟩ := compile_upper_partition width input hg hcount hedges k hk
      exact hij ((howner i hi).trans (howner j hj).symm)
    have hll : (page.group i).left ≠ (page.group j).left := by
      intro he
      exact hshared (hbi.1.trans hbi.2) hmi.1 (he ▸ hmj.1)
    have hlr : (page.group i).left ≠ (page.group j).right := by
      intro he
      exact hshared (hbi.1.trans hbi.2) hmi.1 (he ▸ hmj.2)
    have hrl : (page.group i).right ≠ (page.group j).left := by
      intro he
      exact hshared hbi.2 hmi.2 (he ▸ hmj.1)
    let c := cut width input
    let a : Fin c.upper.length := ⟨i.val, by simpa only [compile, Cut.toLayout, PortLayout.pages,
      PageLevels.Pages.upperPage, List.length_map] using i.isLt⟩
    let b : Fin c.upper.length := ⟨j.val, by simpa only [compile, Cut.toLayout, PortLayout.pages,
      PageLevels.Pages.upperPage, List.length_map] using j.isLt⟩
    have hi : page.group i = .wire (min (c.rank (c.upper.get a).1) (c.rank (c.upper.get a).2))
        (max (c.rank (c.upper.get a).1) (c.rank (c.upper.get a).2)) := upper_pair_at c i
    have hj : page.group j = .wire (min (c.rank (c.upper.get b).1) (c.rank (c.upper.get b).2))
        (max (c.rank (c.upper.get b).1) (c.rank (c.upper.get b).2)) := upper_pair_at c j
    have hcross := upper_pairs_not_cross width input hg hcount hedges hnc
      (List.get_mem c.upper a) (List.get_mem c.upper b)
    have hreverse := upper_pairs_not_cross width input hg hcount hedges hnc
      (List.get_mem c.upper b) (List.get_mem c.upper a)
    change ¬Crosses c.rank (c.upper.get a) (c.upper.get b) at hcross
    change ¬Crosses c.rank (c.upper.get b) (c.upper.get a) at hreverse
    change (page.group i).right < (page.group j).left ∨
      (page.group j).right < (page.group i).left ∨
      (page.group i).Contains (page.group j) ∨ (page.group j).Contains (page.group i)
    simp only [hi, hj, PageLevels.Group.left, PageLevels.Group.right, PageLevels.Group.Contains]
      at hbi hbj hll hlr hrl ⊢
    dsimp only [Crosses] at hcross hreverse
    omega

/-- The actual complete two-page layout follows from its original source-fragment nonalternation. -/
theorem compile_pages_valid_of_sourceNoncrossing (hnc : SourceNoncrossing width input) :
    (compile width input).pages.Valid where
  upper := compile_upper_valid_of_sourceNoncrossing width input hg hcount hedges hnc
  lower := compile_lower_valid width input hg hcount
  upper_wire i := by
    change ∃ a b, (cut width input).toLayout.pages.upperPage.group i = .wire a b
    rw [upper_pair_at (cut width input) i]
    exact ⟨_, _, rfl⟩

end PushPuzzle.PushS.Comb
