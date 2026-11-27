/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPartition

/-! Literal contour positions retain the complete actual lower-page partition. -/

public section
namespace PushPuzzle.PushS.Comb


/-- Every emitted contour token has its actual in-bounds numbered position. -/
theorem Cut.rank_lt (c : Cut) {token : Token} (ht : token ∈ c.order) :
    c.rank token < c.order.length := List.idxOf_lt_length_iff.mpr ht

/-- Two actual contour tokens with the same emitted position coincide. -/
theorem Cut.rank_injective (c : Cut) {a b : Token} (ha : a ∈ c.order)
    (h : c.rank a = c.rank b) : a = b := (List.idxOf_inj ha).mp h

private theorem triple_rank {tokens : List Token} (hn : tokens.Nodup)
    {before after : List Token} {a b c : Token} (ht : tokens = before ++ [a, b, c] ++ after) :
    tokens.idxOf a = before.length ∧ tokens.idxOf b = before.length + 1 ∧
      tokens.idxOf c = before.length + 2 := by
  have ha : before.length < tokens.length := by simp only [ht, List.length_append, List.length_cons, List.length_nil]; omega
  have hb : before.length + 1 < tokens.length := by simp only [ht, List.length_append, List.length_cons, List.length_nil]; omega
  have hc : before.length + 2 < tokens.length := by simp only [ht, List.length_append, List.length_cons, List.length_nil]; omega
  have hia := hn.idxOf_getElem before.length ha
  have hib := hn.idxOf_getElem (before.length + 1) hb
  have hic := hn.idxOf_getElem (before.length + 2) hc
  have hh := And.intro hia (And.intro hib hic)
  simpa [ht, List.getElem_append] using hh

/-- The same computed gate is numbered by three consecutive positions in the actual contour. -/
theorem cut_gate_ranks (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {kind : Shuttle.Kind} {a b c : Token}
    (hgate : .gate kind a b c ∈ (cut width input).lower) :
    (cut width input).rank b = (cut width input).rank a + 1 ∧
      (cut width input).rank c = (cut width input).rank a + 2 := by
  obtain ⟨before, after, horder⟩ := cut_gate_contiguous width input hgate
  have hr := triple_rank (cut_order_nodup width input hg hcount) horder
  exact ⟨by simp only [Cut.rank, hr.1, hr.2.1], by simp only [Cut.rank, hr.1, hr.2.2]⟩

/-- Forgetting the emitted lower gate's label retains precisely its three actual token ranks. -/
theorem cut_lowerGroup_ports (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {group : TokenGroup} (hgroup : group ∈ (cut width input).lower) :
    ((cut width input).lowerGroup group).shape.ports =
      (group.tokens.map (cut width input).rank).toFinset := by
  cases group with
  | wire a b =>
    ext k
    simp [Cut.lowerGroup, LowerGroup.shape, PageLevels.Group.ports, TokenGroup.tokens]
    omega
  | gate kind a b c =>
    obtain ⟨hb, hc⟩ := cut_gate_ranks width input hg hcount hgroup
    simp only [Cut.lowerGroup, LowerGroup.shape, PageLevels.Group.ports, TokenGroup.tokens,
      List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, hb, hc]
    rfl

/-- Every lower-group token belongs to the same complete computed contour. -/
theorem cut_lower_token_mem (width : ℕ) (input : Input) {group : TokenGroup}
    (hg : group ∈ (cut width input).lower) {token : Token} (ht : token ∈ group.tokens) :
    token ∈ (cut width input).order :=
  (cut_lower_tokens_perm width input).mem_iff.mp (List.mem_flatMap.mpr ⟨group, hg, ht⟩)

private theorem unique_flatMap_index {α β : Type} (xs : List α) (f : α → List β)
    (hn : (xs.flatMap f).Nodup) {token : β} (ht : token ∈ xs.flatMap f) :
    ∃! i : Fin xs.length, token ∈ f (xs.get i) := by
  have hp := (List.nodup_flatMap.mp hn).2
  obtain ⟨group, hgroup, htoken⟩ := List.mem_flatMap.mp ht
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hgroup
  refine ⟨i, htoken, ?_⟩
  intro j hj
  rcases lt_trichotomy j i with hji | hji | hij
  · exact False.elim (List.disjoint_left.mp ((List.pairwise_iff_get.mp hp) j i hji) hj htoken)
  · exact hji
  · exact False.elim (List.disjoint_left.mp ((List.pairwise_iff_get.mp hp) i j hij) htoken hj)

/-- Every actual contour token occurs in exactly one indexed lower group. -/
theorem cut_lower_unique (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) {token : Token}
    (ht : token ∈ (cut width input).order) :
    ∃! i : Fin (cut width input).lower.length, token ∈ ((cut width input).lower.get i).tokens := by
  exact unique_flatMap_index _ _ ((cut_lower_tokens_perm width input).nodup_iff.mpr
    (cut_order_nodup width input hg hcount)) ((cut_lower_tokens_perm width input).mem_iff.mpr ht)

/-- Each numbered lower group's ports stay within the literal emitted contour. -/
theorem cut_lowerGroup_port_lt (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {group : TokenGroup} (hgroup : group ∈ (cut width input).lower) {k : ℕ}
    (hk : k ∈ ((cut width input).lowerGroup group).shape.ports) :
    k < (cut width input).order.length := by
  rw [cut_lowerGroup_ports width input hg hcount hgroup] at hk
  obtain ⟨token, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
  exact (cut width input).rank_lt (cut_lower_token_mem width input hgroup ht)

/-- The actual numbered lower groups are nondegenerate intervals inside the emitted contour. -/
theorem cut_lowerGroup_bounded (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {group : TokenGroup} (hgroup : group ∈ (cut width input).lower) :
    ((cut width input).lowerGroup group).shape.left < ((cut width input).lowerGroup group).shape.right ∧
      ((cut width input).lowerGroup group).shape.right < (cut width input).order.length := by
  have hn := (cut_lower_tokens_perm width input).nodup_iff.mpr
    (cut_order_nodup width input hg hcount)
  have hlocal := (List.nodup_flatMap.mp hn).1 group hgroup
  have hr : ((cut width input).lowerGroup group).shape.right ∈
      ((cut width input).lowerGroup group).shape.ports := by
    cases group <;> simp [Cut.lowerGroup, LowerGroup.shape, PageLevels.Group.right, PageLevels.Group.ports]
  refine ⟨?_, cut_lowerGroup_port_lt width input hg hcount hgroup hr⟩
  cases group with
  | wire a b =>
    have hne : a ≠ b := by simpa [TokenGroup.tokens] using hlocal
    have hneq : (cut width input).rank a ≠ (cut width input).rank b := fun he =>
      hne ((cut width input).rank_injective (cut_lower_token_mem width input hgroup (by simp [TokenGroup.tokens])) he)
    simp only [Cut.lowerGroup, LowerGroup.shape, PageLevels.Group.left, PageLevels.Group.right]
    omega
  | gate kind a b c =>
    simp only [Cut.lowerGroup, LowerGroup.shape, PageLevels.Group.left, PageLevels.Group.right]
    omega

private theorem lower_group_at (c : Cut) (i : c.toLayout.pages.lowerPage.Index) :
    c.toLayout.pages.lowerPage.group i =
      (c.lowerGroup (c.lower.get ⟨i.val, by simpa [Cut.toLayout, PortLayout.pages,
        PageLevels.Pages.lowerPage] using i.isLt⟩)).shape := by
  have hi : i.val < c.lower.length := by
    simpa [Cut.toLayout, PortLayout.pages, PageLevels.Pages.lowerPage] using i.isLt
  change ((c.lower.map c.lowerGroup).map LowerGroup.shape)[i.val]'(by simpa using hi) =
    (c.lowerGroup c.lower[i.val]).shape
  simp only [List.getElem_map]

/-- The same actual compiled lower page has bounded, nondegenerate group intervals. -/
theorem compile_lower_bounded (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (i : (compile width input).pages.lowerPage.Index) :
    ((compile width input).pages.lowerPage.group i).left <
        ((compile width input).pages.lowerPage.group i).right ∧
      ((compile width input).pages.lowerPage.group i).right < (compile width input).portCount := by
  change ((cut width input).toLayout.pages.lowerPage.group i).left <
      ((cut width input).toLayout.pages.lowerPage.group i).right ∧
    ((cut width input).toLayout.pages.lowerPage.group i).right < (cut width input).order.length
  rw [lower_group_at (cut width input) i]
  exact cut_lowerGroup_bounded width input hg hcount (List.get_mem _ _)

/-- The actual numbered lower page partitions every emitted port exactly once. -/
theorem compile_lower_partition (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (k : ℕ) (hk : k < (compile width input).portCount) :
    ∃! i : (compile width input).pages.lowerPage.Index,
      k ∈ ((compile width input).pages.lowerPage.group i).ports := by
  let c := cut width input
  have hk' : k < c.order.length := hk
  let token := c.order[k]
  have ht : token ∈ c.order := List.getElem_mem hk'
  have hrank : c.rank token = k := (cut_order_nodup width input hg hcount).idxOf_getElem k hk'
  obtain ⟨i, hi, huniq⟩ := cut_lower_unique width input hg hcount ht
  let j : (compile width input).pages.lowerPage.Index :=
    ⟨i.val, by simpa only [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.lowerPage,
      List.length_map] using i.isLt⟩
  have hj : k ∈ ((compile width input).pages.lowerPage.group j).ports := by
    change k ∈ (c.toLayout.pages.lowerPage.group j).ports
    rw [lower_group_at c j, cut_lowerGroup_ports width input hg hcount (List.get_mem _ _)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨token, hi, hrank⟩)
  refine ⟨j, hj, ?_⟩
  intro j' hj'
  let i' : Fin c.lower.length :=
    ⟨j'.val, by simpa [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.lowerPage] using j'.isLt⟩
  change k ∈ (c.toLayout.pages.lowerPage.group j').ports at hj'
  rw [lower_group_at c j', cut_lowerGroup_ports width input hg hcount (List.get_mem _ _)] at hj'
  obtain ⟨t, hmem, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hj')
  have hteq : t = token := c.rank_injective (cut_lower_token_mem width input (List.get_mem _ _) hmem)
    (heq.trans hrank.symm)
  have heq' : i' = i := huniq i' (hteq ▸ hmem)
  apply Fin.ext
  exact congrArg (fun x : Fin c.lower.length => x.val) heq'

end PushPuzzle.PushS.Comb
