/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNumbering
import all PushS.CombTopology
import all PushS.CombNumbering

/-! The actual lower page is a concatenation of nested tooth brackets and contiguous cores. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private inductive LowerTrace : List Token → List TokenGroup → Prop
  | nil : LowerTrace [] []
  | gate (kind : Shuttle.Kind) (a b c : Token) :
      LowerTrace [a, b, c] [.gate kind a b c]
  | wrap {order : List Token} {groups : List TokenGroup} (trace : LowerTrace order groups)
      (a b : Token) : LowerTrace (a :: order ++ [b]) (.wire a b :: groups)
  | append {left right : List Token} {leftGroups rightGroups : List TokenGroup}
      (hl : LowerTrace left leftGroups) (hr : LowerTrace right rightGroups) :
      LowerTrace (left ++ right) (leftGroups ++ rightGroups)

private theorem core_lower_trace (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) :
    LowerTrace (coreTemplate vertex ports).order (coreTemplate vertex ports).lower := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs
  · exact (LowerTrace.gate kind tb tc inside).wrap ta outside
  · exact (LowerTrace.gate kind inside ta tb).wrap outside tc
  · exact LowerTrace.gate kind ta tb tc

private theorem tooth_lower_trace (hits : List Crossing) {order : List Token} {groups : List TokenGroup}
    (ht : LowerTrace order groups) :
    LowerTrace (hits.map (fun c => c.token false) ++ order ++ hits.reverse.map (fun c => c.token true))
      (hits.map (fun c => .wire (c.token false) (c.token true)) ++ groups) := by
  induction hits with
  | nil => simpa only [List.map_nil, List.reverse_nil, List.nil_append, List.append_nil] using ht
  | cons c hits ih =>
    simpa only [List.map_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.append_assoc] using ih.wrap (c.token false) (c.token true)

private theorem vertex_lower_trace (width : ℕ) (input : Input) (vertex : ℕ) :
    LowerTrace (vertexBlock width input vertex).order (vertexBlock width input vertex).lower :=
  tooth_lower_trace _ (core_lower_trace vertex (fan width input vertex))

private theorem cut_lower_trace (width : ℕ) (input : Input) :
    LowerTrace (cut width input).order (cut width input).lower := by
  simp only [cut, List.flatMap_map]
  induction vertexOrder width input.drawing with
  | nil => exact .nil
  | cons sv order ih => exact (vertex_lower_trace width input sv.2).append ih

private def TokenGroup.firstToken : TokenGroup → Token
  | .wire a _ | .gate _ a _ _ => a

private def TokenGroup.lastToken : TokenGroup → Token
  | .wire _ b | .gate _ _ _ b => b

private theorem LowerTrace.endpoints {order : List Token} {groups : List TokenGroup}
    (ht : LowerTrace order groups) {g : TokenGroup} (hg : g ∈ groups) :
    g.firstToken ∈ order ∧ g.lastToken ∈ order := by
  induction ht with
  | nil => cases hg
  | gate kind a b c =>
    simp only [List.mem_singleton] at hg
    subst g
    simp [TokenGroup.firstToken, TokenGroup.lastToken]
  | @wrap order groups ht a b ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [TokenGroup.firstToken, TokenGroup.lastToken]
    · obtain ⟨hf, hl⟩ := ih hg
      exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hf),
        List.mem_cons_of_mem _ (List.mem_append_left _ hl)⟩
  | append hl hr ihl ihr =>
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨hf, hl⟩ := ihl hg
      exact ⟨List.mem_append_left _ hf, List.mem_append_left _ hl⟩
    · obtain ⟨hf, hl⟩ := ihr hg
      exact ⟨List.mem_append_right _ hf, List.mem_append_right _ hl⟩

private def NestedIntervals (a b : ℕ × ℕ) : Prop :=
  a.2 < b.1 ∨ b.2 < a.1 ∨ (a.1 ≤ b.1 ∧ b.2 ≤ a.2) ∨ (b.1 ≤ a.1 ∧ a.2 ≤ b.2)

private def TokenGroup.interval (rank : Token → ℕ) (g : TokenGroup) : ℕ × ℕ :=
  (rank g.firstToken, rank g.lastToken)

private theorem LowerTrace.laminar {order : List Token} {groups : List TokenGroup}
    (ht : LowerTrace order groups) (rank : Token → ℕ)
    (ho : order.Pairwise (fun a b => rank a < rank b))
    {g h : TokenGroup} (hg : g ∈ groups) (hh : h ∈ groups) :
    NestedIntervals (g.interval rank) (h.interval rank) := by
  induction ht with
  | nil => cases hg
  | gate kind a b c =>
    simp only [List.mem_singleton] at hg hh
    subst g h
    exact Or.inr (Or.inr (Or.inl ⟨le_rfl, le_rfl⟩))
  | @wrap order groups ht a b ih =>
    have hp := List.pairwise_cons.mp ho
    have ha := hp.1
    have hi := (List.pairwise_append.mp hp.2).1
    have hb := (List.pairwise_append.mp hp.2).2.2
    have hr (k : TokenGroup) (hk : k ∈ groups) :
        rank a < rank k.firstToken ∧ rank k.lastToken < rank b := by
      have hm := ht.endpoints hk
      exact ⟨ha _ (List.mem_append_left _ hm.1), hb _ hm.2 _ (by simp)⟩
    rcases List.mem_cons.mp hg with rfl | hg <;> rcases List.mem_cons.mp hh with rfl | hh
    · exact Or.inr (Or.inr (Or.inl ⟨le_rfl, le_rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨(hr _ hh).1.le, (hr _ hh).2.le⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨(hr _ hg).1.le, (hr _ hg).2.le⟩))
    · exact ih hi hg hh
  | @append left right leftGroups rightGroups hl hr ihl ihr =>
    have hp := List.pairwise_append.mp ho
    rcases List.mem_append.mp hg with hg | hg <;> rcases List.mem_append.mp hh with hh | hh
    · exact ihl hp.1 hg hh
    · exact Or.inl (hp.2.2 _ (hl.endpoints hg).2 _ (hr.endpoints hh).1)
    · exact Or.inr (Or.inl (hp.2.2 _ (hl.endpoints hh).2 _ (hr.endpoints hg).1))
    · exact ihr hp.2.1 hg hh

private theorem LowerTrace.increasing {order : List Token} {groups : List TokenGroup}
    (ht : LowerTrace order groups) (rank : Token → ℕ)
    (ho : order.Pairwise (fun a b => rank a < rank b))
    {g : TokenGroup} (hg : g ∈ groups) : rank g.firstToken < rank g.lastToken := by
  induction ht with
  | nil => cases hg
  | gate kind a b c =>
    have ha := (List.pairwise_cons.mp ho).1
    simp only [List.mem_singleton] at hg
    subst g
    change rank a < rank c
    exact ha _ (by simp)
  | @wrap order groups ht a b ih =>
    have hp := List.pairwise_cons.mp ho
    rcases List.mem_cons.mp hg with rfl | hg
    · change rank a < rank b
      exact hp.1 _ (List.mem_append_right _ (by simp))
    · exact ih (List.pairwise_append.mp hp.2).1 hg
  | append hl hr ihl ihr =>
    rcases List.mem_append.mp hg with hg | hg
    · exact ihl (List.pairwise_append.mp ho).1 hg
    · exact ihr (List.pairwise_append.mp ho).2.1 hg

private theorem rank_pairwise (c : Cut) (hn : c.order.Nodup) :
    c.order.Pairwise (fun a b => c.rank a < c.rank b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  change c.order.idxOf c.order[i] < c.order.idxOf c.order[j]
  simpa only [hn.idxOf_getElem i hi, hn.idxOf_getElem j hj] using hij

private theorem lower_interval (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {g : TokenGroup} (hgroup : g ∈ (cut width input).lower) :
    (((cut width input).lowerGroup g).shape.left, ((cut width input).lowerGroup g).shape.right) =
      g.interval (cut width input).rank := by
  have hinc := (cut_lower_trace width input).increasing _
    (rank_pairwise _ (cut_order_nodup width input hg hcount)) hgroup
  cases g with
  | wire a b =>
    change (min _ _, max _ _) = (_, _)
    change (cut width input).rank a < (cut width input).rank b at hinc
    rw [Nat.min_eq_left hinc.le, Nat.max_eq_right hinc.le]
    rfl
  | gate kind a b c =>
    have hc := (cut_gate_ranks width input hg hcount hgroup).2
    exact Prod.ext rfl hc.symm

private theorem lower_nested (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {g h : TokenGroup} (hgm : g ∈ (cut width input).lower) (hhm : h ∈ (cut width input).lower) :
    NestedIntervals
      (((cut width input).lowerGroup g).shape.left, ((cut width input).lowerGroup g).shape.right)
      (((cut width input).lowerGroup h).shape.left, ((cut width input).lowerGroup h).shape.right) := by
  rw [lower_interval width input hg hcount hgm, lower_interval width input hg hcount hhm]
  exact (cut_lower_trace width input).laminar _
    (rank_pairwise _ (cut_order_nodup width input hg hcount)) hgm hhm

private theorem group_left_mem (g : PageLevels.Group) : g.left ∈ g.ports := by
  cases g <;> simp [PageLevels.Group.left, PageLevels.Group.ports]

/-- The actual lower groups are nested or disjoint in their literal emitted port order. -/
theorem compile_lower_noncrossing (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (i j : (compile width input).pages.lowerPage.Index) (hij : i ≠ j) :
    ((compile width input).pages.lowerPage.group i).right < ((compile width input).pages.lowerPage.group j).left ∨
      ((compile width input).pages.lowerPage.group j).right < ((compile width input).pages.lowerPage.group i).left ∨
      ((compile width input).pages.lowerPage.group i).Contains ((compile width input).pages.lowerPage.group j) ∨
      ((compile width input).pages.lowerPage.group j).Contains ((compile width input).pages.lowerPage.group i) := by
  let c := cut width input
  have hleft : ((compile width input).pages.lowerPage.group i).left ≠
      ((compile width input).pages.lowerPage.group j).left := by
    intro heq
    have hb := compile_lower_bounded width input hg hcount i
    obtain ⟨k, _, hk⟩ := compile_lower_partition width input hg hcount _ (hb.1.trans hb.2)
    have hi := hk i (group_left_mem _)
    have hj := hk j (heq ▸ group_left_mem _)
    exact hij (hi.trans hj.symm)
  change (c.toLayout.pages.lowerPage.group i).left ≠ (c.toLayout.pages.lowerPage.group j).left at hleft
  change (c.toLayout.pages.lowerPage.group i).right < (c.toLayout.pages.lowerPage.group j).left ∨
    (c.toLayout.pages.lowerPage.group j).right < (c.toLayout.pages.lowerPage.group i).left ∨
    (c.toLayout.pages.lowerPage.group i).Contains (c.toLayout.pages.lowerPage.group j) ∨
    (c.toLayout.pages.lowerPage.group j).Contains (c.toLayout.pages.lowerPage.group i)
  rw [lower_group_at c i, lower_group_at c j] at hleft ⊢
  let fi : Fin c.lower.length := ⟨i.val, by
    simpa [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.lowerPage] using i.isLt⟩
  let fj : Fin c.lower.length := ⟨j.val, by
    simpa [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.lowerPage] using j.isLt⟩
  have hh := lower_nested width input hg hcount (List.get_mem c.lower fi) (List.get_mem c.lower fj)
  dsimp only [NestedIntervals] at hh
  rcases hh with hh | hh | hh | hh
  · exact Or.inl hh
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (Or.inl ⟨hh.1, hh.2, Or.inl (lt_of_le_of_ne hh.1 hleft)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hh.1, hh.2, Or.inl (lt_of_le_of_ne hh.1 hleft.symm)⟩))

/-- The native graph's computed lower page satisfies all original page validity fields. -/
theorem compile_lower_valid (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) :
    (compile width input).pages.lowerPage.Valid where
  bounded := compile_lower_bounded width input hg hcount
  partition := compile_lower_partition width input hg hcount
  noncrossing := compile_lower_noncrossing width input hg hcount

end PushPuzzle.PushS.Comb
