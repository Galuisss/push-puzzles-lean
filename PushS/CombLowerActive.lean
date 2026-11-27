/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombBlockRanks
public import PushS.CombFeatureBounds
import all PushS.CombLower
import all PushS.CombNumbering
import all PushS.CombTopology

/-! A fixed active-group budget for the actual compiled lower page. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

variable (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
  (hcount : input.drawing.1.length = input.graph.vertices.length)

private theorem lower_group_block (group : TokenGroup) (hm : group ∈ (cut width input).lower) :
    ∃ vertex : Fin input.drawing.1.length,
      group.firstToken ∈ (vertexBlock width input vertex.val).order ∧
        group.lastToken ∈ (vertexBlock width input vertex.val).order := by
  have hm' : group ∈ (vertexOrder width input.drawing).flatMap fun sv => (vertexBlock width input sv.2).lower := by
    simpa only [cut, List.flatMap_map] using hm
  obtain ⟨sv, hsv, hgroup⟩ := List.mem_flatMap.mp hm'
  have hv : sv.2 < input.drawing.1.length := by
    have h := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hsv)
    simpa only [prepare, List.length_map, Nat.add_zero] using h
  exact ⟨⟨sv.2, hv⟩, (vertex_lower_trace width input sv.2).endpoints hgroup⟩

include hg hcount

private theorem lower_interval_block (i : (compile width input).pages.lowerPage.Index) :
    ∃ (vertex : Fin input.drawing.1.length) (left right : Token),
      left ∈ (vertexBlock width input vertex.val).order ∧ right ∈ (vertexBlock width input vertex.val).order ∧
        ((compile width input).pages.lowerPage.group i).left = (cut width input).rank left ∧
          ((compile width input).pages.lowerPage.group i).right = (cut width input).rank right := by
  let c := cut width input
  let j : Fin c.lower.length := ⟨i.val, by
    simpa only [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.lowerPage, List.length_map] using i.isLt⟩
  have hm := List.get_mem c.lower j
  obtain ⟨vertex, hl, hr⟩ := lower_group_block width input (c.lower.get j) hm
  have hinterval := lower_interval width input hg hcount hm
  refine ⟨vertex, (c.lower.get j).firstToken, (c.lower.get j).lastToken, hl, hr, ?_, ?_⟩
  · change (c.toLayout.pages.lowerPage.group i).left = _
    rw [lower_group_at c i]
    exact congrArg Prod.fst hinterval
  · change (c.toLayout.pages.lowerPage.group i).right = _
    rw [lower_group_at c i]
    exact congrArg Prod.snd hinterval

/-- Every active lower group has its left port in the original block containing the current contour cut. -/
theorem compile_lower_active_local (k : ℕ) (hk : k < (compile width input).portCount)
    (vertex : Fin input.drawing.1.length)
    (hvertex : (cut width input).order[k] ∈ (vertexBlock width input vertex.val).order)
    (i : (compile width input).pages.lowerPage.Index) (hi : i ∈ (compile width input).pages.lowerPage.active k) :
    ((compile width input).pages.lowerPage.group i).left ∈
      ((vertexBlock width input vertex.val).order.map (cut width input).rank).toFinset := by
  obtain ⟨owner, left, right, hl, hr, hleft, hright⟩ := lower_interval_block width input hg hcount i
  have hcut : (cut width input).rank (cut width input).order[k] = k :=
    (cut_order_nodup width input hg hcount).idxOf_getElem k hk
  have hactive : ((compile width input).pages.lowerPage.group i).left ≤ k ∧
      k < ((compile width input).pages.lowerPage.group i).right := (Finset.mem_filter.mp hi).2
  have he := cut_rank_block_between width input hg hcount owner vertex hl hr hvertex
    (by rw [hcut, ← hleft]; exact hactive.1) (by rw [hcut, ← hright]; exact hactive.2.le)
  subst owner
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨left, hl, hleft.symm⟩)

/-- Actual lower-page active groups have a uniform budget depending only on the supplied strip width. -/
theorem compile_lower_maxActive_le (height : ℕ) {G : Graph}
    (hd : G.IsPlanarOrthogonalDrawing input.drawing) (hfit : Graph.drawingFits input.drawing width height) :
    (compile width input).pages.lowerPage.maxActive ≤ 4 * width + 7 := by
  unfold PageLevels.Page.maxActive
  apply Finset.sup_le
  intro k hk
  have hk' : k < (compile width input).portCount := by
    have hh := Finset.mem_range.mp hk
    change k < (compile width input).portCount - 1 at hh
    omega
  obtain ⟨vertex, hvertex, _⟩ := cut_port_block_unique width input hg hcount k hk'
  let ports := ((vertexBlock width input vertex.val).order.map (cut width input).rank).toFinset
  have hmap : Set.MapsTo (fun i => ((compile width input).pages.lowerPage.group i).left)
      ((compile width input).pages.lowerPage.active k) ports := by
    intro i hi
    exact compile_lower_active_local width input hg hcount k hk' vertex hvertex i hi
  have hcard := Finset.card_le_card_of_injOn _ hmap (fun _ _ _ _ he =>
    (compile_lower_valid width input hg hcount).left_injective he)
  have hp : ports.card ≤ (vertexBlock width input vertex.val).order.length := by
    simpa only [ports, List.length_map] using List.toFinset_card_le ((vertexBlock width input vertex.val).order.map (cut width input).rank)
  exact hcard.trans (hp.trans (vertexBlock_feature_bounds width height input hd hfit vertex.val).1)

end PushPuzzle.PushS.Comb
