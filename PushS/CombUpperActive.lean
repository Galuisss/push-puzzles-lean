/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombUpperWindows
public import PushS.CombLowerActive
public import PushS.StripSourceWindowCounts
import all PushS.CombUpperPartition
import all PushS.CombNumbering
import all PushS.PageLevels
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Fixed active upper-arc and highest-level bounds for the actual native strip compiler. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

variable (width : ℕ) (g : NCL.AndOrGraph) (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)

include hg in
private theorem native_token_owner {token : Token}
    (ht : token ∈ (cut width ⟨g, drawing.orthogonalDrawing⟩).order) :
    ∃ vertex : Fin g.vertices.length, token ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ vertex.val).order := by
  obtain ⟨v, hv, _⟩ := cut_token_block_unique width ⟨g, drawing.orthogonalDrawing⟩ hg (StripSource.drawing_count drawing) ht
  exact ⟨⟨v.val, by simpa only [StripSource.drawing_count] using v.isLt⟩, hv⟩

include hg in
private theorem upper_left_injective : Function.Injective (fun i : (compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.Index =>
    ((compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.group i).left) := by
  intro i j he
  dsimp only at he
  have hcount := StripSource.drawing_count drawing
  have hedges : drawing.orthogonalDrawing.2.length = g.edgeCount := List.length_ofFn
  have hb := compile_upper_bounded width ⟨g, drawing.orthogonalDrawing⟩ hg hcount hedges i
  obtain ⟨_, _, hu⟩ := compile_upper_partition width ⟨g, drawing.orthogonalDrawing⟩ hg hcount hedges _ (hb.1.trans hb.2)
  exact (hu i (PageLevels.Group.left_mem_ports _)).trans
    (hu j (by
      change ((compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.group i).left ∈
        ((compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.group j).ports
      rw [he]
      exact PageLevels.Group.left_mem_ports _)).symm

include hg in
/-- Each active upper pair's left owner lies within one source span of the current cut's original row. -/
theorem compile_upper_active_near (height span : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height)
    (hwin : ∀ edge, ∃ start : ℕ, ∀ p ∈ support (drawing.path edge).unitRoute,
      0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span)
    (k : ℕ) (hk : k < (compile width ⟨g, drawing.orthogonalDrawing⟩).portCount)
    (current : Fin g.vertices.length)
    (hcurrent : (cut width ⟨g, drawing.orthogonalDrawing⟩).order[k] ∈
      (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ current.val).order)
    (i : (compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.Index)
    (hi : i ∈ (compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.active k) :
    ∃ (owner : Fin g.vertices.length) (left : Token),
      left ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ owner.val).order ∧
        ((compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.group i).left =
          (cut width ⟨g, drawing.orthogonalDrawing⟩).rank left ∧
        (drawing.vertex current).2 ≤ (drawing.vertex owner).2 + span ∧
          (drawing.vertex owner).2 ≤ (drawing.vertex current).2 + span := by
  let input : Input := ⟨g, drawing.orthogonalDrawing⟩
  let c := cut width input
  let j : Fin c.upper.length := ⟨i.val, by
    simpa only [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.upperPage, List.length_map] using i.isLt⟩
  let pair := c.upper.get j
  have hp : pair ∈ c.upper := List.get_mem _ j
  have hcount := StripSource.drawing_count drawing
  have hedges : drawing.orthogonalDrawing.2.length = g.edgeCount := List.length_ofFn
  have hmem := cut_upper_pair_mem width input hg hcount hedges hp
  obtain ⟨a, ha⟩ := native_token_owner width g hg drawing hmem.1
  obtain ⟨b, hb⟩ := native_token_owner width g hg drawing hmem.2
  obtain ⟨start, hwa, hwb⟩ := upper_pair_owner_window width g hg drawing height span hfit hwin pair hp a b ha hb
  have hcut : c.rank c.order[k] = k := (cut_order_nodup width input hg hcount).idxOf_getElem k hk
  have hgroup := upper_pair_at c i
  have hleft : ((compile width input).pages.upperPage.group i).left = min (c.rank pair.1) (c.rank pair.2) := by
    change (c.toLayout.pages.upperPage.group i).left = _
    rw [hgroup]
    rfl
  have hright : ((compile width input).pages.upperPage.group i).right = max (c.rank pair.1) (c.rank pair.2) := by
    change (c.toLayout.pages.upperPage.group i).right = _
    rw [hgroup]
    rfl
  have hactive := (Finset.mem_filter.mp hi).2
  rw [hleft, hright] at hactive
  by_cases hab : c.rank pair.1 ≤ c.rank pair.2
  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab] at hactive
    have hac := native_block_row_mono width g hg drawing height hfit a current ha hcurrent (by rw [hcut]; exact hactive.1)
    have hcb := native_block_row_mono width g hg drawing height hfit current b hcurrent hb (by rw [hcut]; exact hactive.2.le)
    exact ⟨a, pair.1, ha, hleft.trans (Nat.min_eq_left hab), by omega, by omega⟩
  · have hba : c.rank pair.2 ≤ c.rank pair.1 := by omega
    rw [Nat.min_eq_right hba, Nat.max_eq_left hba] at hactive
    have hbc := native_block_row_mono width g hg drawing height hfit b current hb hcurrent (by rw [hcut]; exact hactive.1)
    have hca := native_block_row_mono width g hg drawing height hfit current a hcurrent ha (by rw [hcut]; exact hactive.2.le)
    exact ⟨b, pair.2, hb, hleft.trans (Nat.min_eq_right hba), by omega, by omega⟩

private def nearby_ports (center span : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun v : Fin g.vertices.length =>
    center ≤ (drawing.vertex v).2 + span ∧ (drawing.vertex v).2 ≤ center + span).biUnion fun v =>
      ((vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ v.val).order.map
        (cut width ⟨g, drawing.orthogonalDrawing⟩).rank).toFinset

private theorem nearby_ports_card_le (height center span : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height)
    (hpanel : ∀ panel, Nat.card {v // panel ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ panel + 1} ≤ 1) :
    (nearby_ports width g drawing center span).card ≤ (2 * span + 1) * (4 * width + 7) := by
  let vertices := Finset.univ.filter fun v : Fin g.vertices.length =>
    center ≤ (drawing.vertex v).2 + span ∧ (drawing.vertex v).2 ≤ center + span
  have hv : vertices.card ≤ 2 * span + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, vertices] using
      StripSource.vertex_neighborhood_card_le drawing hpanel center span
  have hb (v : Fin g.vertices.length) :
      (((vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ v.val).order.map
        (cut width ⟨g, drawing.orthogonalDrawing⟩).rank).toFinset).card ≤ 4 * width + 7 := by
    have hc := List.toFinset_card_le ((vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ v.val).order.map
      (cut width ⟨g, drawing.orthogonalDrawing⟩).rank)
    rw [List.length_map] at hc
    exact hc.trans (vertexBlock_feature_bounds width height ⟨g, drawing.orthogonalDrawing⟩ drawing.isPlanarOrthogonalDrawing hfit v.val).1
  exact (Finset.card_biUnion_le_card_mul vertices _ (4 * width + 7) (fun v _ => hb v)).trans
    (Nat.mul_le_mul_right (4 * width + 7) hv)

include hg in
/-- Actual upper-page active groups have a constant budget from the original strip width and whole-edge span. -/
theorem compile_upper_maxActive_le (height span : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height)
    (hwin : ∀ edge, ∃ start : ℕ, ∀ p ∈ support (drawing.path edge).unitRoute,
      0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span)
    (hpanel : ∀ panel, Nat.card {v // panel ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ panel + 1} ≤ 1) :
    (compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.maxActive ≤ (2 * span + 1) * (4 * width + 7) := by
  unfold PageLevels.Page.maxActive
  apply Finset.sup_le
  intro k hk
  have hk' : k < (compile width ⟨g, drawing.orthogonalDrawing⟩).portCount := by
    have hh := Finset.mem_range.mp hk
    change k < (compile width ⟨g, drawing.orthogonalDrawing⟩).portCount - 1 at hh
    omega
  obtain ⟨current, hcurrent⟩ := native_token_owner width g hg drawing (List.getElem_mem hk')
  have hmap : Set.MapsTo (fun i => ((compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.group i).left)
      ((compile width ⟨g, drawing.orthogonalDrawing⟩).pages.upperPage.active k)
      (nearby_ports width g drawing (drawing.vertex current).2 span) := by
    intro i hi
    obtain ⟨owner, left, hl, he, hn⟩ := compile_upper_active_near width g hg drawing height span hfit hwin k hk' current hcurrent i hi
    exact Finset.mem_biUnion.mpr ⟨owner, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨left, hl, he.symm⟩)⟩
  have hcard := Finset.card_le_card_of_injOn _ hmap (fun _ _ _ _ he => upper_left_injective width g hg drawing he)
  exact hcard.trans (nearby_ports_card_le width g drawing height (drawing.vertex current).2 span hfit hpanel)

include hg in
/-- The actual unmodified comb compiler has fixed highest working level on the original bounded strip family. -/
theorem compile_highest_le (height span : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height)
    (hwin : ∀ edge, ∃ start : ℕ, ∀ p ∈ support (drawing.path edge).unitRoute,
      0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span)
    (hpanel : ∀ panel, Nat.card {v // panel ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ panel + 1} ≤ 1) :
    (compile width ⟨g, drawing.orthogonalDrawing⟩).pages.highest ≤ 2 * ((2 * span + 1) * (4 * width + 7)) := by
  have hu := compile_upper_maxActive_le width g hg drawing height span hfit hwin hpanel
  have hl := compile_lower_maxActive_le width ⟨g, drawing.orthogonalDrawing⟩ hg (StripSource.drawing_count drawing)
    height drawing.isPlanarOrthogonalDrawing hfit
  have hh := PageLevels.Pages.highest_le (compile width ⟨g, drawing.orthogonalDrawing⟩).pages
  have hb : 4 * width + 7 ≤ (2 * span + 1) * (4 * width + 7) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (4 * width + 7) (show 1 ≤ 2 * span + 1 by omega)
  omega

end PushPuzzle.PushS.Comb

namespace PushPuzzle.PushS.StripSource

/-- The actual graph and complete strip geometry give a fixed compiler level budget for every configuration input. -/
theorem validDrawing_highest_le {width span : ℕ} {x : Instance} (hg : NCL.SourceValid x.ncl.graph)
    (hd : PushPuzzle.NCL.StripAndOrNCL.ValidDrawing width span x) :
    (layout width x).pages.highest ≤ 2 * ((2 * span + 1) * (4 * width + 7)) := by
  obtain ⟨drawing, he, _, hwin, hpanel, _, _⟩ := hd
  obtain ⟨height, hfit⟩ := drawingFits drawing hg hwin
  have h := Comb.compile_highest_le width x.ncl.graph hg drawing height span hfit hwin hpanel
  simpa only [layout, toComb, he] using h

/-- The same actual PSPACE-hard strip inputs retain that width/span compiler level budget. -/
theorem layout_highest_le {width span : ℕ} {x : Instance} (hx : x ∈ language width span) :
    (layout width x).pages.highest ≤ 2 * ((2 * span + 1) * (4 * width + 7)) :=
  validDrawing_highest_le (NCL.SourceValid.ofValid hx.1.1 hx.2.1) hx.2.2

end PushPuzzle.PushS.StripSource
