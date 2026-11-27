/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSourceWindows
public import PushS.CombBlockRanks
public import PushS.CombUpperPartition
import all PushS.CombPreprocess
import all PushS.CombCrossingGeometry
import all PushS.CombTopology

/-! Actual upper-pair endpoints and their intervening contour cuts share a bounded source window. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

private theorem vertex_upper_pair_mem (width : ℕ) (input : Input) (vertex : ℕ) (pair : Token × Token)
    (hp : pair ∈ (vertexBlock width input vertex).upper) :
    pair.1 ∈ (vertexBlock width input vertex).order ∧ pair.2 ∈ (vertexBlock width input vertex).order := by
  change pair ∈ (coreTemplate vertex (fan width input vertex)).upper at hp
  have hcore : pair.1 ∈ (coreTemplate vertex (fan width input vertex)).order ∧
      pair.2 ∈ (coreTemplate vertex (fan width input vertex)).order := by
    unfold coreTemplate at hp ⊢
    dsimp only at hp ⊢
    split_ifs at hp ⊢ <;> simp only [List.mem_singleton, List.not_mem_nil] at hp <;> subst pair <;> simp
  exact ⟨List.mem_append_left _ (List.mem_append_right _ hcore.1),
    List.mem_append_left _ (List.mem_append_right _ hcore.2)⟩

variable (width : ℕ) (g : NCL.AndOrGraph) (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)

include hg in
/-- Comparing actual native contour ranks compares the original longitudinal rows of their block owners. -/
theorem native_block_row_mono (height : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height)
    (a b : Fin g.vertices.length) {ta tb : Token}
    (ha : ta ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ a.val).order)
    (hb : tb ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ b.val).order)
    (hab : (cut width ⟨g, drawing.orthogonalDrawing⟩).rank ta ≤ (cut width ⟨g, drawing.orthogonalDrawing⟩).rank tb) :
    (drawing.vertex a).2 ≤ (drawing.vertex b).2 := by
  let da : Fin drawing.orthogonalDrawing.1.length := ⟨a.val, by rw [StripSource.drawing_count]; exact a.isLt⟩
  let db : Fin drawing.orthogonalDrawing.1.length := ⟨b.val, by rw [StripSource.drawing_count]; exact b.isLt⟩
  have hc := cut_rank_block_column_mono width ⟨g, drawing.orthogonalDrawing⟩ hg (StripSource.drawing_count drawing)
    height drawing.isPlanarOrthogonalDrawing hfit da db ha hb hab
  have sa : drawing.orthogonalDrawing.1.getD a.val (0, 0) = NCL.GridDrawing.integerPoint (drawing.vertex a) := List.getD_ofFn _ a _
  have sb : drawing.orthogonalDrawing.1.getD b.val (0, 0) = NCL.GridDrawing.integerPoint (drawing.vertex b) := List.getD_ofFn _ b _
  change ((prepare width drawing.orthogonalDrawing).1.getD a.val (0, 0)).1 ≤
    ((prepare width drawing.orthogonalDrawing).1.getD b.val (0, 0)).1 at hc
  rw [site_prepare, site_prepare, sa, sb] at hc
  have hxa := hfit.1 _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hxb := hfit.1 _ (List.mem_ofFn.mpr ⟨b, rfl⟩)
  by_contra h
  have hh := point_column_lt width ⟨hxb.1, hxb.2.1⟩ ⟨hxa.1, hxa.2.1⟩
    (show (NCL.GridDrawing.integerPoint (drawing.vertex b)).2 < (NCL.GridDrawing.integerPoint (drawing.vertex a)).2 by
      dsimp only [NCL.GridDrawing.integerPoint]
      exact_mod_cast (show (drawing.vertex b).2 < (drawing.vertex a).2 by omega))
  omega

include hg in
/-- Every actual upper pair's two original block owners share one complete source-span row window. -/
theorem upper_pair_owner_window (height span : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height)
    (hwin : ∀ edge, ∃ start : ℕ, ∀ p ∈ support (drawing.path edge).unitRoute,
      0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span)
    (pair : Token × Token) (hp : pair ∈ (cut width ⟨g, drawing.orthogonalDrawing⟩).upper)
    (a b : Fin g.vertices.length)
    (ha : pair.1 ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ a.val).order)
    (hb : pair.2 ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ b.val).order) :
    ∃ start, (start ≤ (drawing.vertex a).2 ∧ (drawing.vertex a).2 ≤ start + span) ∧
      (start ≤ (drawing.vertex b).2 ∧ (drawing.vertex b).2 ≤ start + span) := by
  have hp' : pair ∈ drawing.orthogonalDrawing.2.zipIdx.flatMap (fun re => pairOff (edgeVisits width drawing.orthogonalDrawing re.2)) ∨
      pair ∈ (vertexOrder width drawing.orthogonalDrawing).flatMap (fun sv => (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ sv.2).upper) := by
    simpa only [cut, List.mem_append, List.flatMap_map] using hp
  rcases hp' with hp | hp
  · obtain ⟨re, hre, hpair⟩ := List.mem_flatMap.mp hp
    let edge : Fin g.edgeCount := ⟨re.2, by
      have h := List.snd_lt_of_mem_zipIdx hre
      simpa only [NCL.GridDrawing.Closed.orthogonalDrawing, List.length_ofFn, Nat.add_zero] using h⟩
    have visits : pair.1 ∈ edgeVisits width drawing.orthogonalDrawing edge.val ∧
        pair.2 ∈ edgeVisits width drawing.orthogonalDrawing edge.val := by
      rw [← edgeVisits_pairOff_tokens]
      exact ⟨List.mem_flatMap.mpr ⟨pair, hpair, by simp⟩, List.mem_flatMap.mpr ⟨pair, hpair, by simp⟩⟩
    obtain ⟨start, hs⟩ := hwin edge
    exact ⟨start, source_token_window_rows width g hg drawing height start span hfit edge hs a visits.1 ha,
      source_token_window_rows width g hg drawing height start span hfit edge hs b visits.2 hb⟩
  · obtain ⟨sv, hsv, hpair⟩ := List.mem_flatMap.mp hp
    have hv : sv.2 < drawing.orthogonalDrawing.1.length := by
      have h := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width drawing.orthogonalDrawing).mem_iff.mp hsv)
      simpa only [prepare, List.length_map, Nat.add_zero] using h
    let v : Fin drawing.orthogonalDrawing.1.length := ⟨sv.2, hv⟩
    let da : Fin drawing.orthogonalDrawing.1.length := ⟨a.val, by rw [StripSource.drawing_count]; exact a.isLt⟩
    let db : Fin drawing.orthogonalDrawing.1.length := ⟨b.val, by rw [StripSource.drawing_count]; exact b.isLt⟩
    have hm := vertex_upper_pair_mem width ⟨g, drawing.orthogonalDrawing⟩ sv.2 pair hpair
    have hcount := StripSource.drawing_count drawing
    have he := cut_rank_block_between width ⟨g, drawing.orthogonalDrawing⟩ hg hcount v da hm.1 hm.1 ha le_rfl le_rfl
    have hf := cut_rank_block_between width ⟨g, drawing.orthogonalDrawing⟩ hg hcount v db hm.2 hm.2 hb le_rfl le_rfl
    have hab : a = b := by
      apply Fin.ext
      change da.val = db.val
      exact congrArg Fin.val (he.symm.trans hf)
    subst b
    exact ⟨(drawing.vertex a).2, ⟨le_rfl, Nat.le_add_right _ _⟩, ⟨le_rfl, Nat.le_add_right _ _⟩⟩

end PushPuzzle.PushS.Comb
