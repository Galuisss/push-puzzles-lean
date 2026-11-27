/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombLower
public import PushS.CombToothOrder
import all PushS.CombLower
import all PushS.CombNumbering
import all PushS.CombToothOrder
import all PushS.CombRouteOrder

/-! Actual contour-port ranks localize to their unique original vertex blocks. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

variable (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
  (hcount : input.drawing.1.length = input.graph.vertices.length)

include hg hcount

private theorem cut_blocks_pairwise :
    (vertexOrder width input.drawing).Pairwise (fun a b =>
      ∀ ta ∈ (vertexBlock width input a.2).order, ∀ tb ∈ (vertexBlock width input b.2).order,
        (cut width input).rank ta < (cut width input).rank tb) := by
  have h := rank_pairwise (cut width input) (cut_order_nodup width input hg hcount)
  have h' : ((vertexOrder width input.drawing).flatMap fun sv => (vertexBlock width input sv.2).order).Pairwise
      (fun a b => (cut width input).rank a < (cut width input).rank b) := by
    simpa only [cut, List.flatMap_map] using h
  exact (List.pairwise_flatMap.mp h').2

/-- Original block order strictly separates every actual port rank in the two blocks. -/
theorem cut_rank_lt_of_block_lt (a b : Fin input.drawing.1.length)
    (hab : vertexRank width input.drawing a.val < vertexRank width input.drawing b.val)
    {ta tb : Token} (ha : ta ∈ (vertexBlock width input a.val).order)
    (hb : tb ∈ (vertexBlock width input b.val).order) :
    (cut width input).rank ta < (cut width input).rank tb := by
  obtain ⟨i, hi, hia, _⟩ := ordered_site width input.drawing a.isLt
  obtain ⟨j, hj, hjb, _⟩ := ordered_site width input.drawing b.isLt
  have hij : i < j := by change i.val < j.val; omega
  have h := List.pairwise_iff_get.mp (cut_blocks_pairwise width input hg hcount) i j hij
  rw [hia, hjb] at h
  exact h ta ha tb hb

/-- Comparing actual port ranks compares the corresponding original vertex-block ranks. -/
theorem cut_rank_block_mono (a b : Fin input.drawing.1.length)
    {ta tb : Token} (ha : ta ∈ (vertexBlock width input a.val).order)
    (hb : tb ∈ (vertexBlock width input b.val).order)
    (hab : (cut width input).rank ta ≤ (cut width input).rank tb) :
    vertexRank width input.drawing a.val ≤ vertexRank width input.drawing b.val := by
  by_contra h
  have hh := cut_rank_lt_of_block_lt width input hg hcount b a (by omega) hb ha
  omega

/-- Any contour port between two ports of one original block belongs to that same block. -/
theorem cut_rank_block_between (owner current : Fin input.drawing.1.length) {left right token : Token}
    (hl : left ∈ (vertexBlock width input owner.val).order) (hr : right ∈ (vertexBlock width input owner.val).order)
    (ht : token ∈ (vertexBlock width input current.val).order)
    (hlt : (cut width input).rank left ≤ (cut width input).rank token)
    (htr : (cut width input).rank token ≤ (cut width input).rank right) : owner = current := by
  have hle := cut_rank_block_mono width input hg hcount owner current hl ht hlt
  have hge := cut_rank_block_mono width input hg hcount current owner ht hr htr
  exact Fin.ext (vertexRank_injective width input.drawing owner.isLt (Nat.le_antisymm hle hge))

/-- Every genuine contour token belongs to one unique original vertex block. -/
theorem cut_token_block_unique {token : Token} (ht : token ∈ (cut width input).order) :
    ∃! vertex : Fin input.drawing.1.length, token ∈ (vertexBlock width input vertex.val).order := by
  have hnodup : ((vertexOrder width input.drawing).flatMap fun sv => (vertexBlock width input sv.2).order).Nodup := by
    simpa only [cut, List.flatMap_map] using cut_order_nodup width input hg hcount
  have hmem : token ∈ (vertexOrder width input.drawing).flatMap (fun sv => (vertexBlock width input sv.2).order) := by
    simpa only [cut, List.flatMap_map] using ht
  obtain ⟨i, hi, hu⟩ := unique_flatMap_index _ _ hnodup hmem
  have hv : ((vertexOrder width input.drawing).get i).2 < input.drawing.1.length := by
    have h := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp
      (List.get_mem (vertexOrder width input.drawing) i))
    simpa only [prepare, List.length_map, Nat.add_zero] using h
  refine ⟨⟨_, hv⟩, hi, ?_⟩
  intro vertex hvertex
  obtain ⟨j, _, hj, _⟩ := ordered_site width input.drawing vertex.isLt
  have htj : token ∈ (vertexBlock width input ((vertexOrder width input.drawing).get j).2).order := by
    rw [hj]
    exact hvertex
  have hji := hu j htj
  apply Fin.ext
  rw [← hj, hji]

/-- Any actual numbered contour port has that same unique original block owner. -/
theorem cut_port_block_unique (k : ℕ) (hk : k < (cut width input).order.length) :
    ∃! vertex : Fin input.drawing.1.length,
      (cut width input).order[k] ∈ (vertexBlock width input vertex.val).order :=
  cut_token_block_unique width input hg hcount (List.getElem_mem hk)

/-- Contour-port order preserves the actual prepared column order of its original block owners. -/
theorem cut_rank_block_column_mono (height : ℕ) {G : Graph}
    (hd : G.IsPlanarOrthogonalDrawing input.drawing) (hfit : Graph.drawingFits input.drawing width height)
    (a b : Fin input.drawing.1.length) {ta tb : Token}
    (ha : ta ∈ (vertexBlock width input a.val).order) (hb : tb ∈ (vertexBlock width input b.val).order)
    (hab : (cut width input).rank ta ≤ (cut width input).rank tb) :
    ((prepare width input.drawing).1.getD a.val (0, 0)).1 ≤
      ((prepare width input.drawing).1.getD b.val (0, 0)).1 := by
  have hr := cut_rank_block_mono width input hg hcount a b ha hb hab
  by_contra h
  have hh := (vertexRank_column_lt_iff width height hd hfit b.isLt a.isLt).mpr (by omega)
  omega

end PushPuzzle.PushS.Comb
