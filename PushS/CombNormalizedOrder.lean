/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNormalizedCores
import all PushS.CombNormalizedConfiguration
import all PushS.CombPartition

/-!
# Actual global contour ranks of the normalized directions

Flatten the same original vertex blocks with their actual normalized local values. Their token
projection is the original complete contour, and their value projection is the emitted array.
The existing native contour uniqueness therefore gives exact readout at every actual port rank.

## Main results

* `Comb.ConfigurationInput.normalizedAxes_rank`: exact local normalized value at the original
  actual global contour rank.
-/

public section

namespace PushPuzzle.PushS.Comb


open Cslib.Orthogonal

private def entries (width : ℕ) (x : ConfigurationInput) : List (Token × Bool) :=
  (vertexOrder width x.input.drawing).flatMap fun sv =>
    (vertexBlock width x.input sv.2).order.map fun token =>
      (token, x.normalizedTokenBit width sv.2 token)

private theorem entries_tokens (width : ℕ) (x : ConfigurationInput) :
    (entries width x).map Prod.fst = (cut width x.input).order := by
  simp only [entries, List.map_flatMap, List.map_map, Function.comp_def, cut,
    List.flatMap_map, List.map_id']

private theorem entries_bits (width : ℕ) (x : ConfigurationInput) :
    (entries width x).map Prod.snd = x.normalizedAxes width := by
  simp only [entries, List.map_flatMap, List.map_map, Function.comp_def,
    ConfigurationInput.normalizedAxes, CoreQuery.axes, ConfigurationInput.normalizedTokenBit]

private theorem getD_entry (es : List (Token × Bool)) (hn : (es.map Prod.fst).Nodup)
    {token : Token} {bit : Bool} (he : (token, bit) ∈ es) :
    (es.map Prod.snd).getD ((es.map Prod.fst).idxOf token) false = bit := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
  have hib : i.val < (es.map Prod.fst).length := by simpa only [List.length_map] using i.isLt
  have hf : (es.map Prod.fst)[i.val]'hib = token := by
    simpa only [List.getElem_map, List.get_eq_getElem] using congrArg Prod.fst hi
  have hx := hn.idxOf_getElem i.val hib
  rw [hf] at hx
  rw [hx, List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt)]
  simpa only [List.getElem_map, List.get_eq_getElem] using congrArg Prod.snd hi

/-- The actual global contour rank reads exactly the normalized value of its original vertex block.
-/
theorem ConfigurationInput.normalizedAxes_rank (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length) {token : Token}
    (ht : token ∈ (vertexBlock width x.input vertex).order) :
    (x.normalizedAxes width).getD ((cut width x.input).rank token) false =
      x.normalizedTokenBit width vertex token := by
  have hv' : vertex < x.input.drawing.1.length := by omega
  have hm : vertex ∈ (prepare width x.input.drawing).1.zipIdx.map Prod.snd := by
    rw [List.zipIdx_map_snd]
    simpa only [prepare, List.length_map, ← List.range_eq_range'] using List.mem_range.mpr hv'
  have hp := (vertexOrder_perm width x.input.drawing).map Prod.snd
  obtain ⟨sv, hsv, hvx⟩ := List.mem_map.mp (hp.mem_iff.mpr hm)
  have he : (token, x.normalizedTokenBit width vertex token) ∈ entries width x := by
    apply List.mem_flatMap.mpr
    refine ⟨sv, hsv, ?_⟩
    rw [hvx]
    exact List.mem_map.mpr ⟨token, ht, rfl⟩
  have hn : ((entries width x).map Prod.fst).Nodup := by
    rw [entries_tokens]
    exact cut_order_nodup width x.input hg hcount
  have hr := getD_entry _ hn he
  rw [entries_tokens, entries_bits] at hr
  exact hr

private theorem block_witness (width : ℕ) (input : Input)
    (hcount : input.drawing.1.length = input.graph.vertices.length) {token : Token}
    (ht : token ∈ (cut width input).order) :
    ∃ vertex, vertex < input.graph.vertices.length ∧
      token ∈ (vertexBlock width input vertex).order := by
  simp only [cut, List.flatMap_map] at ht
  obtain ⟨sv, hsv, ht⟩ := List.mem_flatMap.mp ht
  have hv := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hsv)
  refine ⟨sv.2, ?_, ht⟩
  simpa only [prepare, List.length_map, hcount, Nat.add_zero] using hv

/-- A listed native tip that supplied the upper page still supplies it at its same global rank. -/
theorem ConfigurationInput.normalizedAxis_tip_true (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (edge : ℕ) (dir : Bool) (ht : Token.tip edge dir ∈ (cut width x.input).order)
    (hb : x.tokenBit width (.tip edge dir) = true) :
    (x.normalizedAxes width).getD ((cut width x.input).rank (.tip edge dir)) false = true := by
  obtain ⟨vertex, hv, hm⟩ := block_witness width x.input hcount ht
  rw [x.normalizedAxes_rank width hg hcount hv hm]
  exact x.normalized_tip_true width vertex edge dir hb

/-- A listed genuine crossing side retains its exact original direction at its global rank. -/
theorem ConfigurationInput.normalizedAxis_mark (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (edge slot tooth : ℕ) (side : Bool)
    (ht : Token.mark edge slot tooth side ∈ (cut width x.input).order) :
    (x.normalizedAxes width).getD ((cut width x.input).rank (.mark edge slot tooth side)) false =
      x.tokenBit width (.mark edge slot tooth side) := by
  obtain ⟨vertex, hv, hm⟩ := block_witness width x.input hcount ht
  rw [x.normalizedAxes_rank width hg hcount hv hm, x.normalized_mark width vertex]

/-- A listed rotation retains its own actual original vertex context at the same global rank. -/
theorem ConfigurationInput.normalizedAxis_rotation (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (vertex : ℕ) (side : Bool)
    (ht : Token.rotation vertex side ∈ (cut width x.input).order) :
    (x.normalizedAxes width).getD ((cut width x.input).rank (.rotation vertex side)) false =
      x.normalizedTokenBit width vertex (.rotation vertex side) := by
  obtain ⟨owner, hv, hm⟩ := block_witness width x.input hcount ht
  have he := vertexBlock_rotation_owner width x.input hm
  subst owner
  exact x.normalizedAxes_rank width hg hcount hv hm

end PushPuzzle.PushS.Comb
