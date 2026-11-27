/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNormalizedLocal
public import PushS.CombUpperPartition
public import PushS.PortInputLegal

/-!
# Ordered native inputs of the complete actual normalized contour

The same source direction vector supplies every actual upper fragment, every local rotation,
every tooth wire, and every original core. Read their normalized local values at the same actual
global contour ranks and retain the existing numerical port layout.

## Main results

* `Comb.ConfigurationInput.normalizedAxes_orderedInputs`: original native legality gives legal
  and ordered inputs of the same actual compiled two-page layout.
-/

public section

namespace PushPuzzle.PushS.Comb


open Cslib.Orthogonal

private theorem vertex_bound (width : ℕ) (input : Input)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {sv : Point × ℕ} (hv : sv ∈ vertexOrder width input.drawing) :
    sv.2 < input.graph.vertices.length := by
  have h := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hv)
  simpa only [prepare, List.length_map, hcount, Nat.add_zero] using h

private theorem lower_owner (width : ℕ) (input : Input)
    (hcount : input.drawing.1.length = input.graph.vertices.length) {group : TokenGroup}
    (hg : group ∈ (cut width input).lower) :
    ∃ vertex, vertex < input.graph.vertices.length ∧
      group ∈ (vertexBlock width input vertex).lower := by
  simp only [cut, List.flatMap_map] at hg
  obtain ⟨sv, hsv, hg⟩ := List.mem_flatMap.mp hg
  exact ⟨sv.2, vertex_bound width input hcount hsv, hg⟩

private theorem lower_token (width : ℕ) (input : Input) (vertex : ℕ)
    {group : TokenGroup} (hg : group ∈ (vertexBlock width input vertex).lower)
    {token : Token} (ht : token ∈ group.tokens) :
    token ∈ (vertexBlock width input vertex).order :=
  (vertexBlock_lower_perm width input vertex).mem_iff.mp (List.mem_flatMap.mpr ⟨group, hg, ht⟩)

private theorem minmax_supply (value : ℕ → Bool) (bit : Bool) (a b : ℕ)
    (h : value a = bit ∨ value b = bit) : value (min a b) = bit ∨ value (max a b) = bit := by
  rcases le_total a b with hab | hba
  · simpa only [Nat.min_eq_left hab, Nat.max_eq_right hab] using h
  · simpa only [Nat.min_eq_right hba, Nat.max_eq_left hba] using h.symm

private theorem fragment_token_true (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    {edge : ℕ} {token : Token} (hv : token ∈ edgeVisits width x.input.drawing edge)
    (ht : token ∈ (cut width x.input).order) (hb : x.tokenBit width token = true) :
    (x.normalizedAxes width).getD ((cut width x.input).rank token) false = true := by
  cases token with
  | tip e dir => exact x.normalizedAxis_tip_true width hg hcount e dir ht hb
  | mark e slot tooth side =>
    rw [x.normalizedAxis_mark width hg hcount e slot tooth side ht]
    exact hb
  | rotation vertex inside =>
    have hm := (edgeVisits_mem width x.input.drawing edge (.rotation vertex inside)).mp hv
    simp only [Crossing.token, reduceCtorEq, or_false, and_false, exists_false] at hm

private theorem upper_supply (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    {a b : Token} (hu : (a, b) ∈ (cut width x.input).upper) :
    (x.normalizedAxes width).getD ((cut width x.input).rank a) false = true ∨
      (x.normalizedAxes width).getD ((cut width x.input).rank b) false = true := by
  have hm := cut_upper_pair_mem width x.input hg hcount hedges hu
  have hparts := hu
  simp only [cut, List.flatMap_map] at hparts
  rcases List.mem_append.mp hparts with hf | hr
  · obtain ⟨re, _, hp⟩ := List.mem_flatMap.mp hf
    have ha : a ∈ edgeVisits width x.input.drawing re.2 := by
      rw [← edgeVisits_pairOff_tokens width x.input.drawing re.2]
      exact List.mem_flatMap.mpr ⟨(a, b), hp, by simp⟩
    have hb : b ∈ edgeVisits width x.input.drawing re.2 := by
      rw [← edgeVisits_pairOff_tokens width x.input.drawing re.2]
      exact List.mem_flatMap.mpr ⟨(a, b), hp, by simp⟩
    rcases x.upperFragment_supplied width re.2 hp with hab | hab
    · exact .inl (fragment_token_true width x hg hcount ha hm.1 hab)
    · exact .inr (fragment_token_true width x hg hcount hb hm.2 hab)
  · obtain ⟨sv, _, hp⟩ := List.mem_flatMap.mp hr
    have hs : x.normalizedTokenBit width sv.2 (.rotation sv.2 true) = true ∨
        x.normalizedTokenBit width sv.2 (.rotation sv.2 false) = true := by
      have hside := x.normalized_rotation_sides width sv.2
      cases hb : x.normalizedTokenBit width sv.2 (.rotation sv.2 true)
      · right
        rw [hside, hb]
        rfl
      · exact .inl rfl
    rcases vertexBlock_upper_shape width x.input sv.2 hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [x.normalizedAxis_rotation width hg hcount sv.2 true hm.1,
        x.normalizedAxis_rotation width hg hcount sv.2 false hm.2]
      exact hs
    · rw [x.normalizedAxis_rotation width hg hcount sv.2 false hm.1,
        x.normalizedAxis_rotation width hg hcount sv.2 true hm.2]
      exact hs.symm

private theorem compiled_upper (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    {a b : ℕ} (hu : (a, b) ∈ (compile width x.input).upperPairs) :
    (x.normalizedAxes width).getD a false = true ∨
      (x.normalizedAxes width).getD b false = true := by
  change (a, b) ∈ (cut width x.input).upper.map _ at hu
  obtain ⟨⟨ta, tb⟩, ht, he⟩ := List.mem_map.mp hu
  cases he
  exact minmax_supply (fun k => (x.normalizedAxes width).getD k false) true
    ((cut width x.input).rank ta) ((cut width x.input).rank tb)
    (upper_supply width x hg hcount hedges ht)

private theorem compiled_wire (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    {a b : ℕ} (hw : .wire a b ∈ (compile width x.input).lowerGroups) :
    (x.normalizedAxes width).getD a false = false ∨
      (x.normalizedAxes width).getD b false = false := by
  change LowerGroup.wire a b ∈ (cut width x.input).lower.map (cut width x.input).lowerGroup at hw
  obtain ⟨group, hg', he⟩ := List.mem_map.mp hw
  cases group with
  | gate kind ta tb tc => cases he
  | wire ta tb =>
    cases he
    obtain ⟨vertex, hv, hl⟩ := lower_owner width x.input hcount hg'
    have ha := lower_token width x.input vertex hl (by simp [TokenGroup.tokens] : ta ∈ _)
    have hb := lower_token width x.input vertex hl (by simp [TokenGroup.tokens] : tb ∈ _)
    have hna := x.normalizedAxes_rank width hg hcount hv ha
    have hnb := x.normalizedAxes_rank width hg hcount hv hb
    apply minmax_supply (fun k => (x.normalizedAxes width).getD k false) false
      ((cut width x.input).rank ta) ((cut width x.input).rank tb)
    rw [hna, hnb]
    exact x.normalizedBlock_wire width hg hv hl

private theorem gate_owner (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {kind : Shuttle.Kind} {first : ℕ}
    (hgate : .gate kind first ∈ (compile width input).lowerGroups) :
    ∃ vertex a b c, vertex < input.graph.vertices.length ∧
      .gate kind a b c ∈ (vertexBlock width input vertex).lower ∧
      first = (cut width input).rank a ∧ (cut width input).rank b = first + 1 ∧
      (cut width input).rank c = first + 2 := by
  change LowerGroup.gate kind first ∈
    (cut width input).lower.map (cut width input).lowerGroup at hgate
  obtain ⟨group, hgroup, he⟩ := List.mem_map.mp hgate
  cases group with
  | wire a b => cases he
  | gate other a b c =>
    change LowerGroup.gate other ((cut width input).rank a) = .gate kind first at he
    obtain ⟨rfl, hr⟩ := LowerGroup.gate.inj he
    obtain ⟨vertex, hv, hl⟩ := lower_owner width input hcount hgroup
    obtain ⟨hb, hc⟩ := cut_gate_ranks width input hg hcount hgroup
    exact ⟨vertex, a, b, c, hv, hl, hr.symm, by omega, by omega⟩

private theorem gate_readout (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    {kind : Shuttle.Kind} {first : ℕ}
    (hgate : .gate kind first ∈ (compile width x.input).lowerGroups) :
    ∃ vertex a b c, vertex < x.input.graph.vertices.length ∧
      .gate kind a b c ∈ (vertexBlock width x.input vertex).lower ∧
      (x.normalizedAxes width).getD first false = x.normalizedTokenBit width vertex a ∧
      (x.normalizedAxes width).getD (first + 1) false = x.normalizedTokenBit width vertex b ∧
      (x.normalizedAxes width).getD (first + 2) false = x.normalizedTokenBit width vertex c := by
  obtain ⟨vertex, a, b, c, hv, hl, hf, hb, hc⟩ := gate_owner width x.input hg hcount hgate
  have haT := lower_token width x.input vertex hl (by simp [TokenGroup.tokens] : a ∈ _)
  have hbT := lower_token width x.input vertex hl (by simp [TokenGroup.tokens] : b ∈ _)
  have hcT := lower_token width x.input vertex hl (by simp [TokenGroup.tokens] : c ∈ _)
  refine ⟨vertex, a, b, c, hv, hl, ?_, ?_, ?_⟩
  · rw [hf]
    exact x.normalizedAxes_rank width hg hcount hv haT
  · rw [← hb]
    exact x.normalizedAxes_rank width hg hcount hv hbT
  · rw [← hc]
    exact x.normalizedAxes_rank width hg hcount hv hcT

private theorem compiled_and (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    {first : ℕ} (hgate : .gate .andGate first ∈ (compile width x.input).lowerGroups) :
    ((x.normalizedAxes width).getD (first + 2) false = false ∨
      ((x.normalizedAxes width).getD first false = false ∧
        (x.normalizedAxes width).getD (first + 1) false = false)) ∧
      ((x.normalizedAxes width).getD (first + 1) false = false →
        (x.normalizedAxes width).getD first false = false) := by
  obtain ⟨vertex, a, b, c, hv, hl, ha, hb, hc⟩ := gate_readout width x hg hcount hgate
  rw [ha, hb, hc]
  exact x.normalizedBlock_andGate width hg hs hv hl

private theorem compiled_or (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    {first : ℕ} (hgate : .gate .orGate first ∈ (compile width x.input).lowerGroups) :
    (x.normalizedAxes width).getD first false = false ∨
      (x.normalizedAxes width).getD (first + 1) false = false ∨
        (x.normalizedAxes width).getD (first + 2) false = false := by
  obtain ⟨vertex, a, b, c, hv, hl, ha, hb, hc⟩ := gate_readout width x hg hcount hgate
  rw [ha, hb, hc]
  exact x.normalizedBlock_orGate width hg hs hv hl

/-- The original legal native configuration emits legal and ordered inputs on the same actual
compiled contour, with every real upper/lower group checked in its original numbered position. -/
theorem ConfigurationInput.normalizedAxes_orderedInputs (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph)
    (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount) :
    (compile width x.input).OrderedInputs (x.normalizedAxes width) where
  toInputLegal :=
    { axes_length := length_normalizedAxes width x
      upper := fun _ _ h => compiled_upper width x hg hcount hedges h
      lower_wire := fun _ _ h => compiled_wire width x hg hcount h
      or_gate := fun _ h => compiled_or width x hg hs hcount h
      and_gate := fun _ h => (compiled_and width x hg hs hcount h).1 }
  and_ordered := fun _ h => (compiled_and width x hg hs hcount h).2

end PushPuzzle.PushS.Comb
