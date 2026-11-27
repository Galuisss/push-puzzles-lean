/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNormalizedOrder
import all PushS.CombCore
import all PushS.CombConfiguration
import all PushS.CombPartition

/-!
# Native normalized inputs of each actual vertex block

Read the actual local gate metadata and retain its ordered native port weights. Every original
local gate therefore receives the normalized legal inputs in its own actual contour positions.

## Main results

* `Comb.ConfigurationInput.normalizedBlock_andGate`: actual AND threshold and light-input order.
* `Comb.ConfigurationInput.normalizedBlock_orGate`: actual OR threshold.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem coreTemplate_gate_metadata (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    {kind : Shuttle.Kind} {a b c : Token} :
    .gate kind a b c ∈ (coreTemplate vertex ports).lower →
      (coreTemplate vertex ports).core.kind = kind ∧
        (coreTemplate vertex ports).core.ports.map Prod.fst = [a, b, c] := by
  unfold coreTemplate
  extract_lets pa pb pc coreKind ta tb tc inside outside
  split_ifs <;> intro hg <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, false_or,
      TokenGroup.gate.injEq, reduceCtorEq] at hg
  all_goals obtain ⟨rfl, rfl, rfl, rfl⟩ := hg; exact ⟨rfl, rfl⟩

private theorem vertexBlock_gate_metadata (width : ℕ) (input : Input) (vertex : ℕ)
    {kind : Shuttle.Kind} {a b c : Token}
    (hg : .gate kind a b c ∈ (vertexBlock width input vertex).lower) :
    (coreBlock width input vertex).core.kind = kind ∧
      (coreBlock width input vertex).core.ports.map Prod.fst = [a, b, c] := by
  change TokenGroup.gate kind a b c ∈ _ ++ _ at hg
  rcases List.mem_append.mp hg with hm | hc
  · obtain ⟨_, _, he⟩ := List.mem_map.mp hm
    cases he
  · exact coreTemplate_gate_metadata vertex (fan width input vertex) hc

private theorem ports_of_tokens_weights {ps : List (Token × (NCL.WeightedPort ℕ))}
    {a b c : Token} {wa wb wc : ℕ}
    (ht : ps.map Prod.fst = [a, b, c]) (hw : ps.map (fun p => p.2.2) = [wa, wb, wc]) :
    ∃ p r s, ps = [(a, ⟨p, wa⟩), (b, ⟨r, wb⟩), (c, ⟨s, wc⟩)] := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at ht
  rcases ht with ⟨⟨_, p, _⟩, _, rfl, rfl, ⟨⟨_, r, _⟩, _, rfl, rfl,
    ⟨⟨_, s, _⟩, _, rfl, rfl, rfl⟩⟩⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hw
  obtain ⟨rfl, rfl, rfl⟩ := hw
  exact ⟨p, r, s, rfl⟩

private theorem core_wire_spec (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    {vertex : ℕ} (hv : vertex < input.graph.vertices.length) {a b : Token}
    (hw : .wire a b ∈ (coreBlock width input vertex).lower) :
    ∃ port weight,
      ((a = incidenceToken port ∧ b = .rotation vertex false) ∨
        (a = .rotation vertex false ∧ b = incidenceToken port)) ∧
      (.rotation vertex true, ⟨port, weight⟩) ∈ (coreBlock width input vertex).core.ports ∧
      incidenceToken port ∉ (coreBlock width input vertex).core.ports.map Prod.fst := by
  obtain ⟨pa, pb, pc, hfan⟩ := List.length_eq_three.mp (fan_length width input hg hv)
  have hn := fan_tips_nodup width input hg hv
  rw [hfan] at hn
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hn
  let kind := if [pa, pb, pc].any (fun p => decide (p.2 = 1)) then
    Shuttle.Kind.andGate else .orGate
  by_cases h₁ : kind = .andGate ∧ pa.2 = 2
  all_goals dsimp only [kind] at h₁
  · have hl : (coreBlock width input vertex).lower =
        [.wire (incidenceToken pa.1) (.rotation vertex false),
          .gate kind (incidenceToken pb.1) (incidenceToken pc.1) (.rotation vertex true)] := by
      simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
      rw [ite_eq_left h₁]
    have hp : (coreBlock width input vertex).core.ports =
        [(incidenceToken pb.1, pb), (incidenceToken pc.1, pc), (.rotation vertex true, pa)] := by
      simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
      rw [ite_eq_left h₁]
    rw [hl] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, TokenGroup.wire.injEq,
      reduceCtorEq, or_false] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨pa.1, pa.2, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
    · rw [hp]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · simp only [hp, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hn.1.1, hn.1.2, by simp [incidenceToken]⟩
  · by_cases h₂ : kind = .andGate ∧ pb.2 = 2
    all_goals dsimp only [kind] at h₂
    · have hl : (coreBlock width input vertex).lower =
          [.wire (.rotation vertex false) (incidenceToken pc.1),
            .gate kind (.rotation vertex true) (incidenceToken pa.1) (incidenceToken pb.1)] := by
        simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right h₁, ite_eq_left h₂]
      have hp : (coreBlock width input vertex).core.ports =
          [(.rotation vertex true, pc), (incidenceToken pa.1, pa), (incidenceToken pb.1, pb)] := by
        simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right h₁, ite_eq_left h₂]
      rw [hl] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, TokenGroup.wire.injEq,
        reduceCtorEq, or_false] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨pc.1, pc.2, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [hp]; exact List.mem_cons_self
      · simp only [hp, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        exact ⟨by simp [incidenceToken], Ne.symm hn.1.2, Ne.symm hn.2.1⟩
    · have hl : (coreBlock width input vertex).lower =
          [.gate kind (incidenceToken pa.1) (incidenceToken pb.1) (incidenceToken pc.1)] := by
        simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right h₁, ite_eq_right h₂]
      rw [hl] at hw
      simp only [List.mem_singleton, reduceCtorEq] at hw

/-- The actual ordinary wire introduced by a core rotation retains a supplied lower endpoint. -/
private theorem ConfigurationInput.normalized_coreWire (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length)
    {a b : Token} (hw : .wire a b ∈ (coreBlock width x.input vertex).lower) :
    x.normalizedTokenBit width vertex a = false ∨ x.normalizedTokenBit width vertex b = false := by
  obtain ⟨port, weight, hends, hp, hnot⟩ := core_wire_spec width x.input hg hv hw
  have ht := x.normalized_not_core width vertex (incidenceToken port) hnot
    (by simp [incidenceToken])
  have htip : x.tokenBit width (incidenceToken port) = x.portBit port := by
    simp only [incidenceToken, ConfigurationInput.tokenBit]
  have hi := x.corePort_bit width hg hv hp
  have hout := x.normalized_rotation_sides width vertex
  have hwire : x.normalizedTokenBit width vertex (incidenceToken port) = false ∨
      x.normalizedTokenBit width vertex (.rotation vertex false) = false := by
    rw [ht, htip]
    cases hb : x.portBit port
    · exact .inl rfl
    · right
      have hin : x.tokenBit width (.rotation vertex true) = true := hi.trans hb
      rw [hout, x.normalized_rotation_true width vertex hin]
      rfl
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hwire
  · exact hwire.symm

/-- Every actual lower ordinary wire in one vertex block retains a supplied endpoint. -/
theorem ConfigurationInput.normalizedBlock_wire (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length)
    {a b : Token} (hw : .wire a b ∈ (vertexBlock width x.input vertex).lower) :
    x.normalizedTokenBit width vertex a = false ∨ x.normalizedTokenBit width vertex b = false := by
  change TokenGroup.wire a b ∈ _ ++ _ at hw
  rcases List.mem_append.mp hw with hm | hc
  · obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
    cases he
    have hcross := (List.mem_filter.mp
      ((toothCrossings_perm width x.input.drawing vertex).mem_iff.mp hc)).1
    simp only [Crossing.token, x.normalized_mark]
    change x.tokenBit width (c.token false) = false ∨ x.tokenBit width (c.token true) = false
    have hsides := x.tokenBit_crossing_sides width hcross
    cases hb : x.tokenBit width (c.token true)
    · exact .inr rfl
    · left
      rw [hsides, hb]
      rfl
  · exact x.normalized_coreWire width hg hv hc

private theorem coreTemplate_upper_shape (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    {a b : Token} : (a, b) ∈ (coreTemplate vertex ports).upper →
      (a = .rotation vertex true ∧ b = .rotation vertex false) ∨
        (a = .rotation vertex false ∧ b = .rotation vertex true) := by
  unfold coreTemplate
  extract_lets pa pb pc kind ta tb tc inside outside
  split_ifs
  · intro h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl⟩
  · intro h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, rfl⟩
  · intro h
    cases h

/-- Every actual local upper wire is precisely the two sides of its original core rotation. -/
theorem vertexBlock_upper_shape (width : ℕ) (input : Input) (vertex : ℕ) {a b : Token}
    (hu : (a, b) ∈ (vertexBlock width input vertex).upper) :
    (a = .rotation vertex true ∧ b = .rotation vertex false) ∨
      (a = .rotation vertex false ∧ b = .rotation vertex true) :=
  coreTemplate_upper_shape vertex (fan width input vertex) hu

/-- The actual AND triple of a native vertex block has legal normalized inputs and the required
middle-to-left light-input order. -/
theorem ConfigurationInput.normalizedBlock_andGate (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length) {a b c : Token}
    (hgate : .gate .andGate a b c ∈ (vertexBlock width x.input vertex).lower) :
    (x.normalizedTokenBit width vertex c = false ∨
      (x.normalizedTokenBit width vertex a = false ∧ x.normalizedTokenBit width vertex b = false)) ∧
      (x.normalizedTokenBit width vertex b = false →
        x.normalizedTokenBit width vertex a = false) := by
  obtain ⟨hk, ht⟩ := vertexBlock_gate_metadata width x.input vertex hgate
  rcases coreBlock_weights width x.input hg hv with ⟨_, hw⟩ | ⟨hor, _⟩
  · obtain ⟨p, r, s, hp⟩ := ports_of_tokens_weights ht hw
    exact x.normalized_and_ports width hg hs hv hk hp
  · cases hk.symm.trans hor

/-- The actual OR triple of a native vertex block retains a supplied original input. -/
theorem ConfigurationInput.normalizedBlock_orGate (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length) {a b c : Token}
    (hgate : .gate .orGate a b c ∈ (vertexBlock width x.input vertex).lower) :
    x.normalizedTokenBit width vertex a = false ∨
      x.normalizedTokenBit width vertex b = false ∨
        x.normalizedTokenBit width vertex c = false := by
  obtain ⟨hk, ht⟩ := vertexBlock_gate_metadata width x.input vertex hgate
  rcases coreBlock_weights width x.input hg hv with ⟨hand, _⟩ | ⟨_, hw⟩
  · cases hk.symm.trans hand
  · obtain ⟨p, r, s, hp⟩ := ports_of_tokens_weights ht hw
    exact x.normalized_or_ports width hg hs hv hk hp

end PushPuzzle.PushS.Comb
