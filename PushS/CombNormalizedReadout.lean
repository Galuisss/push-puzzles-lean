/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNormalizedConfiguration
import all PushS.CombNormalizedConfiguration

/-!
# Exact local readout of normalized actual core demands

Normalization preserves every genuine crossing, increases upper supply at native tips, and keeps
the two sides of every local rotation complementary. At the actual original core, only a light
input of a supplied-heavy AND vertex is withdrawn.

## Main results

* `Comb.ConfigurationInput.normalized_mark`: original actual crossing bits are retained.
* `Comb.ConfigurationInput.normalized_tip_true`: upper supply at original tips is retained.
* `Comb.ConfigurationInput.normalized_rotation_sides`: complementary local rotation directions.
* `Comb.ConfigurationInput.normalized_corePort_bit`: exact original core-demand normalization.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem lightTokens_subset (width : ℕ) (q : CoreQuery) {token : Token}
    (h : token ∈ q.lightTokens width) : token ∈ (q.core width).ports.map Prod.fst := by
  obtain ⟨tp, ht, he⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨tp, (List.mem_filter.mp ht).1, he⟩

private theorem lightTokens_no_mark (width : ℕ) (q : CoreQuery)
    (edge slot tooth : ℕ) (side : Bool) :
    (q.lightTokens width).contains (.mark edge slot tooth side) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact coreTokens_no_mark width q.source.input q.vertex edge slot tooth side
    (lightTokens_subset width q (List.contains_iff_mem.mp h))

private theorem lightTokens_no_outside (width : ℕ) (q : CoreQuery) :
    (q.lightTokens width).contains (.rotation q.vertex false) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hp := coreTokens_rotation width q.source.input q.vertex q.vertex false
    (lightTokens_subset width q (List.contains_iff_mem.mp h))
  exact Bool.false_ne_true hp.2

private theorem normalized_mark_query (width : ℕ) (q : CoreQuery)
    (edge slot tooth : ℕ) (side : Bool) :
    q.tokenBit width (.mark edge slot tooth side) =
      q.source.tokenBit width (.mark edge slot tooth side) := by
  have hl := lightTokens_no_mark width q edge slot tooth side
  have ho : (Token.mark edge slot tooth side == Token.rotation q.vertex false) = false := by simp
  simp only [CoreQuery.tokenBit, CoreQuery.demand, Demand.bit, hl, ho, Bool.and_false,
    Bool.false_eq_true, ite_false, ite_self]

/-- Every actual crossing side retains its same original native direction after normalization.
-/
theorem ConfigurationInput.normalized_mark (width : ℕ) (x : ConfigurationInput)
    (vertex edge slot tooth : ℕ) (side : Bool) :
    x.normalizedTokenBit width vertex (.mark edge slot tooth side) =
      x.tokenBit width (.mark edge slot tooth side) :=
  normalized_mark_query width ⟨x, vertex⟩ edge slot tooth side

private theorem normalized_true_query (width : ℕ) (q : CoreQuery) (token : Token)
    (hne : token ≠ .rotation q.vertex false) (h : q.source.tokenBit width token = true) :
    q.tokenBit width token = true := by
  have ho : (token == Token.rotation q.vertex false) = false := beq_eq_false_iff_ne.mpr hne
  simp only [CoreQuery.tokenBit, CoreQuery.demand, Demand.bit, ho, Bool.and_false,
    Bool.false_eq_true, ite_false, h, ite_self]

/-- Normalizing a native tip preserves every existing upper-page supply. -/
theorem ConfigurationInput.normalized_tip_true (width : ℕ) (x : ConfigurationInput)
    (vertex edge : ℕ) (dir : Bool) (h : x.tokenBit width (.tip edge dir) = true) :
    x.normalizedTokenBit width vertex (.tip edge dir) = true :=
  normalized_true_query width ⟨x, vertex⟩ (.tip edge dir) (by simp) h

/-- Normalizing a rotation's inside retains every existing upper-page supply. -/
theorem ConfigurationInput.normalized_rotation_true (width : ℕ) (x : ConfigurationInput)
    (vertex : ℕ) (h : x.tokenBit width (.rotation vertex true) = true) :
    x.normalizedTokenBit width vertex (.rotation vertex true) = true :=
  normalized_true_query width ⟨x, vertex⟩ (.rotation vertex true) (by simp) h

private theorem normalized_not_core_query (width : ℕ) (q : CoreQuery) (token : Token)
    (hnot : token ∉ (q.core width).ports.map Prod.fst) (hout : token ≠ .rotation q.vertex false) :
    q.tokenBit width token = q.source.tokenBit width token := by
  have hl : (q.lightTokens width).contains token = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hnot (lightTokens_subset width q (List.contains_iff_mem.mp h))
  have ho : (token == Token.rotation q.vertex false) = false := beq_eq_false_iff_ne.mpr hout
  simp only [CoreQuery.tokenBit, CoreQuery.demand, Demand.bit, hl, ho, Bool.and_false,
    Bool.false_eq_true, ite_false, ite_self]

/-- An ordinary token outside the actual core and its outside rotation keeps its original bit.
-/
theorem ConfigurationInput.normalized_not_core (width : ℕ) (x : ConfigurationInput)
    (vertex : ℕ) (token : Token)
    (hnot : token ∉ (coreBlock width x.input vertex).core.ports.map Prod.fst)
    (hout : token ≠ .rotation vertex false) :
    x.normalizedTokenBit width vertex token = x.tokenBit width token :=
  normalized_not_core_query width ⟨x, vertex⟩ token hnot hout

private theorem normalized_rotation_query (width : ℕ) (q : CoreQuery) :
    q.tokenBit width (.rotation q.vertex false) =
      !(q.tokenBit width (.rotation q.vertex true)) := by
  have ho := lightTokens_no_outside width q
  have he : (Token.rotation q.vertex true == Token.rotation q.vertex false) = false := by simp
  simp only [CoreQuery.tokenBit, CoreQuery.demand, Demand.bit, ho, he, beq_self_eq_true,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ite_false]
  cases hh : q.heavySupplied width <;>
    cases hl : (q.lightTokens width).contains (.rotation q.vertex true) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_true]
  all_goals exact q.source.rotation_sides width q.vertex

/-- Normalization keeps the same local rotation's two directions complementary. -/
theorem ConfigurationInput.normalized_rotation_sides (width : ℕ) (x : ConfigurationInput)
    (vertex : ℕ) :
    x.normalizedTokenBit width vertex (.rotation vertex false) =
      !(x.normalizedTokenBit width vertex (.rotation vertex true)) :=
  normalized_rotation_query width ⟨x, vertex⟩

private theorem lightTokens_entry (width : ℕ) (q : CoreQuery) (hg : NCL.SourceValid q.source.input.graph)
    (hv : q.vertex < q.source.input.graph.vertices.length)
    {token : Token} {port : NCL.Port ℕ} {weight : ℕ}
    (h : (token, ⟨port, weight⟩) ∈ (q.core width).ports) :
    (q.lightTokens width).contains token = (weight == 1) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, beq_iff_eq]
  constructor
  · intro hm
    obtain ⟨tp, htp, he⟩ := List.mem_map.mp hm
    obtain ⟨htp, hw⟩ := List.mem_filter.mp htp
    have hn := coreTokens_nodup width q.source.input hg hv
    have hp := List.inj_on_of_nodup_map hn htp h he
    subst tp
    exact of_decide_eq_true hw
  · intro hw
    apply List.mem_map.mpr
    exact ⟨(token, ⟨port, weight⟩), List.mem_filter.mpr ⟨h, by simp only [hw, beq_self_eq_true]⟩, rfl⟩

private theorem normalized_corePort_query (width : ℕ) (q : CoreQuery)
    (hg : NCL.SourceValid q.source.input.graph) (hv : q.vertex < q.source.input.graph.vertices.length)
    {token : Token} {port : NCL.Port ℕ} {weight : ℕ}
    (h : (token, ⟨port, weight⟩) ∈ (q.core width).ports) :
    q.tokenBit width token =
      if q.heavySupplied width && weight == 1 then true else q.source.portBit port := by
  have hl := lightTokens_entry width q hg hv h
  have ht : token ≠ .rotation q.vertex false := by
    intro he
    have hm : Token.rotation q.vertex false ∈ (q.core width).ports.map Prod.fst :=
      List.mem_map.mpr ⟨(token, ⟨port, weight⟩), h, he⟩
    exact Bool.false_ne_true
      (coreTokens_rotation width q.source.input q.vertex q.vertex false hm).2
  have he : (token == Token.rotation q.vertex false) = false := beq_eq_false_iff_ne.mpr ht
  have hb := q.source.corePort_bit width hg hv h
  simp only [CoreQuery.tokenBit, CoreQuery.demand, Demand.bit, hl, he, hb,
    Bool.and_false, Bool.false_eq_true, ite_false]
  cases hh : q.heavySupplied width <;> cases hw : weight == 1 <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Bool.false_and, Bool.true_and]

/-- Only actual light core inputs are withdrawn while the same original heavy direction supplies
the AND core. -/
theorem ConfigurationInput.normalized_corePort_bit (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length)
    {token : Token} {port : NCL.Port ℕ} {weight : ℕ}
    (h : (token, ⟨port, weight⟩) ∈ (coreBlock width x.input vertex).core.ports) :
    x.normalizedTokenBit width vertex token =
      if x.heavySupplied width vertex && weight == 1 then true else x.portBit port :=
  normalized_corePort_query width ⟨x, vertex⟩ hg hv h

end PushPuzzle.PushS.Comb
