/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionGates
public import PushS.CombConstraintGraph
import all PushS.CombNormalizedInputs
import all PushS.PortConstraintGraph

/-! Exact legality of the same original native subdivision and the actual numbered port layout. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem minmax_supply_iff (value : ℕ → Bool) (bit : Bool) (a b : ℕ) :
    (value (min a b) = bit ∨ value (max a b) = bit) ↔ value a = bit ∨ value b = bit := by
  rcases le_total a b with h | h
  · simp only [Nat.min_eq_left h, Nat.max_eq_right h]
  · simp only [Nat.min_eq_right h, Nat.max_eq_left h, or_comm]

private theorem numbered_upper_iff (cut : Cut) (value : ℕ → Bool) (bit : Bool) :
    (∀ a b, (a, b) ∈ cut.toLayout.upperPairs → value a = bit ∨ value b = bit) ↔
      ∀ a b, (a, b) ∈ cut.upper → value (cut.rank a) = bit ∨ value (cut.rank b) = bit := by
  constructor
  · intro h a b hp
    exact (minmax_supply_iff value bit _ _).mp (h _ _ (List.mem_map.mpr ⟨(a, b), hp, rfl⟩))
  · intro h a b hp
    change (a, b) ∈ cut.upper.map (fun p =>
      (min (cut.rank p.1) (cut.rank p.2), max (cut.rank p.1) (cut.rank p.2))) at hp
    obtain ⟨⟨left, right⟩, hraw, he⟩ := List.mem_map.mp hp
    cases he
    exact (minmax_supply_iff value bit _ _).mpr (h left right hraw)

private theorem numbered_wire_iff (cut : Cut) (value : ℕ → Bool) :
    (∀ a b, .wire a b ∈ cut.toLayout.lowerGroups → value a = false ∨ value b = false) ↔
      ∀ a b, .wire a b ∈ cut.lower → value (cut.rank a) = false ∨ value (cut.rank b) = false := by
  constructor
  · intro h a b hp
    exact (minmax_supply_iff value false _ _).mp (h _ _ (List.mem_map.mpr ⟨.wire a b, hp, rfl⟩))
  · intro h a b hp
    change .wire a b ∈ cut.lower.map cut.lowerGroup at hp
    obtain ⟨group, hraw, he⟩ := List.mem_map.mp hp
    cases group with
    | wire left right =>
      cases he
      exact (minmax_supply_iff value false _ _).mpr (h left right hraw)
    | gate kind left middle right => cases he

private theorem numbered_gate_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (condition : Shuttle.Kind → ℕ → ℕ → ℕ → Prop) :
    (∀ kind first, .gate kind first ∈ (compile width input).lowerGroups →
      condition kind first (first + 1) (first + 2)) ↔
      ∀ kind a b c, .gate kind a b c ∈ (cut width input).lower →
        condition kind ((cut width input).rank a) ((cut width input).rank b) ((cut width input).rank c) := by
  constructor
  · intro h kind a b c hp
    obtain ⟨hb, hc⟩ := cut_gate_ranks width input hg hcount hp
    rw [hb, hc]
    exact h kind _ (List.mem_map.mpr ⟨.gate kind a b c, hp, rfl⟩)
  · intro h kind first hp
    change .gate kind first ∈ (cut width input).lower.map (cut width input).lowerGroup at hp
    obtain ⟨group, hraw, he⟩ := List.mem_map.mp hp
    cases group with
    | wire a b => cases he
    | gate source a b c =>
      have he' : source = kind ∧ (cut width input).rank a = first := LowerGroup.gate.inj he
      obtain ⟨rfl, rfl⟩ := he'
      obtain ⟨hb, hc⟩ := cut_gate_ranks width input hg hcount hraw
      simpa only [hb, hc] using h source a b c hraw

private theorem inputLegal_fields_iff (layout : PortLayout) (axes : List Bool) :
    layout.InputLegal axes ↔ axes.length = layout.portCount ∧
      (∀ a b, (a, b) ∈ layout.upperPairs → axes.getD a false = true ∨ axes.getD b false = true) ∧
      (∀ a b, .wire a b ∈ layout.lowerGroups → axes.getD a false = false ∨ axes.getD b false = false) ∧
      (∀ kind first, .gate kind first ∈ layout.lowerGroups → match kind with
        | .andGate => axes.getD (first + 2) false = false ∨
            (axes.getD first false = false ∧ axes.getD (first + 1) false = false)
        | .orGate => axes.getD first false = false ∨ axes.getD (first + 1) false = false ∨
            axes.getD (first + 2) false = false) := by
  constructor
  · intro h
    refine ⟨h.axes_length, h.upper, h.lower_wire, ?_⟩
    intro kind first hp
    cases kind with
    | andGate => exact h.and_gate first hp
    | orGate => exact h.or_gate first hp
  · rintro ⟨hlen, hu, hw, hg⟩
    exact ⟨hlen, hu, hw, hg .orGate, hg .andGate⟩

private theorem token_gate_fields_iff (cut : Cut) (direction : Token → Bool) :
    (∀ kind a b c, .gate kind a b c ∈ cut.lower → match kind with
      | .andGate => direction c = false ∨ (direction a = false ∧ direction b = false)
      | .orGate => direction a = false ∨ direction b = false ∨ direction c = false) ↔
      (∀ a b c, .gate .andGate a b c ∈ cut.lower →
        direction c = false ∨ (direction a = false ∧ direction b = false)) ∧
      (∀ a b c, .gate .orGate a b c ∈ cut.lower →
        direction a = false ∨ direction b = false ∨ direction c = false) := by
  constructor
  · exact fun h => ⟨h .andGate, h .orGate⟩
  · rintro ⟨ha, ho⟩ kind a b c hp
    cases kind with
    | andGate => exact ha a b c hp
    | orGate => exact ho a b c hp

/-- The same actual subdivision-axis renaming in the standard native graph's finite edge type. -/
noncomputable def subdivisionNativeEquiv (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing) ≃
      Fin (compile width input).graphData.edgeCount :=
  (subdivisionAxisEquiv width input hg hcount hedges drawing).trans
    (finCongr (compile width input).graphData_edgeCount.symm)

/-- Renaming into the native finite edge type retains the same literal numerical axis. -/
theorem subdivisionNativeEquiv_val (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing)) :
    (subdivisionNativeEquiv width input hg hcount hedges drawing segment).val =
      (subdivisionAxisEquiv width input hg hcount hedges drawing segment).val := by
  rfl

/-- Arbitrary configurations of the original native subdivision are exactly legal actual axis arrays.
-/
theorem axisGraph_legal_iff_inputLegal (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (axes : List Bool)
    (hlen : axes.length = (compile width input).portCount) :
    (axisGraph width input drawing).Legal
      ((compile width input).graphData.config axes ∘ subdivisionNativeEquiv width input hg hcount hedges drawing) ↔
      (compile width input).InputLegal axes := by
  let direction := fun token => axes.getD ((cut width input).rank token) false
  have he : (compile width input).graphData.config axes ∘ subdivisionNativeEquiv width input hg hcount hedges drawing =
      direction ∘ segmentToken width input drawing := by
    funext segment
    exact congrArg (fun index => axes.getD index false) (subdivisionAxisEquiv_val width input hg hcount hedges drawing segment)
  rw [he]
  rw [NCL.ConstraintGraph.Legal, Sum.forall]
  erw [axisGraph_cores_sat_iff width input hg hcount drawing direction,
    axisGraph_joints_sat_iff width input hg hcount hedges drawing direction,
    inputLegal_fields_iff, numbered_upper_iff (cut width input) (fun index => axes.getD index false) true,
    numbered_wire_iff (cut width input) (fun index => axes.getD index false),
    numbered_gate_iff width input hg hcount (fun kind a b c => match kind with
      | .andGate => axes.getD c false = false ∨ (axes.getD a false = false ∧ axes.getD b false = false)
      | .orGate => axes.getD a false = false ∨ axes.getD b false = false ∨ axes.getD c false = false)]
  simp only [hlen, true_and]
  rw [token_gate_fields_iff (cut width input) direction]
  tauto

end PushPuzzle.PushS.Comb
