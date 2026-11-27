/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombConfigurationReadout
public import PushS.CombCore
import all PushS.CombConfiguration
import all PushS.CombCore
import all PushS.CombPartition

/-!
# Actual original incidence directions at the emitted cores

The local heavy-port rotation retains the same original weighted incidences. Its inside axis
has exactly the original incidence direction, and its outside axis has the complementary bit.

## Main results

* `Comb.ConfigurationInput.corePort_bit`: exact original direction at each actual core port.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- Every actual core port has a distinct original contour token. -/
theorem coreTokens_nodup (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    {vertex : ℕ} (hv : vertex < input.graph.vertices.length) :
    ((coreBlock width input vertex).core.ports.map Prod.fst).Nodup := by
  let ports := fan width input vertex
  have hn := coreTemplate_order_nodup vertex ports (fan_length width input hg hv)
    (fan_tips_nodup width input hg hv)
  obtain ⟨left, middle, right, hp, hg⟩ := coreTemplate_core_group vertex ports
  obtain ⟨before, after, ho⟩ := coreTemplate_gate_contiguous vertex ports hg
  rw [ho] at hn
  change ((coreTemplate vertex ports).core.ports.map Prod.fst).Nodup
  rw [hp]
  exact hn.of_append_left.of_append_right

/-- Genuine tooth-crossing tokens never occur in an actual original core's port list. -/
theorem coreTokens_no_mark (width : ℕ) (input : Input) (vertex edge slot tooth : ℕ) (side : Bool) :
    Token.mark edge slot tooth side ∉ (coreBlock width input vertex).core.ports.map Prod.fst := by
  unfold coreBlock coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;> simp [ta, tb, tc, inside, incidenceToken]

/-- Every rotation port on an actual core is its own inside incidence. -/
theorem coreTokens_rotation (width : ℕ) (input : Input) (vertex owner : ℕ) (side : Bool)
    (h : Token.rotation owner side ∈ (coreBlock width input vertex).core.ports.map Prod.fst) :
    owner = vertex ∧ side = true := by
  unfold coreBlock coreTemplate at h
  extract_lets a b c kind ta tb tc inside outside at h
  split_ifs at h <;> simp [ta, tb, tc, inside, incidenceToken] at h
  all_goals exact h

/-- Every actual original core port reads exactly its original native weighted incidence. -/
theorem ConfigurationInput.corePort_bit (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length)
    {tp : Token × (NCL.WeightedPort ℕ)} (hp : tp ∈ (coreBlock width x.input vertex).core.ports) :
    let (token, ⟨port, _⟩) := tp
    x.tokenBit width token = x.portBit port := by
  change x.tokenBit width tp.1 = x.portBit tp.2.1
  obtain ⟨a, b, c, hfan⟩ := List.length_eq_three.mp (fan_length width x.input hg hv)
  let kind := if [a, b, c].any (fun p => decide (p.2 = 1)) then
    Shuttle.Kind.andGate else .orGate
  by_cases h₁ : kind = .andGate ∧ a.2 = 2
  all_goals dsimp only [kind] at h₁
  · have hm : (coreBlock width x.input vertex).core.ports =
        [(incidenceToken b.1, b), (incidenceToken c.1, c), (.rotation vertex true, a)] := by
      simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
      rw [ite_eq_left h₁]
    have hr : rotationPort width x.input vertex = a.1 := by
      simp [rotationPort, hm, incidenceToken, beq_iff_eq]
    rw [hm] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    obtain rfl := List.mem_singleton.mp hp
    simp only [ConfigurationInput.tokenBit, hr, ite_true]
  · by_cases h₂ : kind = .andGate ∧ b.2 = 2
    all_goals dsimp only [kind] at h₂
    · have hm : (coreBlock width x.input vertex).core.ports =
          [(.rotation vertex true, c), (incidenceToken a.1, a), (incidenceToken b.1, b)] := by
        simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right h₁, ite_eq_left h₂]
      have hr : rotationPort width x.input vertex = c.1 := by
        simp [rotationPort, hm, incidenceToken, beq_iff_eq]
      rw [hm] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [ConfigurationInput.tokenBit, hr, ite_true]
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      obtain rfl := List.mem_singleton.mp hp
      rfl
    · have hm : (coreBlock width x.input vertex).core.ports =
          [(incidenceToken a.1, a), (incidenceToken b.1, b), (incidenceToken c.1, c)] := by
        simp only [coreBlock, hfan, coreTemplate, List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right h₁, ite_eq_right h₂]
      rw [hm] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      obtain rfl := List.mem_singleton.mp hp
      rfl

/-- A local rotation's two actual axes always have complementary directions. -/
theorem ConfigurationInput.rotation_sides (width : ℕ) (x : ConfigurationInput) (vertex : ℕ) :
    x.tokenBit width (.rotation vertex false) = !(x.tokenBit width (.rotation vertex true)) := by
  simp only [ConfigurationInput.tokenBit, Bool.false_eq_true, ite_false, ite_true]

/-- The actual core's emitted incoming directions satisfy the same original weighted threshold.
-/
theorem ConfigurationInput.core_inflow (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph)
    (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length) :
    2 ≤ ((coreBlock width x.input vertex).core.ports.map
      (fun (token, ⟨_, weight⟩) => if x.tokenBit width token = false then weight else 0)).sum := by
  let v : Fin x.input.graph.vertices.length := ⟨vertex, hv⟩
  let direction := fun e : ℕ => x.bits.getD e false
  let raw := x.input.graph.vertices.getD vertex ⟨[], 0⟩
  have hm : (x.input.graph.graph v).map Fin.val = raw := by
    change (x.input.graph.graph v).map Fin.val = x.input.graph.vertices.getD v.val ⟨[], 0⟩
    rw [List.getD_eq_get _ _ v]
    exact congrFun (x.input.graph.graph_map_val hg.1) v
  have hr : raw.Sat direction := by
    rw [← hm, NCL.Vertex.sat_map]
    exact hs v
  have hmin : raw.minInflow = 2 := (vertex_isAndOr x.input hg hv).shape.2
  have hp := coreBlock_ports_perm width x.input hg hv
  have he : ((coreBlock width x.input vertex).core.ports.map
      (fun tp => if x.tokenBit width tp.1 = false then tp.2.2 else 0)).sum =
      ((coreBlock width x.input vertex).core.ports.map Prod.snd |>.map
        fun p => if p.1.In direction then p.2 else 0).sum := by
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro tp ht
    simp only [Function.comp_apply, x.corePort_bit width hg hv ht,
      x.portBit_eq_false, NCL.Port.In, direction]
    rfl
  rw [he, (hp.map (fun p => if p.1.In direction then p.2 else 0)).sum_nat]
  change raw.minInflow ≤ raw.inflow direction at hr
  rwa [hmin] at hr

end PushPuzzle.PushS.Comb
