/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNormalizedReadout
import all PushS.CombNormalizedConfiguration

/-!
# Ordered normalized inputs at the actual AND and OR cores

Use the same original native legality and the actual retained core weight list. A supplied-heavy
AND withdraws both light demands; an unsupplied-heavy AND receives both light inputs. OR cores
retain their original legal directions.

## Main results

* `Comb.ConfigurationInput.normalized_and_ports`: legal and ordered actual AND inputs.
* `Comb.ConfigurationInput.normalized_or_ports`: a supplied actual OR input.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

variable (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
  (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
  {vertex : ℕ} (hv : vertex < x.input.graph.vertices.length)
  {a b c : Token} {p r s : NCL.Port ℕ}

include hg hs hv

private theorem three_port_threshold {wa wb wc : ℕ}
    (hp : (coreBlock width x.input vertex).core.ports = [(a, ⟨p, wa⟩), (b, ⟨r, wb⟩), (c, ⟨s, wc⟩)]) :
    2 ≤ (if x.portBit p = false then wa else 0) +
      ((if x.portBit r = false then wb else 0) + (if x.portBit s = false then wc else 0)) := by
  have ha : (a, ⟨p, wa⟩) ∈ (coreBlock width x.input vertex).core.ports := by rw [hp]; simp
  have hb : (b, ⟨r, wb⟩) ∈ (coreBlock width x.input vertex).core.ports := by rw [hp]; simp
  have hc : (c, ⟨s, wc⟩) ∈ (coreBlock width x.input vertex).core.ports := by rw [hp]; simp
  have hi := x.core_inflow width hg hs hv
  rw [hp] at hi
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    x.corePort_bit width hg hv ha, x.corePort_bit width hg hv hb,
    x.corePort_bit width hg hv hc] using hi

omit hs in
private theorem three_normalized_ports {wa wb wc : ℕ}
    (hp : (coreBlock width x.input vertex).core.ports = [(a, ⟨p, wa⟩), (b, ⟨r, wb⟩), (c, ⟨s, wc⟩)]) :
    x.normalizedTokenBit width vertex a =
        (if x.heavySupplied width vertex && wa == 1 then true else x.portBit p) ∧
      x.normalizedTokenBit width vertex b =
        (if x.heavySupplied width vertex && wb == 1 then true else x.portBit r) ∧
      x.normalizedTokenBit width vertex c =
        (if x.heavySupplied width vertex && wc == 1 then true else x.portBit s) := by
  refine ⟨x.normalized_corePort_bit width hg hv ?_, x.normalized_corePort_bit width hg hv ?_,
    x.normalized_corePort_bit width hg hv ?_⟩ <;> rw [hp] <;> simp

/-- The actual normalized AND core receives its heavy input or both light inputs, with the
middle light input requested only while the left light input is present. -/
theorem ConfigurationInput.normalized_and_ports
    (hk : (coreBlock width x.input vertex).core.kind = .andGate)
    (hp : (coreBlock width x.input vertex).core.ports = [(a, ⟨p, 1⟩), (b, ⟨r, 1⟩), (c, ⟨s, 2⟩)]) :
    (x.normalizedTokenBit width vertex c = false ∨
      (x.normalizedTokenBit width vertex a = false ∧ x.normalizedTokenBit width vertex b = false)) ∧
      (x.normalizedTokenBit width vertex b = false →
        x.normalizedTokenBit width vertex a = false) := by
  have hh : x.heavySupplied width vertex = !(x.portBit s) := by
    simp [ConfigurationInput.heavySupplied, CoreQuery.heavySupplied, heavyDemand, CoreQuery.core,
      hk, hp]
  obtain ⟨hna, hnb, hnc⟩ := three_normalized_ports width x hg hv hp
  have hi := three_port_threshold width x hg hs hv hp
  rw [hna, hnb, hnc, hh]
  cases ha : x.portBit p <;> cases hb : x.portBit r <;> cases hc : x.portBit s <;>
    simp only [ha, hb, hc] at hi
    <;> simp only [Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
      Nat.reduceBEq, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hi ⊢
    <;> first | omega | decide

/-- The actual normalized OR core retains at least one supplied original native input. -/
theorem ConfigurationInput.normalized_or_ports
    (hk : (coreBlock width x.input vertex).core.kind = .orGate)
    (hp : (coreBlock width x.input vertex).core.ports = [(a, ⟨p, 2⟩), (b, ⟨r, 2⟩), (c, ⟨s, 2⟩)]) :
    x.normalizedTokenBit width vertex a = false ∨
      x.normalizedTokenBit width vertex b = false ∨
        x.normalizedTokenBit width vertex c = false := by
  have hh : x.heavySupplied width vertex = false := by
    simp [ConfigurationInput.heavySupplied, CoreQuery.heavySupplied, heavyDemand,
      CoreQuery.core, hk]
  obtain ⟨hna, hnb, hnc⟩ := three_normalized_ports width x hg hv hp
  have hi := three_port_threshold width x hg hs hv hp
  rw [hna, hnb, hnc, hh]
  cases ha : x.portBit p <;> cases hb : x.portBit r <;> cases hc : x.portBit s <;>
    simp only [ha, hb, hc, Bool.false_and, Bool.false_eq_true, Bool.true_eq_false,
      ite_false, ite_true] at hi ⊢ <;> first | omega | decide

end PushPuzzle.PushS.Comb
