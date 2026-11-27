/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Deterministic weighted port order

The physical gate has a left input, an upper input and a right output. For an
AND vertex a cyclic rotation puts its blue port at the output; for an OR
vertex the three listed blue ports keep their order.
Every edge number and reference direction is retained.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL

/-- The three numbered ports used by a physical gate. -/
structure OrderedPorts where
  /-- Select AND rather than OR. -/
  isAND : Bool
  /-- Left input, red at an AND vertex. -/
  left : NCL.Port ℕ
  /-- Upper input, red at an AND vertex. -/
  upper : NCL.Port ℕ
  /-- Right output, blue at either kind of vertex. -/
  output : NCL.Port ℕ

/-- Gate kind followed by binary edge numbers and their orientation bits. -/
enc_structure encOrderedPorts : OrderedPorts where
  isAND : encBool, left : (NCL.encPort encNat), upper : (NCL.encPort encNat),
  output : (NCL.encPort encNat)

/-- Rotate a cyclic three-port order to put the AND's blue port at the output. -/
def orderPorts (v : NCL.Vertex ℕ) : OrderedPorts :=
  let fallback : NCL.WeightedPort ℕ := ⟨⟨0, false⟩, 0⟩
  let a := v.ports.getD 0 fallback
  let b := v.ports.getD 1 fallback
  let c := v.ports.getD 2 fallback
  if a.weight = 2 ∧ b.weight = 2 ∧ c.weight = 2 then ⟨false, a.port, b.port, c.port⟩
  else if a.weight = 2 then ⟨true, b.port, c.port, a.port⟩
  else if b.weight = 2 then ⟨true, c.port, a.port, b.port⟩
  else ⟨true, a.port, b.port, c.port⟩

/-- The weighted constraint in the chosen physical port order. -/
def OrderedPorts.vertex (p : OrderedPorts) : NCL.Vertex ℕ :=
  if p.isAND then NCL.Vertex.and p.left p.upper p.output
  else NCL.Vertex.or p.left p.upper p.output

private theorem three_permutations {α : Type} (x y z : α) :
    [x, y, z].permutations =
      [[x, y, z], [y, x, z], [z, y, x], [y, z, x], [z, x, y], [x, z, y]] := by
  cbv

/-- The actual vertex data differ only in port order after normalization. -/
theorem orderPorts_correct {v : NCL.Vertex ℕ} (hv : v.IsAndOr) :
    v.minInflow = 2 ∧ v.ports.Perm (orderPorts v).vertex.ports := by
  rcases hv with ⟨a, b, c, hm, hp⟩ | ⟨a, b, c, hm, hp⟩
  · refine ⟨hm, ?_⟩
    have he := List.mem_permutations.mpr hp
    change v.ports ∈ ([⟨a, 1⟩, ⟨b, 1⟩, ⟨c, 2⟩] : List (NCL.WeightedPort ℕ)).permutations at he
    rw [three_permutations] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    have hn : orderPorts v = ⟨true, a, b, c⟩ ∨ orderPorts v = ⟨true, b, a, c⟩ := by
      rcases he with he | he | he | he | he | he <;>
        simp [orderPorts, he]
    rcases hn with hn | hn
    · simpa only [hn, OrderedPorts.vertex, Bool.true_eq, ite_true] using hp
    · have hswap : (NCL.Vertex.and a b c).ports.Perm (NCL.Vertex.and b a c).ports :=
        List.Perm.swap _ _ _
      simpa only [hn, OrderedPorts.vertex, Bool.true_eq, ite_true] using hp.trans hswap
  · refine ⟨hm, ?_⟩
    have he := List.mem_permutations.mpr hp
    change v.ports ∈ ([⟨a, 2⟩, ⟨b, 2⟩, ⟨c, 2⟩] : List (NCL.WeightedPort ℕ)).permutations at he
    rw [three_permutations] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he | he | he | he <;>
      simp [orderPorts, OrderedPorts.vertex, NCL.Vertex.or, he]

/-- Computing the physical port roles has an actual polynomial-time machine. -/
theorem orderPorts_polyTime :
    ComputableInPolyTime orderPorts (NCL.encVertex encNat) encOrderedPorts := by
  unfold orderPorts
  fun_prop

end PushPuzzle.PushFS.Reduction
