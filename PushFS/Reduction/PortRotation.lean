/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortAnnulus
import Mathlib.Tactic.FinCases

/-!
# Binding the finite annuli to the source's actual cyclic ports

Port normalization computes a rotation by zero, one or two positions. The
annular curve for each physical role ends in the direction of exactly that
source-star arm, preserving the original edge number and reference direction.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- The cyclic shift used to put an AND's blue port in the physical output role. -/
def portRotation (v : Vertex ℕ) : Fin 3 :=
  let fallback : WeightedPort ℕ := ⟨⟨0, false⟩, 0⟩
  let a := v.ports.getD 0 fallback
  let b := v.ports.getD 1 fallback
  let c := v.ports.getD 2 fallback
  if a.weight = 2 ∧ b.weight = 2 ∧ c.weight = 2 then 0
  else if a.weight = 2 then 1
  else if b.weight = 2 then 2 else 0

/-- Read one physical W/N/E role in the normalized gate. -/
def OrderedPorts.port (p : OrderedPorts) (i : Fin 3) : Port ℕ :=
  if i = 0 then p.left else if i = 1 then p.upper else p.output

/-- The physical port is the exact cyclicly indexed source port. -/
private theorem orderPorts_port_rotation (v : Vertex ℕ) (hv : v.ports.length = 3) (i : Fin 3) :
    (orderPorts v).port i =
      (v.ports.getD (((portRotation v).val + i.val) % 3) ⟨⟨0, false⟩, 0⟩).port := by
  obtain ⟨a, b, c, hp⟩ := List.length_eq_three.mp hv
  fin_cases i <;>
    simp [orderPorts, portRotation, hp, OrderedPorts.port]
  all_goals split_ifs <;> rfl

/-- Unary encoding of the three possible rotation values. -/
def encRole : Fin 3 ↪ List Bool :=
  (⟨Fin.val, Fin.val_injective⟩ : Fin 3 ↪ ℕ).trans encUnary

@[fun_prop] theorem portRotation_polyTime :
    ComputableInPolyTime portRotation (encVertex encNat) encRole := by
  unfold portRotation
  fun_prop

namespace PortAnnulus

/-- Unary framing of the outer pattern, rotation and physical role. -/
abbrev encKey : Key ↪ List Bool := encPair encRole (encPair encRole encRole)

/-- A source-star arm before numeric edge names are substituted. -/
structure Arm where
  /-- Input rather than output. -/
  incoming : Bool
  /-- Its index on that boundary row. -/
  index : ℕ
  deriving DecidableEq

/-- Enumerate top ports left-to-right and bottom ports right-to-left. -/
def circularArm (inputArity : ℕ) (j : Fin 3) : Arm :=
  if j.val < inputArity then ⟨true, j.val⟩
  else ⟨false, 3 - inputArity - 1 - (j.val - inputArity)⟩

/-- The actual direction in which the grid-star arm leaves its central vertex. -/
def armDirection (inputArity : ℕ) (a : Arm) : Direction :=
  if a.index < GridStar.center inputArity then .west
  else if GridStar.center inputArity < a.index then .east
  else if a.incoming then .north else .south

/-- Select the actual outer triple of a three-port source star. -/
def pattern (inputArity : ℕ) : Fin 3 :=
  if inputArity = 0 then 0 else if inputArity = 3 then 2 else 1

@[fun_prop] theorem pattern_polyTime : ComputableInPolyTime pattern encUnary encRole := by
  unfold pattern
  fun_prop

private theorem direction_checked : ∀ (a : Fin 4) (j : Fin 3),
    boundaryDirection (pattern a.val) j.val = armDirection a.val (circularArm a.val j) := by
  decide +kernel

/-- The annulus's unrotated cyclic outer order is exactly the source-star tangent order. -/
private theorem direction_circular (a : ℕ) (ha : a ≤ 3) (j : Fin 3) :
    boundaryDirection (pattern a) j.val = armDirection a (circularArm a j) :=
  direction_checked ⟨a, by omega⟩ j

end PortAnnulus

namespace Plan

/-- The source's true cyclic port table has exactly the three incidences of its cell. -/
theorem Layer.circularPorts_length {l : Layer} (h : l.HasDrawing) :
    l.circularPorts.length = 3 := by
  simpa [Layer.circularPorts] using h.constraints.2.1

/-- Each clockwise slot is its actual numbered input or reversed output arm. -/
theorem Layer.circularPort_arm {l : Layer} (h : l.HasDrawing) (j : Fin 3) :
    l.circularPorts.getD j.val ⟨⟨0, false⟩, 0⟩ =
      if (PortAnnulus.circularArm l.instruction.data.inputs.length j).incoming then
        l.inputPort (PortAnnulus.circularArm l.instruction.data.inputs.length j).index
      else l.outputPort (PortAnnulus.circularArm l.instruction.data.inputs.length j).index := by
  have harity := h.constraints.2.1
  have hj := j.isLt
  by_cases hi : j.val < l.instruction.data.inputs.length
  · simp [Layer.circularPorts, PortAnnulus.circularArm, hi,
      List.getD_eq_getElem?_getD, List.getElem?_append]
  · have ho : j.val - l.instruction.data.inputs.length < l.instruction.data.outputs.length := by omega
    have hab : 3 - l.instruction.data.inputs.length = l.instruction.data.outputs.length := by omega
    simp [Layer.circularPorts, PortAnnulus.circularArm, hi, hab,
      List.getD_eq_getElem?_getD, List.getElem?_append, ho]

/-- Select one of the checked finite annulus curves from the actual source layer. -/
def Layer.annulusKey (l : Layer) (role : Fin 3) : PortAnnulus.Key :=
  ⟨PortAnnulus.pattern l.instruction.data.inputs.length, portRotation l.geometricVertex, role⟩

/-- The exact circular position of the source port used by a physical W/N/E role. -/
def Layer.cyclicIndex (l : Layer) (role : Fin 3) : Fin 3 :=
  ⟨((portRotation l.geometricVertex).val + role.val) % 3, Nat.mod_lt _ (by decide)⟩

/-- The chosen physical role retains the edge name and reference direction at that cyclic slot. -/
theorem Layer.annulus_port {l : Layer} (h : l.HasDrawing) (role : Fin 3) :
    (orderPorts l.geometricVertex).port role =
      (l.circularPorts.getD (l.cyclicIndex role).val ⟨⟨0, false⟩, 0⟩).port :=
  orderPorts_port_rotation l.geometricVertex (l.circularPorts_length h) role

/-- The finite annulus ends in exactly the direction of the selected actual source arm. -/
theorem Layer.annulus_direction {l : Layer} (h : l.HasDrawing) (role : Fin 3) :
    PortAnnulus.outerDirection (l.annulusKey role) =
      PortAnnulus.armDirection l.instruction.data.inputs.length
        (PortAnnulus.circularArm l.instruction.data.inputs.length (l.cyclicIndex role)) := by
  have ha : l.instruction.data.inputs.length ≤ 3 := by have := h.constraints.2.1; omega
  simpa only [Layer.annulusKey, Layer.cyclicIndex, PortAnnulus.outerDirection] using
    PortAnnulus.direction_circular _ ha (l.cyclicIndex role)

@[fun_prop] theorem Layer.annulusKey_polyTime :
    ComputableInPolyTime (fun q : Layer × Fin 3 => q.1.annulusKey q.2)
      (encPair encLayer encRole) PortAnnulus.encKey := by
  unfold Layer.annulusKey PortAnnulus.encKey
  fun_prop

end Plan
end PushPuzzle.PushFS.Reduction
