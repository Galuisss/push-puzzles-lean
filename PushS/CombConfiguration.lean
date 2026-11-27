/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTopologyPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-!
# Actual native configurations in the emitted contour order

Retain the source direction on every original edge. Its tips and the two sides of each actual
tooth crossing receive the corresponding alternating axis bits; a local rotation retains the
actual original core port on its inside and the complementary bit on its outside.

## Main definitions

* `Comb.ConfigurationInput`: the actual native graph/drawing and its direction vector.
* `Comb.ConfigurationInput.axes`: bits in the actual emitted contour order.

## Main results

* `Comb.computableInPolyTime_axes`: standard polynomial-time axis-vector emission.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal _root_.Turing.MultiTapeTM

/-- The actual original native graph/drawing and one original edge direction vector. -/
structure ConfigurationInput where
  /-- The original native graph and its original drawing arrays. -/
  input : Input
  /-- Directions in the original native edge order. -/
  bits : List Bool

/-- Standard native graph/drawing data followed by the framed native direction vector. -/
enc_structure encConfigurationInput : ConfigurationInput where
  input : encInput, bits : (encList encBool)

/-- The axis supplies the upper page exactly when the original port receives no inflow. -/
@[expose] def ConfigurationInput.portBit (x : ConfigurationInput) (p : NCL.Port ℕ) : Bool :=
  x.bits.getD p.edge false ^^ p.dir

/-- The original prepared segment's actual traversal direction. -/
private def segmentForward (width : ℕ) (input : Input) (edge slot : ℕ) : Bool :=
  let r := (prepare width input.drawing).2.getD edge []
  let ab := r.consecutivePairs.getD slot ((0, 0), (0, 0))
  decide (ab.1.1 < ab.2.1)

/-- The exact original incidence carried by a local rotation's inside token. -/
private def rotationPort (width : ℕ) (input : Input) (vertex : ℕ) : NCL.Port ℕ :=
  (((coreBlock width input vertex).core.ports.filter
    (fun p => p.1 == Token.rotation vertex true)).map (fun p => p.2.1)).headD ⟨0, false⟩

/-- The original direction at one actual contour token, with true supplying the upper page. -/
def ConfigurationInput.tokenBit (width : ℕ) (x : ConfigurationInput) : Token → Bool
  | .tip edge dir => x.portBit ⟨edge, dir⟩
  | .mark edge slot _ side =>
    x.bits.getD edge false ^^ (segmentForward width x.input edge slot ^^ side)
  | .rotation vertex inside =>
    let bit := x.portBit (rotationPort width x.input vertex)
    if inside then bit else !bit

/-- The complete actual axis vector in the same contour order used by the port compiler. -/
@[expose] def ConfigurationInput.axes (width : ℕ) (x : ConfigurationInput) : List Bool :=
  (cut width x.input).order.map (x.tokenBit width)

@[local fun_prop] private theorem computableInPolyTime_xor :
    ComputableInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
      (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _

@[local fun_prop] private theorem computableInPolyTime_nativeBit :
    ComputableInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
      (encPair (encList encBool) encNat) encBool :=
  ComputableInPolyTime.listGetD_binary false
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _)

/-- Original weighted incidences read the same native direction vector in polynomial time. -/
theorem computableInPolyTime_portBit :
    ComputableInPolyTime (fun p : ConfigurationInput × NCL.Port ℕ => p.1.portBit p.2)
      (encPair encConfigurationInput (NCL.encPort encNat)) encBool := by
  unfold ConfigurationInput.portBit
  fun_prop

private theorem computableInPolyTime_segmentForward (width : ℕ) :
    ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => segmentForward width p.1.1 p.1.2 p.2)
      (encPair (encPair encInput encNat) encUnary) encBool := by
  have hprep := computableInPolyTime_prepare width
  have hr : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ =>
      (prepare width p.1.1.drawing).2.getD p.1.2 [])
      (encPair (encPair encInput encNat) encUnary) encRoute := by
    apply ComputableInPolyTime.listGetD_binary (encL := encList encRoute) []
    · unfold Graph.encOrthogonalDrawing at hprep
      fun_prop
    · fun_prop
  have hz : ComputableInPolyTime (List.consecutivePairs (α := Point))
      encRoute (encList (encPair encPoint encPoint)) := by
    unfold List.consecutivePairs encRoute
    fun_prop
  have hpairs := hz.comp hr
  have hab : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ =>
      (((prepare width p.1.1.drawing).2.getD p.1.2 []).consecutivePairs.getD p.2
        ((0, 0), (0, 0)))) (encPair (encPair encInput encNat) encUnary)
      (encPair encPoint encPoint) :=
    ComputableInPolyTime.listGetDWithInput hpairs (ComputableInPolyTime.snd _ _) _
  have htest : ComputableInPolyTime (fun p : Point × Point => decide (p.1.1 < p.2.1))
      (encPair encPoint encPoint) encBool := by unfold encPoint; fun_prop
  exact (htest.comp hab).of_enc_eq (fun _ => rfl)

private theorem computableInPolyTime_rotationPort (width : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => rotationPort width p.1 p.2)
      (encPair encInput encUnary) (NCL.encPort encNat) := by
  unfold rotationPort
  fun_prop

private abbrev encMarkSide :=
  encPair encConfigurationInput (encPair encUnary (encPair encUnary (encPair encUnary encBool)))

private theorem computableInPolyTime_markBit (width : ℕ) :
    ComputableInPolyTime
      (fun p : ConfigurationInput × (ℕ × (ℕ × (ℕ × Bool))) => p.1.bits.getD p.2.1 false ^^
        (segmentForward width p.1.input p.2.1 p.2.2.1 ^^ p.2.2.2.2)) encMarkSide encBool := by
  have he : ComputableInPolyTime
      (fun p : ConfigurationInput × (ℕ × (ℕ × (ℕ × Bool))) => p.2.1) encMarkSide encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold encMarkSide; fun_prop)
  have hi : ComputableInPolyTime
      (fun p : ConfigurationInput × (ℕ × (ℕ × (ℕ × Bool))) => ((p.1.input, p.2.1), p.2.2.1))
      encMarkSide (encPair (encPair encInput encNat) encUnary) := by
    unfold encMarkSide at he ⊢
    fun_prop
  have hb : ComputableInPolyTime
      (fun p : ConfigurationInput × (ℕ × (ℕ × (ℕ × Bool))) => p.1.bits.getD p.2.1 false)
      encMarkSide encBool := computableInPolyTime_nativeBit.comp
        ((encConfigurationInput_bits_polyTime (ComputableInPolyTime.fst _ _)).prod he)
  have hs := (computableInPolyTime_segmentForward width).comp hi
  have hside : ComputableInPolyTime
      (fun p : ConfigurationInput × (ℕ × (ℕ × (ℕ × Bool))) => p.2.2.2.2) encMarkSide encBool := by
    unfold encMarkSide
    fun_prop
  exact computableInPolyTime_xor.comp (hb.prod
    (computableInPolyTime_xor.comp (hs.prod hside)))

private theorem computableInPolyTime_rotationBit (width : ℕ) :
    ComputableInPolyTime (fun p : ConfigurationInput × (ℕ × Bool) =>
      if p.2.2 then p.1.portBit (rotationPort width p.1.input p.2.1)
      else !(p.1.portBit (rotationPort width p.1.input p.2.1)))
      (encPair encConfigurationInput (encPair encUnary encBool)) encBool := by
  have hx := ComputableInPolyTime.fst encConfigurationInput (encPair encUnary encBool)
  have hv := (ComputableInPolyTime.fst encUnary encBool).comp
    (ComputableInPolyTime.snd encConfigurationInput (encPair encUnary encBool))
  have hi := (encConfigurationInput_input_polyTime hx).prod hv
  have hp := (computableInPolyTime_rotationPort width).comp hi
  have hb := computableInPolyTime_portBit.comp
    ((ComputableInPolyTime.fst encConfigurationInput (encPair encUnary encBool)).prod hp)
  have hside : ComputableInPolyTime (fun p : ConfigurationInput × (ℕ × Bool) => p.2.2)
      (encPair encConfigurationInput (encPair encUnary encBool)) encBool := by fun_prop
  have hf : ComputableInPolyTime (fun p : Bool × Bool => if p.1 then p.2 else !p.2)
      (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
  exact (hf.comp (hside.prod hb)).of_enc_eq (by
    intro p
    simp only [Function.comp_apply])

/-- The actual contour token's signed source bit emits in standard polynomial time. -/
theorem computableInPolyTime_tokenBit (width : ℕ) :
    ComputableInPolyTime (fun p : ConfigurationInput × Token => p.1.tokenBit width p.2)
      (encPair encConfigurationInput encToken) encBool := by
  have hp := computableInPolyTime_portBit
  have h := encToken_elim_polyTime (encP := encConfigurationInput) (encE := encBool)
    (g0 := fun p => p.1.portBit ⟨p.2.1, p.2.2⟩)
    (g1 := fun p => p.1.bits.getD p.2.1 false ^^
      (segmentForward width p.1.input p.2.1 p.2.2.1 ^^ p.2.2.2.2))
    (g2 := fun p => if p.2.2 then p.1.portBit (rotationPort width p.1.input p.2.1)
      else !(p.1.portBit (rotationPort width p.1.input p.2.1)))
    (by fun_prop) (computableInPolyTime_markBit width) (computableInPolyTime_rotationBit width)
  exact h.of_enc_eq (by intro p; rcases p with ⟨x, token⟩; cases token <;> rfl)

/-- The complete same contour's source axis vector emits in standard polynomial time. -/
theorem computableInPolyTime_axes (width : ℕ) :
    ComputableInPolyTime (ConfigurationInput.axes width) encConfigurationInput (encList encBool) := by
  unfold ConfigurationInput.axes
  apply ComputableInPolyTime.mapWithInput
    (encCut_order_polyTime ((computableInPolyTime_cut width).comp
      (encConfigurationInput_input_polyTime ComputableInPolyTime.id')))
  exact computableInPolyTime_tokenBit width

/-- There is exactly one emitted axis bit per actual contour port. -/
theorem length_axes (width : ℕ) (x : ConfigurationInput) :
    (x.axes width).length = (compile width x.input).portCount := by
  exact List.length_map _

end PushPuzzle.PushS.Comb
