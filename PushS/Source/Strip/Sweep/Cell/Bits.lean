/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Cell.Code
public import PushS.Source.Strip.Sweep.Context.Frame
public import PushS.Source.Diagram.Labeling.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD

/-!
# Actual canonical configuration table of the finite strip cells

Each raw cell has at most four ordered boundary edges. Retain those four input/output direction
bits and serialize the exact canonical extension supplied by the existing local open simulation.
The finite table is polynomial-time under the standard finite-code and fixed-function encodings.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Cell.bitMap`: creation-order serialization of the actual standard substitution.
* `PushPuzzle.NCL.Strip.Sweep.Cell.configuration`: the actual local canonical extension table.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Cell.computableInPolyTime_configuration`: the standard finite-table time bound.
* `PushPuzzle.NCL.Strip.Sweep.Cell.orientation_pack`: exact original ordered boundary directions.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram _root_.Turing.MultiTapeTM

/-- The actual local substitutions serialize their created edges compositionally. -/
@[expose] def bitMap : Diagram.BitMap Cell where
  bits D s := (openSimSubst expandOpenSim D).bits s
  bits_id _ _ := rfl
  bits_comp _ _ _ := OpenSim.bits_comp _ _ _
  bits_tensor _ _ _ := OpenSim.bits_tensor _ _ _

/-- Four ordered original boundary direction bits. -/
abbrev Signals := Fin 4 → Bool

/-- Standard canonical-order fixed-function encoding of the four direction bits. -/
abbrev encSignals : Signals ↪ List Bool := encFinFn 4 encBool

/-- Retain the four actual ordered boundary directions, padding shorter boundaries with false. -/
@[expose] def pack (bits : List Bool) : Signals := fun i => bits.getD i.val false

/-- Packing the fixed-size boundary signal table is standard encoded polynomial-time. -/
theorem computableInPolyTime_pack : ComputableInPolyTime pack (encList encBool) encSignals := by
  apply ComputableInPolyTime.finFn
  intro i
  unfold pack
  fun_prop

/-- Read ordered input directions followed by ordered output directions on the original raw cell.
-/
@[expose] def Fragment.orientation (g : Fragment) (signals : Signals) :
    (Diagram.gen g.generator).Edge → Bool :=
  Sum.elim (fun i => (List.ofFn signals).getD i.val false)
    (fun j => (List.ofFn signals).getD (g.inputs.length + j.val) false)

/-- The actual canonical created-edge configuration of one existing finite-code implementation.
-/
@[expose] def configuration (code : Fin 14) (signals : Signals) : List Bool :=
  let g := alphabet.get code
  (expandOpenSim g.generator).bits (g.orientation signals)

/-- The exact canonical local extension table is polynomial-time under standard finite encodings.
-/
theorem computableInPolyTime_configuration :
    ComputableInPolyTime (fun p : Fin 14 × Signals => configuration p.1 p.2)
      (encPair (encFinEnum (Fin 14)) encSignals) (encList encBool) :=
  ComputableInPolyTime.of_finite _

/-- The selected original code uses the same existing original local open simulation. -/
private theorem configuration_code (g : Fragment) (signals : Signals) :
    configuration g.code signals = (expandOpenSim g.generator).bits (g.orientation signals) := by
  unfold configuration
  rw [get_code]

private theorem boundary_length (g : Fragment) : g.inputs.length + g.outputs.length ≤ 4 := by
  rcases g with ⟨a, b, g⟩
  cases g <;> simp

private theorem get_pack (bits : List Bool) (i : ℕ) (hi : i < 4) :
    (List.ofFn (pack bits)).getD i false = bits.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some,
    pack]

/-- Packing actual input/output lists preserves every original ordered raw-cell direction. -/
theorem orientation_pack {Label : Type*} (g : Fragment) (x y : List Label)
    (hx : x.length = g.inputs.length) (hy : y.length = g.outputs.length) (u : Label → Bool) :
    g.orientation (pack (x.map u ++ y.map u)) =
      u ∘ (genLabeling g.generator x y hx hy).label := by
  have hn := boundary_length g
  funext e
  rcases e with i | j
  · have hi : i.val < 4 := by omega
    have hix : i.val < (x.map u).length := by simpa only [List.length_map, hx] using i.isLt
    change (List.ofFn (pack (x.map u ++ y.map u))).getD i.val false = _
    rw [get_pack _ _ hi, List.getD_append _ _ _ _ hix]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
    simp only [List.getElem_map, Option.getD_some, Function.comp_def, genLabeling]
    rfl
  · have hj : g.inputs.length + j.val < 4 := by omega
    have hiy : j.val < (y.map u).length := by simpa only [List.length_map, hy] using j.isLt
    change (List.ofFn (pack (x.map u ++ y.map u))).getD (g.inputs.length + j.val) false = _
    rw [get_pack _ _ hj, List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
    simp only [List.length_map, ← hx, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiy]
    simp only [List.getElem_map, Option.getD_some, Function.comp_def, genLabeling]
    rfl

/-- The original labeled local raw cell serializes exactly its finite canonical table entry. -/
theorem configuration_genLabeling {Label : Type*} (g : Fragment) (x y : List Label)
    (hx : x.length = g.inputs.length) (hy : y.length = g.outputs.length) (u : Label → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits bitMap) (genLabeling g.generator x y hx hy) u =
      configuration g.code (pack (x.map u ++ y.map u)) := by
  rw [configuration_code]
  change (expandOpenSim g.generator).bits (u ∘ (genLabeling g.generator x y hx hy).label) = _
  rw [orientation_pack]

/-- Equal colored-boundary transport retains the same actual canonical configuration stream. -/
theorem labelledBits_retype {Label : Type*} {a b a' b' : List Color}
    {D : Diagram Cell a b} {x y : List Label} (L : Labeling D x y)
    (ha : a = a') (hb : b = b') (u : Label → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits bitMap) (retypeLabeling L ha hb) u = (PushPuzzle.NCL.Diagram.BitMap.labelledBits bitMap) L u := by
  cases ha
  cases hb
  rfl

/-- Transported identity wires create no canonical configuration bits, for every orientation. -/
theorem bits_retype_id (a : List Color) {a' b' : List Color} (ha : a = a') (hb : a = b')
    (s : (retype (Diagram.id (Γ := Cell) a) ha hb).Edge → Bool) :
    bitMap.bits (retype (Diagram.id a) ha hb) s = [] := by
  cases ha
  cases hb
  rfl

/-- Actual unchanged prefix/suffix wires contribute no created canonical configuration bits. -/
theorem labelledBits_pad {Label : Type*} {a b : List Color} (g : Cell a b)
    (color : Label → Color) (pre x y post : List Label)
    (hx : x.length = a.length) (hy : y.length = b.length) (u : Label → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits bitMap) (padLabeling g color pre x y post hx hy) u =
      (PushPuzzle.NCL.Diagram.BitMap.labelledBits bitMap) (genLabeling g x y hx hy) u := by
  change (PushPuzzle.NCL.Diagram.BitMap.labelledBits bitMap)
    ((Labeling.id (Γ := Cell) (pre.map color) pre (by simp)).tensor
      ((genLabeling g x y hx hy).tensor (Labeling.id (post.map color) post (by simp)))) u = _
  rw [(PushPuzzle.NCL.Diagram.BitMap.labelledBits_tensor bitMap), (PushPuzzle.NCL.Diagram.BitMap.labelledBits_tensor bitMap),
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits_id bitMap), (PushPuzzle.NCL.Diagram.BitMap.labelledBits_id bitMap)]
  simp only [List.nil_append, List.append_nil]

end PushPuzzle.NCL.Strip.Sweep.Cell
