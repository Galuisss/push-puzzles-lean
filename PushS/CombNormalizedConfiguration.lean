/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombConfigurationCore
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-!
# Normalized actual core demands in contour order

When the original heavy edge supplies an AND core, withdraw both light core inputs. A light
incidence represented by an inside rotation withdraws its demand there and supplies the outside
ordinary wire instead. Every original vertex block retains its actual token order.

## Main definitions

* `Comb.ConfigurationInput.normalizedAxes`: actual contour directions with normalized core inputs.

## Main results

* `Comb.computableInPolyTime_normalizedAxes`: standard polynomial-time normalized emission.
* `Comb.length_normalizedAxes`: exactly one bit per actual emitted port.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal _root_.Turing.MultiTapeTM

private structure CoreQuery where
  source : ConfigurationInput
  vertex : ℕ

private enc_structure encCoreQuery : CoreQuery where
  source : encConfigurationInput, vertex : encUnary

private def CoreQuery.core (width : ℕ) (q : CoreQuery) : Core :=
  (coreBlock width q.source.input q.vertex).core

private def heavyDemand (p : ConfigurationInput × Core) : Bool :=
  p.2.kind == .andGate && p.2.ports.any
    (fun (_, ⟨port, weight⟩) => weight == 2 && !(p.1.portBit port))

private def lightDemands (core : Core) : List Token :=
  (core.ports.filter (fun tp => tp.2.2 == 1)).map Prod.fst

private structure Demand where
  heavy : Bool
  light : List Token
  vertex : ℕ
  token : Token
  raw : Bool

private enc_structure encDemand : Demand where
  heavy : encBool, light : (encList encToken), vertex : encUnary, token : encToken, raw : encBool

private def Demand.bit (d : Demand) : Bool :=
  if d.heavy then
    if d.light.contains d.token then true
    else if d.light.contains (.rotation d.vertex true) &&
        d.token == .rotation d.vertex false then false
    else d.raw
  else d.raw

private def CoreQuery.heavySupplied (width : ℕ) (q : CoreQuery) : Bool :=
  heavyDemand (q.source, q.core width)

private def CoreQuery.lightTokens (width : ℕ) : CoreQuery → List Token :=
  lightDemands ∘ CoreQuery.core width

private def CoreQuery.demand (width : ℕ) (q : CoreQuery) (token : Token) : Demand :=
  ⟨q.heavySupplied width, q.lightTokens width, q.vertex, token, q.source.tokenBit width token⟩

private def CoreQuery.tokenBit (width : ℕ) (q : CoreQuery) (token : Token) : Bool :=
  (q.demand width token).bit

/-- The original native heavy direction supplies this same actual AND core. -/
def ConfigurationInput.heavySupplied (width : ℕ) (x : ConfigurationInput) (vertex : ℕ) : Bool :=
  (CoreQuery.mk x vertex).heavySupplied width

/-- The normalized direction at one actual token in its original vertex block. -/
def ConfigurationInput.normalizedTokenBit (width : ℕ) (x : ConfigurationInput)
    (vertex : ℕ) (token : Token) : Bool :=
  (CoreQuery.mk x vertex).tokenBit width token

private def CoreQuery.axes (width : ℕ) (q : CoreQuery) : List Bool :=
  (vertexBlock width q.source.input q.vertex).order.map (q.tokenBit width)

/-- Actual contour directions with both light demands withdrawn at every supplied-heavy AND core.
-/
def ConfigurationInput.normalizedAxes (width : ℕ) (x : ConfigurationInput) : List Bool :=
  (vertexOrder width x.input.drawing).flatMap fun sv => (CoreQuery.mk x sv.2).axes width

private theorem computableInPolyTime_core (width : ℕ) :
    ComputableInPolyTime (CoreQuery.core width) encCoreQuery encCore := by
  have hi : ComputableInPolyTime (fun q : CoreQuery => (q.source.input, q.vertex))
      encCoreQuery (encPair encInput encUnary) := by fun_prop
  exact (encBlock_core_polyTime ((computableInPolyTime_coreBlock width).comp hi)).of_enc_eq (by
    intro q
    simp only [CoreQuery.core, Function.comp_apply])

private theorem computableInPolyTime_heavyDemand :
    ComputableInPolyTime heavyDemand (encPair encConfigurationInput encCore) encBool := by
  have hp := encCore_ports_polyTime (ComputableInPolyTime.snd encConfigurationInput encCore)
  have ht : ComputableInPolyTime (fun p : ConfigurationInput × Core => p.2.ports.any
      (fun (_, ⟨port, weight⟩) => weight == 2 && !(p.1.portBit port)))
      (encPair encConfigurationInput encCore) encBool := by
    apply ComputableInPolyTime.anyWithInput hp
    have hi : ComputableInPolyTime
        (fun p : (ConfigurationInput × Core) × (Token × (NCL.WeightedPort ℕ)) => (p.1.1, p.2.2.1))
        (encPair (encPair encConfigurationInput encCore)
          (encPair encToken (NCL.encWeightedPort encNat)))
        (encPair encConfigurationInput (NCL.encPort encNat)) := by fun_prop
    have hb := computableInPolyTime_portBit.comp hi
    have hw : ComputableInPolyTime
        (fun p : (ConfigurationInput × Core) × (Token × (NCL.WeightedPort ℕ)) => p.2.2.2)
        (encPair (encPair encConfigurationInput encCore)
          (encPair encToken (NCL.encWeightedPort encNat))) encNat := by fun_prop
    have hf : ComputableInPolyTime (fun p : ℕ × Bool => p.1 == 2 && !p.2)
        (encPair encNat encBool) encBool := by fun_prop
    exact (hf.comp (hw.prod hb)).of_enc_eq (by
      intro p
      rcases p with ⟨⟨source, core⟩, token, port, weight⟩
      simp only [Function.comp_apply])
  have hk := encCore_kind_polyTime (ComputableInPolyTime.snd encConfigurationInput encCore)
  have hf : ComputableInPolyTime (fun p : Shuttle.Kind × Bool => p.1 == .andGate && p.2)
      (encPair Shuttle.encKind encBool) encBool := ComputableInPolyTime.of_finite _
  exact (hf.comp (hk.prod ht)).of_enc_eq (by
    intro p
    simp only [heavyDemand, Function.comp_apply])

private theorem computableInPolyTime_heavySupplied (width : ℕ) :
    ComputableInPolyTime (CoreQuery.heavySupplied width) encCoreQuery encBool := by
  have hi := (encCoreQuery_source_polyTime ComputableInPolyTime.id').prod
    (computableInPolyTime_core width)
  exact (computableInPolyTime_heavyDemand.comp hi).of_enc_eq (by
    intro q
    simp only [CoreQuery.heavySupplied, Function.comp_apply])

private theorem computableInPolyTime_lightDemands :
    ComputableInPolyTime lightDemands encCore (encList encToken) := by
  have hp := encCore_ports_polyTime ComputableInPolyTime.id'
  have hf : ComputableInPolyTime
      (fun c : Core => c.ports.filter (fun tp => tp.2.2 == 1)) encCore
      (encList (encPair encToken (NCL.encWeightedPort encNat))) := by
    apply ComputableInPolyTime.filterWithInput hp
    have hw : ComputableInPolyTime (fun p : Core × (Token × (NCL.WeightedPort ℕ)) => p.2.2.2)
        (encPair encCore (encPair encToken (NCL.encWeightedPort encNat))) encNat := by
      fun_prop
    have he : ComputableInPolyTime (fun n : ℕ => n == 1) encNat encBool := by fun_prop
    exact he.comp hw
  have hm : ComputableInPolyTime (fun p : Core × (Token × (NCL.WeightedPort ℕ)) => p.2.1)
      (encPair encCore (encPair encToken (NCL.encWeightedPort encNat))) encToken := by
    fun_prop
  exact (ComputableInPolyTime.mapWithInput (f := fun _ tp => tp.1) hf hm).of_enc_eq (by
    intro c
    simp only [lightDemands])

private theorem computableInPolyTime_lightTokens (width : ℕ) :
    ComputableInPolyTime (CoreQuery.lightTokens width) encCoreQuery (encList encToken) := by
  exact computableInPolyTime_lightDemands.comp (computableInPolyTime_core width)

private theorem computableInPolyTime_demandBit :
    ComputableInPolyTime Demand.bit encDemand encBool := by
  unfold Demand.bit
  fun_prop

private theorem computableInPolyTime_normalizedToken (width : ℕ) :
    ComputableInPolyTime (fun p : CoreQuery × Token => p.1.tokenBit width p.2)
      (encPair encCoreQuery encToken) encBool := by
  have hq := ComputableInPolyTime.fst encCoreQuery encToken
  have hheavy := (computableInPolyTime_heavySupplied width).comp hq
  have hlight := (computableInPolyTime_lightTokens width).comp hq
  have hi : ComputableInPolyTime (fun p : CoreQuery × Token => (p.1.source, p.2))
      (encPair encCoreQuery encToken) (encPair encConfigurationInput encToken) := by fun_prop
  have hraw := (computableInPolyTime_tokenBit width).comp hi
  have hd := encDemand_mk_polyTime hheavy hlight (encCoreQuery_vertex_polyTime hq)
    (ComputableInPolyTime.snd encCoreQuery encToken) hraw
  exact (computableInPolyTime_demandBit.comp hd).of_enc_eq (by
    intro p
    simp only [CoreQuery.tokenBit, CoreQuery.demand, Function.comp_apply])

private theorem computableInPolyTime_normalizedBlock (width : ℕ) :
    ComputableInPolyTime (CoreQuery.axes width) encCoreQuery (encList encBool) := by
  have hi : ComputableInPolyTime (fun q : CoreQuery => (q.source.input, q.vertex))
      encCoreQuery (encPair encInput encUnary) := by fun_prop
  have hs := encBlock_order_polyTime ((computableInPolyTime_vertexBlock width).comp hi)
  unfold CoreQuery.axes
  exact ComputableInPolyTime.mapWithInput hs (computableInPolyTime_normalizedToken width)

/-- The actual normalized contour direction vector emits in standard polynomial time. -/
theorem computableInPolyTime_normalizedAxes (width : ℕ) :
    ComputableInPolyTime (ConfigurationInput.normalizedAxes width)
      encConfigurationInput (encList encBool) := by
  have hd := encInput_drawing_polyTime
    (encConfigurationInput_input_polyTime ComputableInPolyTime.id')
  have hv := (computableInPolyTime_vertexOrder width).comp hd
  unfold ConfigurationInput.normalizedAxes
  apply ComputableInPolyTime.flatMapWithInput hv
  have hq : ComputableInPolyTime
      (fun p : ConfigurationInput × (Point × ℕ) => CoreQuery.mk p.1 p.2.2)
      (encPair encConfigurationInput (encPair encPoint encUnary)) encCoreQuery := by
    apply encCoreQuery_mk_polyTime <;> fun_prop
  exact (computableInPolyTime_normalizedBlock width).comp hq

/-- The normalization preserves the same actual contour and allocates exactly its port count. -/
theorem length_normalizedAxes (width : ℕ) (x : ConfigurationInput) :
    (x.normalizedAxes width).length = (compile width x.input).portCount := by
  simp only [ConfigurationInput.normalizedAxes, CoreQuery.axes, List.length_flatMap,
    List.length_map]
  simp only [compile, Cut.toLayout, cut, List.length_flatMap, List.map_map, Function.comp_def]

end PushPuzzle.PushS.Comb
