/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.ProgramData
public import PushS.Source.Strip.Sweep.Cell.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Standard encoded canonical strip configuration emission

Read each actual original carrier bit, rebase it by the actual unit-arc reversal, and retain the
four ordered local input/output directions. The actual selected finite cell emits the canonical
created-edge configuration supplied by its existing open simulation.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.Input`: original metadata and original direction list.
* `PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.bits`: actual finite local configurations in scan order.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.computableInPolyTime_bits`: standard encoded emission.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime.ConfigurationData

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

/-- Original standard source data and one original edge-direction list. -/
structure Input where
  /-- The original source records and actual source/owner rows. -/
  metadata : RoutingMetadata
  /-- Original directions, in the same original edge order. -/
  source : List Bool

/-- Original routing data and a standard framed list of original edge directions. -/
enc_structure encInput : Input where metadata : encRoutingMetadata, source : (encList encBool)

/-- Four actual ordered local boundary directions, rebased from their original carriers. -/
@[expose] def signals (A K : ℕ) (input : Input) (t : ℕ) : PushPuzzle.NCL.Strip.Sweep.Cell.Signals :=
  let sl := (PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K input.metadata t).slice
  PushPuzzle.NCL.Strip.Sweep.Cell.pack ((sl.incoming ++ sl.outgoing).map (PushPuzzle.NCL.Strip.PolyTime.ArcData.direction input.source))

/-- Emit the selected actual local canonical created-edge configurations. -/
@[expose] def stepBits (A K : ℕ) (input : Input) (t : ℕ) : List Bool :=
  (PushPuzzle.NCL.Strip.PolyTime.ProgramData.step A K (PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K input.metadata t)).flatMap fun ins =>
    PushPuzzle.NCL.Strip.Sweep.Cell.configuration ins.2 (signals A K input t)

/-- Emit all actual canonical created-edge bits in the original complete scan order. -/
@[expose] def bits (A K : ℕ) (input : Input) : List Bool :=
  (List.range (PushPuzzle.NCL.Strip.PolyTime.ProgramData.scanLength A K input.metadata)).flatMap (stepBits A K input)

private theorem computableInPolyTime_siteInput (A K : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K p.1.metadata p.2)
      (encPair encInput encUnary) PushPuzzle.NCL.Strip.PolyTime.ProgramData.encSiteInput := by
  exact ((PushPuzzle.NCL.Strip.PolyTime.ProgramData.computableInPolyTime_siteInput A K).comp
    ((encInput_metadata_polyTime (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))).of_enc_eq (fun _ => rfl)

/-- The exact four local source directions are read in standard polynomial time. -/
private theorem computableInPolyTime_signals (A K : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => signals A K p.1 p.2)
      (encPair encInput encUnary) PushPuzzle.NCL.Strip.Sweep.Cell.encSignals := by
  have hs := PushPuzzle.NCL.Strip.PolyTime.ProgramData.encSiteInput_slice_polyTime (computableInPolyTime_siteInput A K)
  have hl : ComputableInPolyTime (fun p : Input × ℕ =>
      (PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K p.1.metadata p.2).slice.incoming ++
        (PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K p.1.metadata p.2).slice.outgoing)
      (encPair encInput encUnary) (encList encArcData) := by fun_prop
  have hb : ComputableInPolyTime (fun p : Input × ℕ =>
      ((PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K p.1.metadata p.2).slice.incoming ++
        (PushPuzzle.NCL.Strip.PolyTime.ProgramData.siteInput A K p.1.metadata p.2).slice.outgoing).map
          (PushPuzzle.NCL.Strip.PolyTime.ArcData.direction p.1.source)) (encPair encInput encUnary) (encList encBool) := by
    apply ComputableInPolyTime.mapWithInput hl
    fun_prop
  exact (PushPuzzle.NCL.Strip.Sweep.Cell.computableInPolyTime_pack.comp hb).of_enc_eq (fun _ => rfl)

/-- Each actual selected finite configuration chunk emits in standard polynomial time. -/
private theorem computableInPolyTime_stepBits (A K : ℕ) :
    ComputableInPolyTime (fun p : Input × ℕ => stepBits A K p.1 p.2)
      (encPair encInput encUnary) (encList encBool) := by
  have hc := (PushPuzzle.NCL.Strip.PolyTime.ProgramData.computableInPolyTime_step A K).comp
    (computableInPolyTime_siteInput A K)
  unfold stepBits
  apply ComputableInPolyTime.flatMapWithInput hc
  have hop : ComputableInPolyTime (fun p : (Input × ℕ) × (ℕ × Fin 14) => p.2.2)
      (encPair (encPair encInput encUnary)
        (encPair encUnary PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode)) (encFinEnum (Fin 14)) := by
    exact ((ComputableInPolyTime.snd _ _).snd').of_enc_eq (fun _ => rfl)
  have hs := (computableInPolyTime_signals A K).comp
    (ComputableInPolyTime.fst (encPair encInput encUnary)
      (encPair encUnary PushPuzzle.NCL.Strip.Sweep.Cell.language.encOpcode))
  exact (PushPuzzle.NCL.Strip.Sweep.Cell.computableInPolyTime_configuration.comp (hop.prod hs)).of_enc_eq
    (fun _ => rfl)

/-- The complete actual canonical bit stream emits in standard encoded polynomial time. -/
theorem computableInPolyTime_bits (A K : ℕ) :
    ComputableInPolyTime (bits A K) encInput (encList encBool) := by
  have hn := (PushPuzzle.NCL.Strip.PolyTime.ProgramData.computableInPolyTime_scanLength A K).comp
    (encInput_metadata_polyTime ComputableInPolyTime.id')
  unfold bits
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  exact computableInPolyTime_stepBits A K

end PushPuzzle.NCL.Strip.PolyTime.ConfigurationData
