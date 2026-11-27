/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip.Program
public import PushS.Source.Strip.Sweep.Context.ConfigurationData

/-!
# Polynomial-time exact canonical word-network strip configurations

The original numbered word-network directions feed the same actual strip configuration emitter.
Both native endpoint vectors are polynomial-time and read exactly the existing full simulation's
canonical orientations, in the existing native graph's edge order.

## Main definitions

* `PushPuzzle.NCL.HWord.Strip.Sweep.bits`: actual canonical native strip direction vector for one source word.

## Main results

* `PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_bits`: standard encoded configuration emission.
* `PushPuzzle.NCL.HWord.Strip.Sweep.bits_eq`: the same existing full canonical simulation orientation.
-/

public section

namespace PushPuzzle.NCL.HWord.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib SelectorNetwork.AndOr _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Original source metadata and the existing canonical numbered word-network directions. -/
@[expose] def configurationInput (n : ℕ) (word : List (Fin q)) :
    PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.Input where
  metadata := routingMetadata H hq n
  source := Program.bits (Metadata.stateBlocks H hq n word)

/-- The actual canonical strip direction vector for the same original source word. -/
@[expose] def bits (n : ℕ) (word : List (Fin q)) : List Bool :=
  PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.bits (vertexBudget q) (edgeBudget q)
    (configurationInput H hq n word)

private theorem computableInPolyTime_configurationInput :
    ComputableInPolyTime (fun p : ℕ × List (Fin q) => configurationInput H hq p.1 p.2)
      (Metadata.encStateInput q) PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.encInput := by
  have hm := (computableInPolyTime_routingMetadata H hq).comp
    (ComputableInPolyTime.fst encUnary (HWord.encWord q))
  have hs := Metadata.computableInPolyTime_bits H hq
  unfold configurationInput
  exact PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.encInput_mk_polyTime hm hs

/-- The same actual canonical native direction vector emits in standard polynomial time. -/
theorem computableInPolyTime_bits :
    ComputableInPolyTime (fun p : ℕ × List (Fin q) => bits H hq p.1 p.2)
      (Metadata.encStateInput q) (encList encBool) :=
  ((PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.computableInPolyTime_bits
    (vertexBudget q) (edgeBudget q)).comp (computableInPolyTime_configurationInput H hq)).of_enc_eq
      (fun _ => rfl)

/-- The standard emitter returns exactly the existing complete strip simulation's orientation.
-/
theorem bits_eq {n : ℕ} (word : List (Fin q)) (w : Fin n → Fin q)
    (hw : ∀ i, word.getD i.val ⟨0, hq⟩ = w i) :
    bits H hq n word = List.ofFn (orientation H hq w) := by
  let s : Fin (context (n := n) H hq).source.edgeCount → Bool :=
    (Numbering.simulation (PortGraph.network H n) (AndOr.rowSection H hq)
      (PortGraph.bandwidthCertificate H).order).enc (AndOr.orientation H hq w)
  have hs : Program.bits (Metadata.stateBlocks H hq n word) = List.ofFn s :=
    Metadata.bits_stateBlocks_eq H hq word w hw
  calc
    bits H hq n word = List.ofFn ((context (n := n) H hq).nativeSimulation.enc
        ((context H hq).source.config (Program.bits (Metadata.stateBlocks H hq n word)))) := by
      unfold bits configurationInput
      rw [routingMetadata_eq]
      exact (context H hq).configurationData_native _
    _ = List.ofFn ((context (n := n) H hq).nativeSimulation.enc s) := by
      rw [hs, AndOrGraph.config_ofFn]
    _ = List.ofFn (orientation H hq w) := rfl

/-- The canonical native vector has exactly one direction bit per actual output edge. -/
theorem length_bits (n : ℕ) (word : List (Fin q)) :
    (bits H hq n word).length = (program (n := n) H hq).compile.edgeCount := by
  rw [bits_eq H hq word (fun i : Fin n => word.getD i.val ⟨0, hq⟩) (fun _ => rfl)]
  exact List.length_ofFn

end PushPuzzle.NCL.HWord.Strip.Sweep
