/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.ProgramData
public import PushS.Source.Strip.Sweep.Context.Bits
public import PushS.Source.Strip.PolyTime.ConfigurationData

/-!
# Exact standard-data output configurations of the actual strip simulation

Read the same original source vector through actual unit-arc records. The standard-data
configuration emitter uses the same four boundary bits and finite canonical table at each
actual selected instruction. Its full output is exactly the existing native simulation's full
configuration, in the original native edge order.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.configurationData_bits`: same actual canonical created-edge stream.
* `PushPuzzle.NCL.Strip.Sweep.Context.configurationData_native`: same existing native simulation encoding.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib PolyTime

variable {A K : ℕ} (C : Context A K)

private theorem configurationData_signals (source : List Bool) (t : ℕ) :
    let u : Arc C.environment → Bool := fun a =>
      a.reversed C.environment ^^ source.getD a.edge.val false
    let sl := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))
    PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.signals A K ⟨C.routingMetadata, source⟩ t =
      PushPuzzle.NCL.Strip.Sweep.Cell.pack (sl.incoming.map u ++ sl.outgoing.map u) := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.signals
  rw [C.programData_siteInput]
  simp only [programDataInput, PushPuzzle.NCL.Strip.PolyTime.SliceData.ofSlice, List.map_append, List.map_map]
  apply congrArg PushPuzzle.NCL.Strip.Sweep.Cell.pack
  apply congrArg₂ (· ++ ·)
  all_goals apply List.map_congr_left
  all_goals intro a _
  all_goals exact PushPuzzle.NCL.Strip.PolyTime.ArcData.direction_ofArc C.environment source a

private theorem configurationData_stepBits (source : List Bool) (t : ℕ) :
    PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.stepBits A K ⟨C.routingMetadata, source⟩ t =
      C.stepConfiguration t (fun a =>
        a.reversed C.environment ^^ source.getD a.edge.val false) := by
  unfold PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.stepBits
  rw [C.programData_siteInput, C.programData_step, C.configurationData_signals]
  let u : Arc C.environment → Bool := fun a =>
    a.reversed C.environment ^^ source.getD a.edge.val false
  let sl := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))
  change ((instruction C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))).toList.map
      (fun ins => (ins.offset, ins.fragment.code))).flatMap
        (fun ins : ℕ × Fin 14 => PushPuzzle.NCL.Strip.Sweep.Cell.configuration ins.2
          (PushPuzzle.NCL.Strip.Sweep.Cell.pack (sl.incoming.map u ++ sl.outgoing.map u))) = _
  rw [List.flatMap_map]
  rfl

/-- Standard encoded configuration emission returns the same complete actual canonical stream.
-/
theorem configurationData_bits (source : List Bool) :
    PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.bits A K ⟨C.routingMetadata, source⟩ =
      C.canonicalBits (C.source.config source) := by
  rw [C.canonicalBits_steps]
  unfold PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.bits
  rw [C.programData_scanLength]
  apply List.flatMap_congr
  intro i _
  exact C.configurationData_stepBits source i

/-- The emitted standard vector is exactly the same existing native simulation configuration. -/
theorem configurationData_native (source : List Bool) :
    PushPuzzle.NCL.Strip.PolyTime.ConfigurationData.bits A K ⟨C.routingMetadata, source⟩ =
      List.ofFn (C.nativeSimulation.enc (C.source.config source)) :=
  (C.configurationData_bits source).trans (C.canonicalBits_eq _)

end PushPuzzle.NCL.Strip.Sweep.Context
