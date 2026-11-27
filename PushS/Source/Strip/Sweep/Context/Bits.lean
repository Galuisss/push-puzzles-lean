/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Cell.Bits
public import PushS.Source.Strip.Sweep.Context.Correspondence
public import PushS.Source.Diagram.CompileBits

/-!
# Exact canonical configuration serialization of the actual strip program

Serialize the actual local open-simulation extensions in created-edge order. The complete
closed stream is the same existing native simulation's full configuration, with original
carrier directions rebased by each actual unit arc's reversal bit.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.canonicalBits`: actual created-edge extension of original source bits.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.canonicalBits_eq`: exact existing native simulation configuration.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- The actual canonical configuration bits in the expanded native graph's creation order. -/
@[expose] def canonicalBits (s : Fin C.source.edgeCount → Bool) : List Bool :=
  (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) C.labeling (fun a => a.reversed C.environment ^^ s a.edge)

private theorem expansionSimulation_bits (s : C.diagram.Edge → Bool) :
    List.ofFn (C.expansionSimulation.enc s) = PushPuzzle.NCL.Strip.Sweep.Cell.bitMap.bits C.diagram s := by
  have transport (w : Word)
      (h : (C.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 = w) :
      let S : ConstraintGraph.Simulation (C.diagram.graph PushPuzzle.NCL.Strip.Sweep.Cell.interp) w.compile.graph := h ▸
        ((substSimulation PushPuzzle.NCL.Strip.Sweep.Cell.expandOpenSim C.diagram).trans
          (compileSimulation Prim.interp (C.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)))
      List.ofFn (S.enc s) = PushPuzzle.NCL.Strip.Sweep.Cell.bitMap.bits C.diagram s := by
    cases h
    have he := compileSimulation_bits Prim.interp (C.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)
      ((substSimulation PushPuzzle.NCL.Strip.Sweep.Cell.expandOpenSim C.diagram).enc s)
    rw [Diagram.bits_closed] at he
    exact he
  exact transport C.program C.expanded_word

private theorem unitDiagramSimulation_enc (u : Arc C.environment → Bool) :
    C.unitDiagramSimulation.enc u = u ∘ C.labeling.label := by
  funext e
  change u (C.edgeEquiv e) = _
  rw [C.edgeEquiv_apply]
  rfl

/-- Actual canonical serialization is exactly the full existing native simulation configuration.
-/
theorem canonicalBits_eq (s : Fin C.source.edgeCount → Bool) :
    C.canonicalBits s = List.ofFn (C.nativeSimulation.enc s) := by
  have hu : (unitSimulation C.environment C.graph (fun e => (C.color e).weight)
      (fun e => by cases C.color e <;> decide) C.loopFree).enc s =
        (fun a => a.reversed C.environment ^^ s a.edge) := by
    funext a
    exact unitSimulation_enc _ _ _ _ _ s a
  have he : C.nativeSimulation.enc s = C.expansionSimulation.enc
      ((fun a => a.reversed C.environment ^^ s a.edge) ∘ C.labeling.label) := by
    change C.expansionSimulation.enc (C.unitDiagramSimulation.enc
      ((unitSimulation C.environment C.graph (fun e => (C.color e).weight)
        (fun e => by cases C.color e <;> decide) C.loopFree).enc s)) = _
    rw [hu, C.unitDiagramSimulation_enc]
  rw [he, C.expansionSimulation_bits]
  rfl

/-- The exact finite local configuration table selected by the same original instruction. -/
@[expose] def stepConfiguration (t : ℕ) (u : Arc C.environment → Bool) : List Bool :=
  let sl := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))
  (instruction C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K (t : ℤ))).toList.flatMap fun ins =>
      PushPuzzle.NCL.Strip.Sweep.Cell.configuration ins.fragment.code (PushPuzzle.NCL.Strip.Sweep.Cell.pack (sl.incoming.map u ++ sl.outgoing.map u))

private theorem emptyLabeling_bits (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) (u : Arc C.environment → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) (C.emptyLabeling t hc) u = [] := by
  change PushPuzzle.NCL.Strip.Sweep.Cell.bitMap.bits (C.emptyDiagram t hc) _ = []
  exact PushPuzzle.NCL.Strip.Sweep.Cell.bits_retype_id (C.frontierColors t) rfl
    (congrArg (List.map (fun a : Arc C.environment => C.color a.edge)) (C.empty_frontier t hc)) _

private theorem cellLabeling_bits (t : ℤ)
    (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site)
    (u : Arc C.environment → Bool) :
    let sl := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) (C.cellLabeling t site hc) u =
      PushPuzzle.NCL.Strip.Sweep.Cell.configuration (site.fragment C.graph C.arity C.color).code
        (PushPuzzle.NCL.Strip.Sweep.Cell.pack (sl.incoming.map u ++ sl.outgoing.map u)) := by
  let sl := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)
  let g := site.fragment C.graph C.arity C.color
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K t)
  have hi := C.selection_interfaces (p := scanPoint K t) (s := site)
    (by simpa only [hc] using hs)
  change (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap)
    (PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling
      (PushPuzzle.NCL.Strip.Sweep.Cell.padLabeling g.generator (fun a => C.color a.edge)
        sl.above sl.incoming sl.outgoing sl.below
        (by rw [hi.1, List.length_map]) (by rw [hi.2, List.length_map]))
      (C.cell_frontiers t site hc).1.symm (C.cell_frontiers t site hc).2.symm) u = _
  rw [PushPuzzle.NCL.Strip.Sweep.Cell.labelledBits_retype, PushPuzzle.NCL.Strip.Sweep.Cell.labelledBits_pad, PushPuzzle.NCL.Strip.Sweep.Cell.configuration_genLabeling]

/-- Each actual frame serializes the same local canonical table selected by its actual instruction.
-/
private theorem stepLabeling_bits (t : ℕ) (u : Arc C.environment → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) (C.stepLabeling (t : ℤ)) u = C.stepConfiguration t u := by
  change (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) (C.frame (t : ℤ)).labeling u = _
  apply C.frame_cases (t : ℤ)
    (fun F => (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) F.labeling u = C.stepConfiguration t u)
  · intro hc
    dsimp only [emptyFrame]
    rw [C.emptyLabeling_bits]
    simp only [stepConfiguration, instruction, hc, Option.map_none, Option.toList_none,
      List.flatMap_nil]
  · intro site hc
    dsimp only [cellFrame]
    rw [C.cellLabeling_bits]
    simp only [stepConfiguration, instruction, hc, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Actual local canonical configurations concatenate in the original grid scan order. -/
private theorem prefixLabeling_bits (n : ℕ) (u : Arc C.environment → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) (C.prefixLabeling n) u =
      (List.range n).flatMap (fun i => C.stepConfiguration i u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let h : (n : ℤ) + 1 = (n + 1 : ℕ) := by omega
    change (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap)
      (PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling ((C.prefixLabeling n).comp (C.stepLabeling n))
        rfl (congrArg C.frontierColors h)) u = _
    rw [PushPuzzle.NCL.Strip.Sweep.Cell.labelledBits_retype, (PushPuzzle.NCL.Diagram.BitMap.labelledBits_comp PushPuzzle.NCL.Strip.Sweep.Cell.bitMap), ih, C.stepLabeling_bits]
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]

/-- The actual complete closed stream consists of the actual local canonical configurations. -/
private theorem labeling_bits (u : Arc C.environment → Bool) :
    (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap) C.labeling u =
      (List.range (scanLength C.environment (List.finRange C.source.edgeCount))).flatMap
        (fun i => C.stepConfiguration i u) := by
  change (PushPuzzle.NCL.Diagram.BitMap.labelledBits PushPuzzle.NCL.Strip.Sweep.Cell.bitMap)
    (PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling
      (C.prefixLabeling (scanLength C.environment (List.finRange C.source.edgeCount)))
      (by simp only [frontierColors, frontier_zero, List.map_nil])
      (by simp only [frontierColors, frontier_scanLength, List.map_nil])) u = _
  rw [PushPuzzle.NCL.Strip.Sweep.Cell.labelledBits_retype, C.prefixLabeling_bits]

/-- The same native canonical configuration emits from the actual finite local tables in order.
-/
theorem canonicalBits_steps (s : Fin C.source.edgeCount → Bool) :
    C.canonicalBits s =
      (List.range (scanLength C.environment (List.finRange C.source.edgeCount))).flatMap
        (fun i => C.stepConfiguration i (fun a => a.reversed C.environment ^^ s a.edge)) :=
  C.labeling_bits _

end PushPuzzle.NCL.Strip.Sweep.Context
