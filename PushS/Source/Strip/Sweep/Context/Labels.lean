/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Diagram
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# Actual unit-arc labels through the typed sweep diagram

Local generators carry the actual incoming/outgoing unit-arc lists. Padding retains the unchanged
context, and stacking glues exactly matching labeled frontiers.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.stepLabeling`: actual unit labels on one padded grid cell.
* `PushPuzzle.NCL.Strip.Sweep.Context.labeling`: actual unit labels on the whole closed source diagram.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- Actual local labels are constructed with that same local padded diagram. -/
@[expose] def stepLabeling (t : ℤ) :
    Labeling (C.stepDiagram t) (C.frontier t) (C.frontier (t + 1)) := (C.frame t).labeling

/-- Glue actual local labels through the first `n` grid sites. -/
@[expose] def prefixLabeling : (n : ℕ) →
    Labeling (C.diagramPrefix n) (C.frontier 0) (C.frontier n)
  | 0 => Labeling.id _ _ (by simp only [frontierColors, frontier, List.length_map])
  | n + 1 =>
    let h : (n : ℤ) + 1 = (n + 1 : ℕ) := by omega
    let L := PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling ((prefixLabeling n).comp (C.stepLabeling n)) rfl
      (congrArg C.frontierColors h)
    { label := L.label
      top_eq := L.top_eq
      bot_eq := L.bot_eq.trans (congrArg C.frontier h) }

/-- The actual unit-arc labeling of the whole closed source diagram. -/
@[expose] def labeling : Labeling (Label := Arc C.environment) C.diagram [] [] :=
  let L := PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling
    (C.prefixLabeling (scanLength C.environment (List.finRange C.source.edgeCount)))
    (by simp only [frontierColors, frontier_zero, List.map_nil])
    (by simp only [frontierColors, frontier_scanLength, List.map_nil])
  { label := L.label
    top_eq := L.top_eq.trans (frontier_zero C.environment _)
    bot_eq := L.bot_eq.trans (frontier_scanLength C.environment _) }

/-- Every actual scan step creates exactly the outgoing labels of that same grid site. -/
theorem stepLabeling_created (t : ℤ) :
    (PushPuzzle.NCL.Diagram.createdLabels (C.stepDiagram t)) (C.stepLabeling t).label =
      (slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)).outgoing :=
  (C.frame t).created_eq

/-- The actual diagram prefix creates exactly the chronological outgoing arc stream. -/
private theorem prefixLabeling_created (n : ℕ) :
    (PushPuzzle.NCL.Diagram.createdLabels (C.diagramPrefix n)) (C.prefixLabeling n).label =
      (List.range n).flatMap (fun (i : ℕ) =>
        (slice C.environment (List.finRange C.source.edgeCount) (scanPoint K i)).outgoing) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [diagramPrefix, prefixLabeling, PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_created,
      PushPuzzle.NCL.Diagram.Labeling.createdLabels_comp, ih, stepLabeling_created, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The actual closed diagram's creation labels are exactly the actual unit-arc birth stream. -/
private theorem labeling_created :
    (PushPuzzle.NCL.Diagram.createdLabels C.diagram) C.labeling.label =
    births C.environment (List.finRange C.source.edgeCount) := by
  simp only [diagram, labeling, PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_created, prefixLabeling_created, births]

/-- The actual closed source diagram creates exactly one edge for each actual unit-arc birth. -/
theorem innerCount_births : C.diagram.innerCount =
    (births C.environment (List.finRange C.source.edgeCount)).length := by
  have h := congrArg List.length C.labeling_created
  simpa only [length_createdLabels] using h

/-- Number the actual diagram edges by their actual chronological unit-arc birth labels. -/
@[expose] def edgeEquiv : C.diagram.Edge ≃ Arc C.environment :=
  C.diagram.numEquiv.trans
    ((finCongr (by simpa only [List.length_nil, Nat.zero_add] using C.innerCount_births)).trans
      (birthEquiv C.environment (List.finRange C.source.edgeCount) (List.nodup_finRange _)
        (fun e => List.mem_finRange e)))

/-- The computable birth-based numbering is the actual propagated unit-arc labeling. -/
theorem edgeEquiv_apply (e : C.diagram.Edge) : C.edgeEquiv e = C.labeling.label e := by
  cases e with
  | inl e => exact Fin.elim0 e
  | inr e =>
    have h := get_createdLabels C.diagram C.labeling.label e
    simp only [labeling_created] at h
    have hi : (C.diagram.numEquiv (.inr e)).val = C.diagram.idx e := by
      rw [Diagram.numEquiv_val]
      simp only [Diagram.num, Diagram.name, Sum.elim_inr, List.length_nil, Nat.zero_add]
    simp only [edgeEquiv, Equiv.trans_apply, finCongr_apply, birthEquiv,
      List.Nodup.getEquivOfForallMemList_apply, List.get_eq_getElem, Fin.val_cast]
    simpa only [hi] using h

end PushPuzzle.NCL.Strip.Sweep.Context
