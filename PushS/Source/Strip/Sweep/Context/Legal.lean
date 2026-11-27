/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Labels
public import PushS.Source.Strip.Sweep.Cell.Labels

/-!
# Labeled legality through the actual strip scan

All local diagrams and labels come from the same executed classifier. Boundary transport and
unchanged wires add no constraints, while consecutive scan positions contribute conjunctions.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.cellLabeling_legal`: only the selected local generator imposes constraints.
* `PushPuzzle.NCL.Strip.Sweep.Context.labeling_legal`: the actual closed diagram checks exactly its scan steps.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- The actual padded selected cell checks exactly its actual incoming/outgoing generator labels.
-/
theorem cellLabeling_legal (t : ℤ)
    (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site)
    (s : Arc C.environment → Bool) :
    let p := scanPoint K t
    let g := site.fragment C.graph C.arity C.color
    let x := (slice C.environment (List.finRange C.source.edgeCount) p).incoming
    let y := (slice C.environment (List.finRange C.source.edgeCount) p).outgoing
    let h := C.selection_interfaces (by
      simpa only [hc] using classify_spec C.environment (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K t))
    ((C.cellDiagram t site hc).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ (C.cellLabeling t site hc).label) ↔
      ((Diagram.gen g.generator).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
        (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.genLabeling g.generator x y
          (by rw [h.1, List.length_map]) (by rw [h.2, List.length_map])).label) := by
  simp only [cellDiagram, cellLabeling, PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_legal, PushPuzzle.NCL.Strip.Sweep.Cell.padLabeling_legal]

/-- Every actual scan prefix checks exactly the local labeled diagrams it contains. -/
private theorem prefixLabeling_legal (n : ℕ) (s : Arc C.environment → Bool) :
    ((C.diagramPrefix n).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ (C.prefixLabeling n).label) ↔
      ∀ i < n, ((C.stepDiagram i).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ (C.stepLabeling i).label) := by
  induction n with
  | zero =>
    constructor
    · intro _ i hi
      omega
    · intro _
      exact legal_id _ _
  | succ n ih =>
    change ((PushPuzzle.NCL.Strip.Sweep.Cell.retype ((C.diagramPrefix n).comp (C.stepDiagram n)) _ _).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
      (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling ((C.prefixLabeling n).comp (C.stepLabeling n)) _ _).label) ↔ _
    rw [PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_legal, Labeling.legal_comp, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hit : i < n
      · exact h i hit
      · have he : i = n := by omega
        subst i
        exact hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- The actual closed source diagram checks exactly the actual finite sequence of local frames.
-/
theorem labeling_legal (s : Arc C.environment → Bool) :
    (C.diagram.graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ C.labeling.label) ↔
      ∀ i < scanLength C.environment (List.finRange C.source.edgeCount),
        ((C.stepDiagram i).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ (C.stepLabeling i).label) := by
  change ((PushPuzzle.NCL.Strip.Sweep.Cell.retype (C.diagramPrefix _) _ _).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal
    (s ∘ (PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling (C.prefixLabeling _) _ _).label) ↔ _
  rw [PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_legal, C.prefixLabeling_legal]

end PushPuzzle.NCL.Strip.Sweep.Context
