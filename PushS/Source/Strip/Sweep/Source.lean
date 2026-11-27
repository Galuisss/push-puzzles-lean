/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Vertices

/-!
# Source cells of the actual constraint-graph sweep

The three boundary labels are the original port-list slots. Their weights come from the same
original graph color scan, their minimum inflow is two, and their reference-direction changes
are the actual reversals of the incident unit arcs.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.source_cell`: actual input/output lists, weights, threshold, and port directions.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Planar.Embedding

/-- The actual source sweep cell retains the three original weighted incidences in slot order. -/
theorem source_cell {m A K : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i))
    (hAnd : ∀ v ∈ vs, v.IsAndOr)
    (vertexRows : Fin vs.length → ℕ) (ownerRows : Fin m → ℕ)
    (hA : ∀ r, Fintype.card {i // vertexRows i = r} ≤ A)
    (hK : ∀ r, Fintype.card {e // ownerRows e = r} ≤ K)
    (hrows : ∀ i p, p ∈ (vs.get i).ports →
      ownerRows p.1.edge ≤ vertexRows i ∧ vertexRows i ≤ ownerRows p.1.edge + 1)
    (i : Fin vs.length) :
    let h3 := fun j : Fin vs.length => (hAnd _ (List.get_mem vs j)).shape.1.le
    let R := ofConstraintGraph vs hw hl h3 vertexRows ownerRows hA hK hrows
    let ps := fun s : Fin 3 => (vs.get i).ports.get
      (s.cast (hAnd _ (List.get_mem vs i)).shape.1.symm)
    (slice R (List.finRange m) (R.center i)).incoming = [portArc R (ps 0).1.edge (ps 0).1.dir] ∧
      (slice R (List.finRange m) (R.center i)).outgoing =
        [portArc R (ps 1).1.edge (ps 1).1.dir, portArc R (ps 2).1.edge (ps 2).1.dir] ∧
      (vs.get i).minInflow = 2 ∧
      (∀ s, (ps s).2 = (color vs (ps s).1.edge).weight) ∧
      ∀ s, ((portArc R (ps s).1.edge (ps s).1.dir).reversed R ^^ (ps s).1.dir) =
        decide (s = 0) := by
  dsimp only
  let h3 := fun j : Fin vs.length => (hAnd _ (List.get_mem vs j)).shape.1.le
  let R := ofConstraintGraph vs hw hl h3 vertexRows ownerRows hA hK hrows
  let ps := fun s : Fin 3 => (vs.get i).ports.get
    (s.cast (hAnd _ (List.get_mem vs i)).shape.1.symm)
  have hslots (s : Fin 3) : R.endpoint (ps s).1.edge (ps s).1.dir = i ∧
      R.port (ps s).1.edge (ps s).1.dir = s := by
    have h := incidencePort_eq_of_get vs hw h3 i
      (s.cast (hAnd _ (List.get_mem vs i)).shape.1.symm)
    exact ⟨h.1, Fin.ext h.2⟩
  refine ⟨?_, ?_, (hAnd _ (List.get_mem vs i)).shape.2, ?_, ?_⟩
  · have h := source_incoming_eq R (List.nodup_finRange m)
      (List.mem_finRange (ps 0).1.edge) (hslots 0).2
    simpa only [(hslots 0).1] using h
  · have h := source_outgoing_eq R (List.nodup_finRange m)
      (List.mem_finRange (ps 1).1.edge) (List.mem_finRange (ps 2).1.edge)
      ((hslots 1).1.trans (hslots 2).1.symm) (hslots 1).2 (hslots 2).2
    simpa only [(hslots 1).1] using h
  · intro s
    exact port_weight_color hAnd hw (List.get_mem _ _) (List.get_mem _ _)
  · intro s
    simpa only [(hslots s).2] using portArc_dir R (ps s).1.edge (ps s).1.dir

end PushPuzzle.NCL.Strip.Sweep
