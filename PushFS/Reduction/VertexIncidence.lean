/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.ProgramSeparation

/-! Every emitted edge reaching a source vertex is one of that very vertex's actual weighted ports. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- At the actual star center, only its three real input/output arms can occur. -/
theorem Layer.vertex_port {l : Layer} (h : l.HasDrawing) {e : ℕ}
    (hp : Route.Trace l.connections e l.vertexPoint) :
    ∃ v ∈ emitted l, ∃ port ∈ v.ports, port.port.edge = e := by
  have hcenter : GridStar.center l.instruction.data.inputs.length ≤ 1 := by
    unfold GridStar.center
    split <;> omega
  have hgeo : ∃ port ∈ l.geometricVertex.ports, port.port.edge = e := by
    cases l.trace_classified h hp with
    | upper i _ ht =>
      have hh := ((l.upper_connects i).row_bounds ht).2
      change l.middleY + 1 ≤ l.middleY at hh
      omega
    | lower i _ ht =>
      have hh := ((l.lower_connects i).row_bounds ht).1
      change l.middleY + 2 ≤ l.middleY + 1 at hh
      omega
    | middle strand hn ht =>
      have hm := (l.middle_trace_iff strand l.vertexPoint).mp ht
      rcases strand with i | ((i | i) | i)
      · have hx := hm.2.1
        change 4 * l.instruction.data.offset + GridStar.center l.instruction.data.inputs.length = 4 * i.val at hx
        have := i.isLt
        omega
      · refine ⟨l.inputPort i.val, ?_, ?_⟩
        · change l.inputPort i.val ∈ (List.range l.instruction.data.inputs.length).map l.inputPort ++
            ((List.range l.instruction.data.outputs.length).map l.outputPort).reverse
          exact List.mem_append_left _ (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)
        · simpa [Layer.strandRoute, Layer.inputRoutes, List.getD_eq_getElem?_getD, i.isLt] using hn
      · refine ⟨l.outputPort i.val, ?_, ?_⟩
        · change l.outputPort i.val ∈ (List.range l.instruction.data.inputs.length).map l.inputPort ++
            ((List.range l.instruction.data.outputs.length).map l.outputPort).reverse
          exact List.mem_append_right _ (List.mem_reverse.mpr
            (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩))
        · simpa [Layer.strandRoute, Layer.outputRoutes, List.getD_eq_getElem?_getD, i.isLt] using hn
      · have hx := hm.2.1
        change 4 * l.instruction.data.offset + GridStar.center l.instruction.data.inputs.length =
          4 * l.instruction.data.offset + 4 + 4 * i.val at hx
        omega
  obtain ⟨port, hp, he⟩ := hgeo
  obtain ⟨v, hv, hperm⟩ := h.geometric_incidence
  exact ⟨v, by rw [hv]; simp, port, hperm.symm.subset hp, he⟩

end PushPuzzle.PushFS.Reduction.Plan
