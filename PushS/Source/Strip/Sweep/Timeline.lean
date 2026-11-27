/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Labeling.Extension
public import PushS.Source.Strip.Sweep.Context.Frame
public import PushS.Source.Strip.Sweep.VertexLabels

/-!
# Constructed stage labels through the actual local replacements

Boundary edges retain their actual birth labels through an open implementation. New internal
edges receive their implementation stage. Stacking glues equal actual boundary labels and
retains the assigned stage of each actual output vertex.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.TimelineLabeling`: actual edge owners and vertex stages with a proved local window.
* `PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.ofOpenSim`: construct a stage window for a local implementation.
* `PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.comp`: compose actual adjacent implementation stages.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Constructed actual edge labels and output-vertex stages with a proved port window. -/
structure TimelineLabeling {a b : List Color} (D : Diagram Prim a b) (radius : ℕ)
    (xs ys : List ℤ) where
  /-- Actual edge-owner labels at the two explicit boundaries. -/
  labels : Labeling D xs ys
  /-- Actual scan stage assigned to each output vertex. -/
  stage : D.Vtx Prim.interp → ℕ
  /-- Each actual incidence lies between its owner stage and that stage plus the fixed radius. -/
  localPort : ∀ v p, p ∈ (D.graph Prim.interp v).ports →
    labels.label p.1.edge ≤ stage v ∧ (stage v : ℤ) ≤ labels.label p.1.edge + radius

namespace TimelineLabeling

open Cslib.Complexity Cslib.Complexity.NCL

variable {a b c : List Color} {D : Diagram Prim a b} {D' : Diagram Prim b c}
  {radius : ℕ} {xs ys zs : List ℤ}

private theorem window_map {E E' : Type*} (v : Vertex E) (f : E → E') (row : ℕ)
    (owner : E' → ℤ) (h : ∀ p ∈ v.ports,
      (owner ∘ f) p.1.edge ≤ row ∧ (row : ℤ) ≤ (owner ∘ f) p.1.edge + radius) :
    ∀ p ∈ (v.map f).ports, owner p.1.edge ≤ row ∧ (row : ℤ) ≤ owner p.1.edge + radius := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

/-- Stack two actual timelines at equal actual edge-owner boundary lists. -/
@[expose] def comp (L : TimelineLabeling D radius xs ys) (M : TimelineLabeling D' radius ys zs) :
    TimelineLabeling (D.comp D') radius xs zs where
  labels := L.labels.comp M.labels
  stage := Sum.elim L.stage M.stage
  localPort := by
    rintro (v | v)
    · apply window_map (D.graph Prim.interp v) (compLeft D D')
      rw [Labeling.comp_label_left]
      exact L.localPort v
    · apply window_map (D'.graph Prim.interp v) (compRight D D')
      rw [Labeling.comp_label_right]
      exact M.localPort v

/-- An actual local implementation retains all old birth labels and owns its new internal edges.
-/
@[expose] noncomputable def ofOpenSim {Γ : List Color → List Color → Type} {I : Interp Γ}
    {a b : List Color} {S : Diagram Γ a b} {T : Diagram Prim a b} {xs ys : List ℤ}
    (L : Labeling S xs ys) (R : OpenSim I Prim.interp S T) (t : ℕ)
    (hL : ∀ e, L.label e ≤ t ∧ (t : ℤ) ≤ L.label e + radius) :
    TimelineLabeling T radius xs ys where
  labels := (PushPuzzle.NCL.Diagram.Labeling.extend L) R (fun _ => t)
  stage _ := t
  localPort := by
    intro _ p _
    by_cases he : ∃ e, R.ι e = p.1.edge
    · obtain ⟨e, he⟩ := he
      simp only [← he, PushPuzzle.NCL.Diagram.Labeling.extend_label_image]
      exact hL e
    · simp only [PushPuzzle.NCL.Diagram.Labeling.extend_label_not_image _ _ _ _ he]
      exact ⟨le_rfl, by omega⟩

/-- Equal boundary-owner lists retain every actual edge and vertex-stage assignment. -/
@[expose] def castLabels (L : TimelineLabeling D radius xs ys) {xs' ys' : List ℤ}
    (hx : xs = xs') (hy : ys = ys') : TimelineLabeling D radius xs' ys' where
  labels := ⟨L.labels.label, L.labels.top_eq.trans hx, L.labels.bot_eq.trans hy⟩
  stage := L.stage
  localPort := L.localPort

/-- Retyping equal raw colored boundaries retains the actual expanded implementation timeline. -/
@[expose] def retypeRaw {a b a' b' : List Color} {D : Diagram Cell a b} {xs ys : List ℤ}
    (L : TimelineLabeling (D.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) radius xs ys) (ha : a = a') (hb : b = b') :
    TimelineLabeling ((PushPuzzle.NCL.Strip.Sweep.Cell.retype D ha hb).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) radius xs ys := by
  cases ha
  cases hb
  exact L

/-- Raw boundary retyping preserves the actual compilation-order vertex stages. -/
theorem vertexLabels_retypeRaw {a b a' b' : List Color} {D : Diagram Cell a b} {xs ys : List ℤ}
    (L : TimelineLabeling (D.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) radius xs ys) (ha : a = a') (hb : b = b') :
    vertexLabels Prim.interp ((PushPuzzle.NCL.Strip.Sweep.Cell.retype D ha hb).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)
        (L.retypeRaw ha hb).stage = vertexLabels Prim.interp (D.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) L.stage := by
  cases ha
  cases hb
  rfl

/-- Equal owner lists preserve the actual compilation-order vertex stages. -/
theorem vertexLabels_castLabels (L : TimelineLabeling D radius xs ys) {xs' ys' : List ℤ}
    (hx : xs = xs') (hy : ys = ys') :
    vertexLabels Prim.interp D (L.castLabels hx hy).stage =
      vertexLabels Prim.interp D L.stage := rfl

/-- Actual stacked timeline stages concatenate in the same actual vertex compilation order. -/
theorem vertexLabels_comp (L : TimelineLabeling D radius xs ys)
    (M : TimelineLabeling D' radius ys zs) :
    vertexLabels Prim.interp (D.comp D') (L.comp M).stage =
      vertexLabels Prim.interp D L.stage ++ vertexLabels Prim.interp D' M.stage := rfl

end TimelineLabeling
end PushPuzzle.NCL.Strip.Sweep
