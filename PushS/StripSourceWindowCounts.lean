/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.StripSource
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite vertex-window budgets supplied by the actual standard strip drawing. -/

public section
namespace PushPuzzle.PushS.StripSource

open Cslib.Complexity

variable {g : NCL.AndOrGraph} (drawing : NCL.GridDrawing.Closed g.graph)
  (hpanel : ∀ panel, Nat.card {v // panel ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ panel + 1} ≤ 1)

include hpanel in
/-- The supplied unit-panel budget identifies each original vertex by its actual longitudinal row. -/
theorem vertex_row_injective : Function.Injective (fun v => (drawing.vertex v).2) := by
  intro a b he
  change (drawing.vertex a).2 = (drawing.vertex b).2 at he
  let r := (drawing.vertex a).2
  have hs : Subsingleton {v // r ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ r + 1} :=
    (Finite.card_le_one_iff_subsingleton).mp (hpanel r)
  have ha : r ≤ (drawing.vertex a).2 ∧ (drawing.vertex a).2 ≤ r + 1 := by dsimp only [r]; omega
  have hb : r ≤ (drawing.vertex b).2 ∧ (drawing.vertex b).2 ≤ r + 1 := by dsimp only [r]; omega
  exact congrArg Subtype.val (hs.elim ⟨a, ha⟩ ⟨b, hb⟩)

include hpanel in
/-- A window of `span+1` actual integer rows contains at most `span+1` original vertices. -/
theorem vertex_window_card_le (start span : ℕ) :
    Nat.card {v // start ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ start + span} ≤ span + 1 := by
  let f : {v // start ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ start + span} → Fin (span + 1) :=
    fun v => ⟨(drawing.vertex v.val).2 - start, by have := v.property; omega⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply vertex_row_injective drawing hpanel
    change (drawing.vertex a.val).2 = (drawing.vertex b.val).2
    have ha := a.property
    have hb := b.property
    have hh := congrArg Fin.val he
    change (drawing.vertex a.val).2 - start = (drawing.vertex b.val).2 - start at hh
    omega
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

include hpanel in
/-- The source-row neighborhood of one actual contour cut has at most `2*span+1` original vertices. -/
theorem vertex_neighborhood_card_le (center span : ℕ) :
    Nat.card {v // center ≤ (drawing.vertex v).2 + span ∧ (drawing.vertex v).2 ≤ center + span} ≤
      2 * span + 1 := by
  let f : {v // center ≤ (drawing.vertex v).2 + span ∧ (drawing.vertex v).2 ≤ center + span} →
      {v // center - span ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ center - span + 2 * span} :=
    fun v => ⟨v.val, by have := v.property; constructor <;> omega⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    change (f a).val = (f b).val
    exact congrArg Subtype.val he
  exact (Nat.card_le_card_of_injective f hf).trans (vertex_window_card_le drawing hpanel (center - span) (2 * span))

/-- Every accepted strip source retains these same local vertex-window budgets in its actual drawing. -/
theorem mem_vertex_windows {width span : ℕ} {x : Instance} (hx : x ∈ language width span) :
    ∃ drawing : NCL.GridDrawing.Closed x.ncl.graph.graph, drawing.orthogonalDrawing = x.drawing ∧
      ∀ start window, Nat.card {v // start ≤ (drawing.vertex v).2 ∧ (drawing.vertex v).2 ≤ start + window} ≤ window + 1 := by
  obtain ⟨drawing, he, _, _, hpanel, _, _⟩ := hx.2.2
  exact ⟨drawing, he, vertex_window_card_le drawing hpanel⟩

end PushPuzzle.PushS.StripSource
