/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.SourceRails
public import PushFS.Gadgets.Wires.Soundness.Horizontal

/-! Complete finite horizontal-wire signals require only real source components and C1–C3, in any globally reoriented board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Soundness

variable {I : Instance} {L : Type} [Fintype L]

structure HorizontalRailGlyph (M : SlotMatching I L) (k : HorizontalKind) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+k.width≤I.width
  fit_y : dy+21≤I.height
  initialPhase : Bool
  targetPhase : Bool
  labels : Fin k.count↪L
  walls : (GridEmbedding.translate dx dy fit_x fit_y).WallsAgree (k.template.board ∅) I.board
  sources : ∀i,M.source (labels i)=(GridEmbedding.translate dx dy fit_x fit_y).cells (k.template.position initialPhase i)
  targets : ∀i,M.target (labels i)=(GridEmbedding.translate dx dy fit_x fit_y).cells (k.template.position targetPhase i)

namespace HorizontalRailGlyph

variable {M : SlotMatching I L} {k : HorizontalKind} (g : HorizontalRailGlyph M k)

theorem component (i j : Fin k.count) : component I.board (M.source (g.labels i))=component I.board (M.source (g.labels j)) := by
  rw [g.sources,g.sources]
  have hh:=HorizontalKind.slots_component k g.initialPhase i j
  exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hh.1,GridEmbedding.staticReach g.walls hh.2⟩

theorem position_row (k : HorizontalKind) (phase : Bool) (i : Fin k.count) : (k.template.position phase i).2.val=10 := by
  cases k <;> cases phase <;> rfl

/-- The real far and near source identities select the horizontal source SCC through C2. -/
private def rail : SourceRail M true (g.dy+10) where
  anchor:=g.labels k.first
  witness:=M.source (g.labels k.last)
  connected:=g.component k.last k.first
  different:=by
    intro he
    have ho:=HorizontalKind.ordered k g.initialPhase k.first k.last (by cases k <;> decide)
    rw [g.sources,g.sources] at he
    change g.dx+(k.template.position g.initialPhase k.last).1.val=g.dx+(k.template.position g.initialPhase k.first).1.val at he
    omega
  anchor_cross:=by
    rw [g.sources]
    change g.dy+(k.template.position g.initialPhase k.first).2.val=g.dy+10
    rw [position_row]

variable {S final : LabelledState L I.width I.height}

/-- Actual two-cell gaps follow from the true component witness and C1–C3. -/
private theorem gap (h : Successful M S final) (cert : Certificate I) (i j : Fin k.count)
    (hij : i<j) :
    (S.position (g.labels i)).1.val+2≤(S.position (g.labels j)).1.val := by
  apply g.rail.gap h cert (g.labels i) (g.labels j) (g.component i k.first) (g.component j k.first)
  rw [g.sources,g.sources]
  exact Nat.add_lt_add_left (k.ordered g.initialPhase i j hij) _

/-- The literal protected strip remains logically open throughout any actual successful path. -/
private theorem strip (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (r : Fin k.stripCount) :
    (S.position (g.labels (k.strip r).left)).1.val+1<g.dx+(k.strip r).lo ∨
    g.dx+(k.strip r).hi+1<(S.position (g.labels (k.strip r).right)).1.val := by
  have hb:=k.strip_bounds r
  have hw:=(k.strip_walls r).translate hb.1 (by decide) (by decide) g.dx g.dy g.fit_x g.fit_y g.walls
  apply g.rail.strip_good h cert ho _ _ (g.labels (k.strip r).left) (g.labels (k.strip r).right) hw
    (g.component _ k.first) (g.component _ k.first)
  · rw [g.sources,g.sources]
    exact Nat.add_lt_add_left (k.ordered g.initialPhase _ _ hb.2) _
  · rw [g.sources,g.sources]
    have hh:=k.strip_normal g.initialPhase r
    change g.dx+_+1<g.dx+_ ∨g.dx+_+1<g.dx+_
    omega
  · rw [g.targets,g.targets]
    have hh:=k.strip_normal g.targetPhase r
    change g.dx+_+1<g.dx+_ ∨g.dx+_+1<g.dx+_
    omega

/-- An input threshold forces the far output threshold at every actual successful state. -/
theorem signal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dx+3 ≤ (S.position (g.labels k.first)).1.val) :
    g.dx+k.span+1 ≤ (S.position (g.labels k.last)).1.val := by
  cases k with
  | straight =>
    have hg0 := g.gap h cert (0 : Fin 18) (1 : Fin 18) (by decide)
    have hg1 := g.gap h cert (1 : Fin 18) (2 : Fin 18) (by decide)
    have hg2 := g.gap h cert (2 : Fin 18) (3 : Fin 18) (by decide)
    have hg3 := g.gap h cert (3 : Fin 18) (4 : Fin 18) (by decide)
    have hg4 := g.gap h cert (4 : Fin 18) (5 : Fin 18) (by decide)
    have hg5 := g.gap h cert (5 : Fin 18) (6 : Fin 18) (by decide)
    have hg6 := g.gap h cert (6 : Fin 18) (7 : Fin 18) (by decide)
    have hg7 := g.gap h cert (7 : Fin 18) (8 : Fin 18) (by decide)
    have hg8 := g.gap h cert (8 : Fin 18) (9 : Fin 18) (by decide)
    have hg9 := g.gap h cert (9 : Fin 18) (10 : Fin 18) (by decide)
    have hg10 := g.gap h cert (10 : Fin 18) (11 : Fin 18) (by decide)
    have hg11 := g.gap h cert (11 : Fin 18) (12 : Fin 18) (by decide)
    have hg12 := g.gap h cert (12 : Fin 18) (13 : Fin 18) (by decide)
    have hg13 := g.gap h cert (13 : Fin 18) (14 : Fin 18) (by decide)
    have hg14 := g.gap h cert (14 : Fin 18) (15 : Fin 18) (by decide)
    have hg15 := g.gap h cert (15 : Fin 18) (16 : Fin 18) (by decide)
    have hg16 := g.gap h cert (16 : Fin 18) (17 : Fin 18) (by decide)
    have hs0 := g.strip h cert ho (0 : Fin 4)
    have hs1 := g.strip h cert ho (1 : Fin 4)
    have hs2 := g.strip h cert ho (2 : Fin 4)
    have hs3 := g.strip h cert ho (3 : Fin 4)
    change (S.position (g.labels 2)).1.val+1 < g.dx+8 ∨ g.dx+8+1 < (S.position (g.labels 3)).1.val at hs0
    change (S.position (g.labels 3)).1.val+1 < g.dx+11 ∨ g.dx+11+1 < (S.position (g.labels 4)).1.val at hs1
    change (S.position (g.labels 11)).1.val+1 < g.dx+28 ∨ g.dx+28+1 < (S.position (g.labels 12)).1.val at hs2
    change (S.position (g.labels 12)).1.val+1 < g.dx+31 ∨ g.dx+31+1 < (S.position (g.labels 13)).1.val at hs3
    change g.dx+3 ≤ (S.position (g.labels 0)).1.val at hin
    change g.dx+40+1 ≤ (S.position (g.labels 17)).1.val
    omega
  | parity =>
    have hg0 := g.gap h cert (0 : Fin 26) (1 : Fin 26) (by decide)
    have hg1 := g.gap h cert (1 : Fin 26) (2 : Fin 26) (by decide)
    have hg2 := g.gap h cert (2 : Fin 26) (3 : Fin 26) (by decide)
    have hg3 := g.gap h cert (3 : Fin 26) (4 : Fin 26) (by decide)
    have hg4 := g.gap h cert (4 : Fin 26) (5 : Fin 26) (by decide)
    have hg5 := g.gap h cert (5 : Fin 26) (6 : Fin 26) (by decide)
    have hg6 := g.gap h cert (6 : Fin 26) (7 : Fin 26) (by decide)
    have hg7 := g.gap h cert (7 : Fin 26) (8 : Fin 26) (by decide)
    have hg8 := g.gap h cert (8 : Fin 26) (9 : Fin 26) (by decide)
    have hg9 := g.gap h cert (9 : Fin 26) (10 : Fin 26) (by decide)
    have hg10 := g.gap h cert (10 : Fin 26) (11 : Fin 26) (by decide)
    have hg11 := g.gap h cert (11 : Fin 26) (12 : Fin 26) (by decide)
    have hg12 := g.gap h cert (12 : Fin 26) (13 : Fin 26) (by decide)
    have hg13 := g.gap h cert (13 : Fin 26) (14 : Fin 26) (by decide)
    have hg14 := g.gap h cert (14 : Fin 26) (15 : Fin 26) (by decide)
    have hg15 := g.gap h cert (15 : Fin 26) (16 : Fin 26) (by decide)
    have hg16 := g.gap h cert (16 : Fin 26) (17 : Fin 26) (by decide)
    have hg17 := g.gap h cert (17 : Fin 26) (18 : Fin 26) (by decide)
    have hg18 := g.gap h cert (18 : Fin 26) (19 : Fin 26) (by decide)
    have hg19 := g.gap h cert (19 : Fin 26) (20 : Fin 26) (by decide)
    have hg20 := g.gap h cert (20 : Fin 26) (21 : Fin 26) (by decide)
    have hg21 := g.gap h cert (21 : Fin 26) (22 : Fin 26) (by decide)
    have hg22 := g.gap h cert (22 : Fin 26) (23 : Fin 26) (by decide)
    have hg23 := g.gap h cert (23 : Fin 26) (24 : Fin 26) (by decide)
    have hg24 := g.gap h cert (24 : Fin 26) (25 : Fin 26) (by decide)
    have hs0 := g.strip h cert ho (0 : Fin 5)
    have hs1 := g.strip h cert ho (1 : Fin 5)
    have hs2 := g.strip h cert ho (2 : Fin 5)
    have hs3 := g.strip h cert ho (3 : Fin 5)
    have hs4 := g.strip h cert ho (4 : Fin 5)
    change (S.position (g.labels 2)).1.val+1 < g.dx+8 ∨ g.dx+8+1 < (S.position (g.labels 3)).1.val at hs0
    change (S.position (g.labels 3)).1.val+1 < g.dx+11 ∨ g.dx+11+1 < (S.position (g.labels 4)).1.val at hs1
    change (S.position (g.labels 11)).1.val+1 < g.dx+28 ∨ g.dx+28+1 < (S.position (g.labels 12)).1.val at hs2
    change (S.position (g.labels 12)).1.val+1 < g.dx+31 ∨ g.dx+31+1 < (S.position (g.labels 13)).1.val at hs3
    change (S.position (g.labels 18)).1.val+1 < g.dx+44 ∨ g.dx+46+1 < (S.position (g.labels 19)).1.val at hs4
    change g.dx+3 ≤ (S.position (g.labels 0)).1.val at hin
    change g.dx+59+1 ≤ (S.position (g.labels 25)).1.val
    omega
  | flip =>
    have hg0 := g.gap h cert (0 : Fin 9) (1 : Fin 9) (by decide)
    have hg1 := g.gap h cert (1 : Fin 9) (2 : Fin 9) (by decide)
    have hg2 := g.gap h cert (2 : Fin 9) (3 : Fin 9) (by decide)
    have hg3 := g.gap h cert (3 : Fin 9) (4 : Fin 9) (by decide)
    have hg4 := g.gap h cert (4 : Fin 9) (5 : Fin 9) (by decide)
    have hg5 := g.gap h cert (5 : Fin 9) (6 : Fin 9) (by decide)
    have hg6 := g.gap h cert (6 : Fin 9) (7 : Fin 9) (by decide)
    have hg7 := g.gap h cert (7 : Fin 9) (8 : Fin 9) (by decide)
    have hs0 := g.strip h cert ho (0 : Fin 2)
    have hs1 := g.strip h cert ho (1 : Fin 2)
    change (S.position (g.labels 2)).1.val+1 < g.dx+8 ∨ g.dx+8+1 < (S.position (g.labels 3)).1.val at hs0
    change (S.position (g.labels 3)).1.val+1 < g.dx+11 ∨ g.dx+11+1 < (S.position (g.labels 4)).1.val at hs1
    change g.dx+3 ≤ (S.position (g.labels 0)).1.val at hin
    change g.dx+20+1 ≤ (S.position (g.labels 8)).1.val
    omega


end HorizontalRailGlyph
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
