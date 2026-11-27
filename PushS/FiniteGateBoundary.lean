/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateFlipReadout

/-! The true outer working boxes read legal AND/OR signals on every successful path. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateReadout

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateCore
open PushFS.Gadgets.Wires.Soundness

variable {I : PushFS.Instance} {Label : Type} [Fintype Label]
    {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}

attribute [local irreducible] side

namespace AndGlyph

variable (g : AndGlyph M A w) {S final : LabelledState Label I.width I.height}

def outerA : Label := g.labels (.west ⟨w+3, by omega⟩)
def outerB : Label := g.labels (.branchB ⟨4*w+15, by omega⟩)
def outerC : Label := g.labels (.branchC ⟨w+4, by omega⟩)

/-- The near-core A signal reaches the literal protection-corner vertical box. -/
theorem a_to_protection (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (hw : 2 ≤ w)
    (hA : (S.position g.a).1.val < g.dx+junction w true) :
    (S.position (g.labels (.lower ⟨w+4, by omega⟩))).2.val+2 ≤ g.mainY := by
  have hDA : (S.position g.d).1.val+2 ≤ (S.position g.a).1.val := by
    apply g.rail_gap h cert true (origin w) (.guard ⟨3*w+4, by omega⟩) .triggerA rfl rfl rfl
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [key, andCell, andPoint]
    unfold origin
    omega
  have hguard := g.guard_span h cert ⟨3*w+4, by omega⟩
  have hF : (S.position (g.guard 0)).1.val ≤ g.mainX+1 := by
    change (S.position (g.guard 0)).1.val+2*(3*w+4) ≤ (S.position g.d).1.val at hguard
    dsimp [mainX, junction, origin] at *
    omega
  exact (g.protection_corner_good h cert ho hw).resolve_left (by omega)

/-- The near protection-arm threshold traverses both long vertical tails, the flip, and upper turn. -/
private theorem protection_to_outer (h : Successful M S final) (cert : Certificate I)
    (ho : M.Ordered) (hw : 2 ≤ w)
    (hG : (S.position (g.labels (.lower ⟨w+4, by omega⟩))).2.val+2 ≤ g.mainY) :
    (S.position g.outerA).1.val ≤ g.dx+(origin w-8*w-17) := by
  have hlower := g.lower_span h cert ⟨w+4, by omega⟩
  have hH : (S.position (g.labels (.lower 0))).2.val ≤ g.flipY+w-1 := by
    change _+2*(w+4) ≤ _ at hlower
    dsimp [mainY, flipY, origin] at *
    omega
  have hJ := g.flip_signal h cert ho hw hH
  have hupper := g.upper_span h cert ⟨w+4, by omega⟩
  have hG2 : (S.position (g.labels (.upper 0))).2.val ≤ g.upperY+1 := by
    change _+2*(w+4) ≤ _ at hupper
    dsimp [flipY, upperY, origin] at *
    omega
  have hF2 := (g.upper_corner_good h cert ho hw).resolve_right (by omega)
  have hwest := g.west_span h cert ⟨w+3, by omega⟩
  change (S.position g.outerA).1.val+2*(w+3) ≤ _ at hwest
  dsimp [mainX, origin] at hF2 ⊢
  omega

/-- The actual core A threshold reaches the true outer endpoint of its complete branch. -/
private theorem a_to_outer (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hw : 2 ≤ w)
    (hA : (S.position g.a).1.val < g.dx+junction w true) :
    (S.position g.outerA).1.val ≤ g.dx+(origin w-8*w-17) :=
  g.protection_to_outer h cert ho hw (g.a_to_protection h cert ho hw hA)

private theorem b_to_outer (h : Successful M S final) (cert : Certificate I)
    (hB : (S.position g.b).2.val+1 < g.mainY) :
    (S.position g.outerB).2.val ≤ g.dy+(origin w-8*w-32) := by
  have hb := g.branchB_span h cert ⟨4*w+15, by omega⟩
  change (S.position g.outerB).2.val+2*(4*w+15) ≤ (S.position g.b).2.val at hb
  dsimp [mainY, origin] at *
  omega

private theorem c_to_outer (h : Successful M S final) (cert : Certificate I)
    (hC : g.dx+rightBoundary w true+1 ≤ (S.position g.c).1.val) :
    g.dx+origin w+3*w+13 ≤ (S.position g.outerC).1.val := by
  have hc := g.branchC_span h cert ⟨w+4, by omega⟩
  change (S.position g.c).1.val+2*(w+4) ≤ (S.position g.outerC).1.val at hc
  dsimp [rightBoundary] at hC
  omega

/-- All three physical boundary boxes use their actual outward normal-slot thresholds. -/
def boundarySignals (S : LabelledState Label I.width I.height) : Gates.Signals :=
  ⟨decide ((S.position g.outerA).1.val ≤ g.dx+(origin w-8*w-17)),
   decide ((S.position g.outerB).2.val ≤ g.dy+(origin w-8*w-32)),
   decide ((S.position g.outerC).1.val < g.dx+origin w+3*w+13)⟩

/-- The real outer AND ports obey the NCL gate constraint throughout arbitrary successful motion. -/
theorem boundary_legal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (hw : 2 ≤ w)
    (hstart : Gates.legal true g.initialSignals) (hfinish : Gates.legal true g.targetSignals) :
    Gates.legal true (g.boundarySignals S) := by
  intro hblue
  have hb : (S.position g.outerC).1.val < g.dx+origin w+3*w+13 := of_decide_eq_true hblue
  have hc : (S.position g.c).1.val ≤ g.dx+rightBoundary w true := by
    by_contra hh
    have ht := g.c_to_outer h cert (by omega)
    omega
  have hg := g.good h cert ho hw hstart hfinish hc
  have ha := g.a_to_outer h cert ho hw hg.1
  have hB := g.b_to_outer h cert hg.2
  exact ⟨decide_eq_true ha, decide_eq_true hB⟩

private theorem boundarySignals_normal (U : LabelledState Label I.width I.height)
    (bits : Gates.Signals)
    (hpos : ∀ l : AndLabel w, U.position (g.labels l) = g.toThickGateGlyph.embedding.cells
      (andCell w bits.left bits.upper bits.right l)) : g.boundarySignals U = bits := by
  unfold boundarySignals outerA outerB outerC
  simp only [hpos]
  rcases bits with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    simp [ThickGateGlyph.embedding, GridEmbedding.translate, andCell, andPoint, origin] <;> omega

theorem boundarySignals_source : g.boundarySignals M.initialLabelled = g.initialSignals :=
  g.boundarySignals_normal _ _ g.sources

theorem boundarySignals_target (ht : final.position = M.target) :
    g.boundarySignals final = g.targetSignals := by
  apply g.boundarySignals_normal
  intro l
  rw [ht]
  exact g.targets l

end AndGlyph

namespace OrGlyph

variable (g : OrGlyph M A w) {S final : LabelledState Label I.width I.height}

def outerA : Label := g.labels (.left ⟨w+4, by omega⟩)
def outerB : Label := g.labels (.branchB ⟨w+6, by omega⟩)
def outerC : Label := g.labels (.branchC ⟨w+4, by omega⟩)

private theorem a_to_outer (h : Successful M S final) (cert : Certificate I)
    (hA : (S.position g.a).1.val+1 < g.dx+junction w false) :
    (S.position g.outerA).1.val ≤ g.dx+(origin w-2*w-8) := by
  have hDA : (S.position (g.labels (.left 0))).1.val+2 ≤ (S.position g.a).1.val := by
    apply g.rail_gap h cert true (origin w) (.left 0) .triggerA rfl rfl rfl
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [key, orCell, orPoint]
    unfold origin
    omega
  have ht := g.left_span h cert ⟨w+4, by omega⟩
  change (S.position g.outerA).1.val+2*(w+4) ≤ _ at ht
  dsimp [junction, origin] at hA ⊢
  omega

private theorem b_to_outer (h : Successful M S final) (cert : Certificate I)
    (hB : (S.position g.b).2.val+1 < g.dy+origin w) :
    (S.position g.outerB).2.val ≤ g.dy+(origin w-2*w-14) := by
  have hb := g.branchB_span h cert ⟨w+6, by omega⟩
  change (S.position g.outerB).2.val+2*(w+6) ≤ (S.position g.b).2.val at hb
  unfold origin at *
  omega

private theorem c_to_outer (h : Successful M S final) (cert : Certificate I)
    (hC : g.dx+rightBoundary w false+1 ≤ (S.position g.c).1.val) :
    g.dx+origin w+3*w+14 ≤ (S.position g.outerC).1.val := by
  have hc := g.branchC_span h cert ⟨w+4, by omega⟩
  change (S.position g.c).1.val+2*(w+4) ≤ (S.position g.outerC).1.val at hc
  dsimp [rightBoundary] at hC
  omega

def boundarySignals (S : LabelledState Label I.width I.height) : Gates.Signals :=
  ⟨decide ((S.position g.outerA).1.val ≤ g.dx+(origin w-2*w-8)),
   decide ((S.position g.outerB).2.val ≤ g.dy+(origin w-2*w-14)),
   decide ((S.position g.outerC).1.val < g.dx+origin w+3*w+14)⟩

theorem boundary_legal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (hw : 2 ≤ w)
    (hstart : Gates.legal false g.initialSignals) (hfinish : Gates.legal false g.targetSignals) :
    Gates.legal false (g.boundarySignals S) := by
  intro hblue
  have hb : (S.position g.outerC).1.val < g.dx+origin w+3*w+14 := of_decide_eq_true hblue
  have hc : (S.position g.c).1.val ≤ g.dx+rightBoundary w false := by
    by_contra hh
    have ht := g.c_to_outer h cert (by omega)
    omega
  have hg := g.or_good hw h cert ho hstart hfinish hc
  rcases hg with ha | hB
  · exact Or.inl (decide_eq_true (g.a_to_outer h cert ha))
  · exact Or.inr (decide_eq_true (g.b_to_outer h cert hB))

private theorem boundarySignals_normal (U : LabelledState Label I.width I.height)
    (bits : Gates.Signals)
    (hpos : ∀ l : OrLabel w, U.position (g.labels l) = g.toThickGateGlyph.embedding.cells
      (orCell w bits.left bits.upper bits.right l)) : g.boundarySignals U = bits := by
  unfold boundarySignals outerA outerB outerC
  simp only [hpos]
  rcases bits with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    simp [ThickGateGlyph.embedding, GridEmbedding.translate, orCell, orPoint, origin] <;> omega

theorem boundarySignals_source : g.boundarySignals M.initialLabelled = g.initialSignals :=
  g.boundarySignals_normal _ _ g.sources

theorem boundarySignals_target (ht : final.position = M.target) :
    g.boundarySignals final = g.targetSignals := by
  apply g.boundarySignals_normal
  intro l
  rw [ht]
  exact g.targets l

end OrGlyph
end PushPuzzle.PushS.FiniteGateReadout
