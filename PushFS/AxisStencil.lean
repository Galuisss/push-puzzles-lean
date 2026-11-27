/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Reduction.FullGateStatics.Cover

/-! Static charts need only their protecting walls; additional ambient walls preserve classification. -/

@[expose] public section
namespace PushPuzzle.PushFS

variable {w h W H : ℕ}

/-- Every displacement on the board with more walls is a displacement on the original board. -/
theorem Displacement.of_walls_subset {B B' : Board w h} (hw : B.walls ⊆ B'.walls)
    {p q : Cell w h} (hd : Displacement B' p q) : Displacement B p q := by
  obtain ⟨hp, d, rear, hr, hq, hrw, hqw⟩ := hd
  exact ⟨fun h => hp (hw h), d, rear, hr, hq, fun h => hrw (hw h), fun h => hqw (hw h)⟩

/-- Adding walls preserves a supported static displacement classifier and all its coordinate names. -/
def AxisClassifier.addWalls {B B' : Board w h} (C : AxisClassifier B)
    (hw : B.walls ⊆ B'.walls) : AxisClassifier B' where
  name := C.name
  supported := C.supported
  displacement p q hd := C.displacement p q (hd.of_walls_subset hw)

/-- Wall cells carry no physical rail; their names can be discarded. -/
def AxisClassifier.floorOnly {B : Board w h} (C : AxisClassifier B) : AxisClassifier B where
  name p := if p ∈ B.walls then .outside else C.name p
  supported p := by
    split
    · trivial
    · exact C.supported p
  displacement p q hd := by
    have hc := C.displacement p q hd
    have hp := hd.1
    obtain ⟨_, _, _, _, _, _, hq⟩ := hd
    simpa only [hp, hq, ite_false] using hc

/-- The exact ambient walls seen through a local rectangle. -/
def GridEmbedding.pullback (e : GridEmbedding w h W H) (B : Board W H) : Board w h :=
  ⟨Finset.univ.filter fun p => e.cells p ∈ B.walls, ∅⟩

theorem GridEmbedding.pullback_walls (e : GridEmbedding w h W H) (B : Board W H) :
    e.WallsAgree (e.pullback B) B := by
  intro p
  simp only [pullback, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A translated cell rectangle has exactly its stated coordinate range. -/
theorem GridEmbedding.translate_image_iff (dx dy : ℕ) (hx : dx+w ≤ W) (hy : dy+h ≤ H)
    (p : Cell W H) :
    (∃ q, (GridEmbedding.translate dx dy hx hy).cells q = p) ↔
      dx ≤ p.1.val ∧ p.1.val < dx+w ∧ dy ≤ p.2.val ∧ p.2.val < dy+h := by
  constructor
  · rintro ⟨q, rfl⟩
    change dx ≤ dx+q.1.val ∧ dx+q.1.val < dx+w ∧
      dy ≤ dy+q.2.val ∧ dy+q.2.val < dy+h
    omega
  · rintro ⟨hxl, hxh, hyl, hyh⟩
    let q : Cell w h := (⟨p.1.val-dx, by omega⟩, ⟨p.2.val-dy, by omega⟩)
    refine ⟨q, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change dx+(p.1.val-dx) = p.1.val
      omega
    · change dy+(p.2.val-dy) = p.2.val
      omega

/-- Keep a minimal protecting stencil's classifier on the actual ambient wall restriction. -/
def TranslatedAxisChart.restrictTo (C : TranslatedAxisChart W H) (B : Board W H)
    (hw : ∀ p, p ∈ C.board.walls → C.embedding.cells p ∈ B.walls) :
    TranslatedAxisChart W H where
  width := C.width
  height := C.height
  board := C.embedding.pullback B
  dx := C.dx
  dy := C.dy
  fits_x := C.fits_x
  fits_y := C.fits_y
  classifier := C.classifier.addWalls (by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw p hp⟩)

theorem TranslatedAxisChart.restrictTo_walls (C : TranslatedAxisChart W H) (B : Board W H)
    (hw : ∀ p, p ∈ C.board.walls → C.embedding.cells p ∈ B.walls) :
    (C.restrictTo B hw).embedding.WallsAgree (C.restrictTo B hw).board B :=
  C.embedding.pullback_walls B

/-- Restrict to actual ambient walls and retain precisely the floor part of the original rail. -/
def TranslatedAxisChart.restrictToFloor (C : TranslatedAxisChart W H) (B : Board W H)
    (hw : ∀ p, p ∈ C.board.walls → C.embedding.cells p ∈ B.walls) : TranslatedAxisChart W H :=
  let R := C.restrictTo B hw
  { R with classifier := R.classifier.floorOnly }

namespace Reduction.GateTileRouting.FullGateStatics.Mosaic

/-- Minimal local guard walls suffice to construct the existing maximal-level chart mosaic. -/
def of_stencils {B : Board W H} {Chart : Type}
    (chart : Chart → TranslatedAxisChart W H)
    (walls : ∀ c p, p ∈ (chart c).board.walls → (chart c).embedding.cells p ∈ B.walls)
    (safe : ∀ c p, (chart c).classifier.name p ≠ .outside → ∃ d q,
      Gadgets.Wires.Catalog.BoundaryAligned (W := W) (H := H) (chart d).dx (chart d).dy q ∧
      (chart d).embedding.cells q = (chart c).embedding.cells p ∧
      ((chart c).classifier.name p).level ≤ ((chart d).classifier.name q).level) :
    Mosaic B Chart where
  chart c := (chart c).restrictTo B (walls c)
  walls c := (chart c).restrictTo_walls B (walls c)
  safe := safe

/-- Only represented floor cells need a neighboring safe owner in the static mosaic. -/
def of_floor_stencils {B : Board W H} {Chart : Type}
    (chart : Chart → TranslatedAxisChart W H)
    (walls : ∀ c p, p ∈ (chart c).board.walls → (chart c).embedding.cells p ∈ B.walls)
    (safe : ∀ c p, (chart c).classifier.name p ≠ .outside →
      (chart c).embedding.cells p ∉ B.walls → ∃ d q,
      Gadgets.Wires.Catalog.BoundaryAligned (W := W) (H := H) (chart d).dx (chart d).dy q ∧
      (chart d).embedding.cells q = (chart c).embedding.cells p ∧
      ((chart c).classifier.name p).level ≤ ((chart d).classifier.name q).level) :
    Mosaic B Chart where
  chart c := (chart c).restrictToFloor B (walls c)
  walls c := (chart c).restrictTo_walls B (walls c)
  safe c p hp := by
    classical
    have hf : (chart c).embedding.cells p ∉ B.walls := by
      intro hw
      apply hp
      simp only [TranslatedAxisChart.restrictToFloor, TranslatedAxisChart.restrictTo,
        AxisClassifier.floorOnly, AxisClassifier.addWalls, GridEmbedding.pullback,
        Finset.mem_filter, Finset.mem_univ, hw, and_self, ite_true]
    have ha : (chart c).classifier.name p ≠ .outside := by
      simpa only [TranslatedAxisChart.restrictToFloor, TranslatedAxisChart.restrictTo,
        AxisClassifier.floorOnly, AxisClassifier.addWalls, GridEmbedding.pullback,
        Finset.mem_filter, Finset.mem_univ, hf, and_false, ite_false] using hp
    obtain ⟨d, q, hs, he, hl⟩ := safe c p ha hf
    have hq : (chart d).embedding.cells q ∉ B.walls := he ▸ hf
    refine ⟨d, q, hs, he, ?_⟩
    simpa only [TranslatedAxisChart.restrictToFloor, TranslatedAxisChart.restrictTo,
      AxisClassifier.floorOnly, AxisClassifier.addWalls, GridEmbedding.pullback,
      Finset.mem_filter, Finset.mem_univ, hf, hq, and_false, ite_false] using hl

end Reduction.GateTileRouting.FullGateStatics.Mosaic
end PushPuzzle.PushFS
