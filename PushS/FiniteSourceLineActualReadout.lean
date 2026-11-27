/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCertificate
public import PushS.FiniteSourceLineRailFloor
public import PushS.FiniteSourceLineForward
public import PushS.FiniteSourcePathReadout

/-! Actual whole-source line readers use the freely reoriented SCC-support names. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

attribute [local irreducible] codes width height Line.width Line.height InventoryAssembly.board InventoryAssembly.walls

noncomputable def readoutTracks (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance
      (checkedPuzzle w hw v hP hT)) :=
  (axisTracks w hw v hP hT).componentTracks.reorient (s.orientation.inverse.axis (width w v) (height w v))

set_option maxHeartbeats 1000000 in
/-- The real complete selector and the proved global rail floor supply every line-glyph field. -/
noncomputable def actualGlyph (H : s.Selection)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    Line.Readout.LineGlyph ((slotMatching w hw v hP hT).reorient
      (s.orientation.inverse.axis (width w v) (height w v)).geometry) (s.readoutTracks hP hT) w s.atoms s.code.above := by
  have hfit := s.orientation.normalized_fits s.fits.1 s.fits.2
  have hspan : 0 < Line.span w s.atoms := by
    obtain ⟨post,hp⟩ := Line.program_contains_flip w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)
    change 0 < Line.span w (Line.program w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide))
    rw [hp]
    simp only [Line.span_append,Line.span_cons,Line.span_nil,Line.Atom.span]
    omega
  apply Line.Readout.LineGlyph.of_rail_slots w hw s.atoms hspan s.code.above
    (s.orientation.normalizedX (width w v) (height w v) (Line.width w s.atoms) (Line.height w) s.dx s.dy)
    (s.orientation.normalizedY (width w v) (height w v) (Line.width w s.atoms) (Line.height w) s.dx s.dy)
    hfit.1 hfit.2 s.code.initial s.code.target H.labels
  · intro l
    change (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells
      ((inventory w hw v).source (H.labels l)) = s.canonicalEmbedding.cells _
    rw [H.source,s.placed_normal]
  · intro l
    change (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells
      ((inventory w hw v).target (H.labels l)) = s.canonicalEmbedding.cells _
    rw [H.target,s.placed_normal]
  · exact s.wall_normal
  · exact s.rail_normal_floor_actual hP hT

noncomputable def actualReadout (H : s.Selection)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    s.Readout (admissible w hw v hP hT) (connected w hw v hP hT) where
  tracks := s.readoutTracks hP hT
  glyph := s.actualGlyph H hP hT
  embedding _ := rfl
  initial := rfl

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
