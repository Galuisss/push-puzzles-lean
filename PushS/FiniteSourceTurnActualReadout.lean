/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCertificate
public import PushS.FiniteSourceChartLevels
public import PushS.FiniteSourcePathReadout

/-! The actual turn reader derives all normalized names from the freely reoriented SCC-support environment. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.TurnSite

open PushFS PushFS.Reduction FiniteRouting

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : TurnSite w hw v)

attribute [local irreducible] codes width height FiniteTools.side InventoryAssembly.board InventoryAssembly.walls

noncomputable def readoutTracks (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance
      (checkedPuzzle w hw v hP hT)) :=
  (axisTracks w hw v hP hT).componentTracks.reorient (s.orientation.inverse.axis (width w v) (height w v))

private theorem normal_active (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (i : Fin 2) :
    (s.readoutTracks hP hT).name (s.canonicalEmbedding.cells (Turn.cell w s.code.initial i)) ≠ .outside := by
  rw [←s.source_normal]
  change (s.orientation.inverse.axis (width w v) (height w v)).name
    ((axisClassifier w hw v hP hT).name
      ((s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm
        ((s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).source (s.label i))))) ≠ .outside
  rw [Equiv.symm_apply_apply]
  exact fun h => axis_actor_active w hw v hP hT false (s.label i)
    (((s.orientation.inverse.axis (width w v) (height w v)).outside _).mp h)

private theorem normalized_connected (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (a b : Bool) (i : Fin 2) :
    SameComponent ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance
      (checkedPuzzle w hw v hP hT)).board
      (s.canonicalEmbedding.cells (Turn.cell w a i)) (s.canonicalEmbedding.cells (Turn.cell w b i)) := by
  have h := ((s.orientation.inverse.axis (width w v) (height w v)).geometry.sameComponent_iff
    (inventory w hw v).board _ _).mpr (s.normal_connected a b i)
  rw [s.placed_normal,s.placed_normal] at h
  exact h

theorem horizontal_name (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (s.readoutTracks hP hT).name (s.canonicalEmbedding.cells (Turn.cell w s.code.initial 0)) =
      .horizontal (s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w) := by
  have h := (s.readoutTracks hP hT).horizontal_of_active_component
    (s.normalized_connected hP hT s.code.initial (!s.code.initial) 0) (q := s.canonicalEmbedding.cells (Turn.cell w (!s.code.initial) 0))
    (by
      change s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+
          (FiniteTools.radius w-2+s.code.initial.toNat) ≠
        s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+
          (FiniteTools.radius w-2+(!s.code.initial).toNat)
      cases s.code.initial <;> simp)
    (s.normal_active hP hT 0)
  exact h

theorem vertical_name (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (s.readoutTracks hP hT).name (s.canonicalEmbedding.cells (Turn.cell w s.code.initial 1)) =
      .vertical (s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w) := by
  have h := (s.readoutTracks hP hT).vertical_of_active_component
    (s.normalized_connected hP hT s.code.initial (!s.code.initial) 1) (q := s.canonicalEmbedding.cells (Turn.cell w (!s.code.initial) 1))
    (by
      change s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+
          (FiniteTools.radius w+1+s.code.initial.toNat) ≠
        s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+
          (FiniteTools.radius w+1+(!s.code.initial).toNat)
      cases s.code.initial <;> simp)
    (s.normal_active hP hT 1)
  exact h

private theorem corner_name_original (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (axisClassifier w hw v hP hT).name (s.actualEmbedding.cells (Turn.center w)) =
      .sink (s.actualEmbedding.cells (Turn.center w)).1.val (s.actualEmbedding.cells (Turn.center w)).2.val := by
  have he : (Turn.stencilChart w s.code.incoming s.code.outgoing).embedding.cells ((3,3) : Cell 7 7) =
      (Turn.orientation w s.code.incoming s.code.outgoing).cells (Turn.center w) := by
    rw [Turn.orientation_center]
    apply Prod.ext <;> apply Fin.ext
    all_goals change FiniteTools.radius w-3+3 = FiniteTools.radius w; unfold FiniteTools.radius; omega
  have hf : s.actualEmbedding.cells (Turn.center w) ∉ (inventory w hw v).walls := by
    apply center_floor w hw v _ s.code s.code_mem
    rw [s.actual_cell_coordinates]
    rfl
  have hp : (primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells
      (((PrimitiveCode.turn s.code).chart w hw ()).embedding.cells ((3,3) : Cell 7 7)) ∉ (inventory w hw v).walls := by
    change (primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells
      ((Turn.stencilChart w s.code.incoming s.code.outgoing).embedding.cells ((3,3) : Cell 7 7)) ∉ _
    rw [he]
    exact hf
  have ht : (((PrimitiveCode.turn s.code).chart w hw ()).classifier.name ((3,3) : Cell 7 7)).level = 3 := by
    change ((Turn.stencilChart w s.code.incoming s.code.outgoing).classifier.name ((3,3) : Cell 7 7)).level = 3
    have h := congrArg AxisTrack.level (Turn.stencilChart_corner w s.code.incoming s.code.outgoing)
    change (AxisTrack.shift (FiniteTools.radius w-3) (FiniteTools.radius w-3)
      ((Turn.stencilChart w s.code.incoming s.code.outgoing).classifier.name ((3,3) : Cell 7 7))).level = 3 at h
    rw [AxisTrack.level_shift] at h
    exact h
  have h := primitive_chart_sink w hw v hP hT s.index (.turn s.code) s.code_eq () ((3,3) : Cell 7 7) hp ht
  change (axisClassifier w hw v hP hT).name
      ((primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells
        ((Turn.stencilChart w s.code.incoming s.code.outgoing).embedding.cells ((3,3) : Cell 7 7))) =
      .sink ((primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells
        ((Turn.stencilChart w s.code.incoming s.code.outgoing).embedding.cells ((3,3) : Cell 7 7))).1.val
        ((primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells
        ((Turn.stencilChart w s.code.incoming s.code.outgoing).embedding.cells ((3,3) : Cell 7 7))).2.val at h
  rw [he] at h
  exact h

theorem corner_name (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (s.readoutTracks hP hT).name (s.canonicalEmbedding.cells (Turn.center w)) =
      .sink (s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w)
        (s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w) := by
  have h := (axisTracks w hw v hP hT).componentTracks.reorient_sink
    (s.orientation.inverse.axis (width w v) (height w v)) (s.actualEmbedding.cells (Turn.center w)) (s.corner_name_original hP hT)
  let F := fun p : Cell (s.orientation.inverse.width (width w v) (height w v))
      (s.orientation.inverse.height (width w v) (height w v)) =>
    (s.readoutTracks hP hT).name p = AxisTrack.sink p.1.val p.2.val
  have hf : F ((s.orientation.inverse.axis (width w v) (height w v)).geometry.cells
      (s.actualEmbedding.cells (Turn.center w))) := h
  have hf' : F (s.canonicalEmbedding.cells (Turn.center w)) := (s.placed_normal (Turn.center w)) ▸ hf
  exact hf'

noncomputable def actualGlyph (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    Turn.Readout.TurnGlyph ((slotMatching w hw v hP hT).reorient
      (s.orientation.inverse.axis (width w v) (height w v)).geometry) (s.readoutTracks hP hT) w :=
  s.glyph (admissible w hw v hP hT) (connected w hw v hP hT) (s.readoutTracks hP hT)
    (s.horizontal_name hP hT) (s.vertical_name hP hT) (s.corner_name hP hT)

noncomputable def actualReadout (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    s.Readout (admissible w hw v hP hT) (connected w hw v hP hT) where
  tracks := s.readoutTracks hP hT
  glyph := s.actualGlyph hP hT
  embedding _ := rfl
  initial := rfl

end PushPuzzle.PushS.FiniteSourceInventory.TurnSite
