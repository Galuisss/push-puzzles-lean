/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalGateReadout
public import PushFS.Reduction.PhysicalCompiler

/-! Actual central thresholds, complete target identities and the finite source's reverse projection. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalBitmap Gadgets
open Gates.Soundness Wires.Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 10000
attribute [local irreducible] Raster.width Raster.height

private theorem inward_eq {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {A : AxisTracks I} {kind : Bool} (g : GateGlyph M A kind) (S : LabelledState L I.width I.height) (r : Fin 3) :
    g.coreInward S r=gateClaim (g.decode S) r := by
  fin_cases r <;> simp [GateGlyph.coreInward,gateClaim,Gates.Signals.get]

private theorem coreGlyph_inward (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT)) (g : VertexData) (hg : g∈vertexRecords v.1)
    (tags : CoreTags v hP hT A g hg)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) (r : Fin 3) :
    (coreGlyph v hP hT A g hg tags).coreInward S r=gateClaim (observedSignals v g hg S) r := by
  exact (inward_eq (coreGlyph v hP hT A g hg tags) S r).trans
    (congrArg (fun b=>gateClaim b r) (coreGlyph_decode v hP hT A g hg tags S))

/-- A real inward source threshold reaches the actual outermost core box on an arbitrary successful path. -/
theorem observed_to_core_boundary (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT)) (g : VertexData) (hg : g∈vertexRecords v.1)
    (tags : CoreTags v hP hT A g hg) (cert : Certificate (puzzle v hP hT))
    (ordered : (rawSlotMatching v hP hT).Ordered)
    {S final : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S final) (r : Fin 3)
    (hin : gateClaim (observedSignals v g hg S) r=true) :
    (coreGlyph v hP hT A g hg tags).boundarySignal S r=true := by
  exact (coreGlyph v hP hT A g hg tags).core_to_boundary hs cert ordered r
    ((coreGlyph_inward v hP hT A g hg tags S r).trans hin)

/-- Successful actual physical motion projects to the original finite NCL graph once each full line's
two inward endpoints are proved exclusive. -/
theorem ncl_of_solvable (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT))
    (tags : ∀g (hg : g∈vertexRecords v.1),CoreTags v hP hT A g hg)
    (cert : Certificate (puzzle v hP hT)) (ordered : (rawSlotMatching v hP hT).Ordered)
    (ha : (Word.compile v.1).checkLegal v.2.1=true) (hb : (Word.compile v.1).checkLegal v.2.2=true)
    (exclusive : ∀S final,Successful (rawSlotMatching v hP hT) S final→
      PortClaims.Exclusive ((sourceReadout v hw hP hT hw.2.2).read S))
    {cap : Option ℕ} (hsol : (puzzle v hP hT).Solvable cap) :
    (Word.compile v.1).graph.Reachable (fun e=>v.2.1.getD e.val false) (fun e=>v.2.2.getD e.val false) := by
  obtain ⟨t,hr,hsol⟩:=hsol
  obtain ⟨T,hTstate,hpath,hTpos⟩:=ordered.lift_success cert hr hsol
  have hgoals : T.state.boxes=(puzzle v hP hT).board.goals := hTstate ▸hsol
  exact (sourceReadout v hw hP hT hw.2.2).successful_path hpath
    (fun S hbefore hafter=>⟨exclusive S T ⟨hbefore,hafter,hgoals⟩,
      sourceReadout_legal v hw hP hT hw.2.2 A tags cert ordered ha hb ⟨hbefore,hafter,hgoals⟩⟩)
    (sourceReadout_initial v hw hP hT hw.2.2) (sourceReadout_target v hw hP hT hw.2.2 T hTpos)

end PushPuzzle.PushFS.Reduction.PhysicalInventory

namespace PushPuzzle.PushFS.Reduction.PhysicalCompiler

open Cslib.Complexity.NCL PushPuzzle.NCL

/-- The checked total compiler's physical reverse proof suffices on precisely its admitted source data. -/
theorem mem_of_checkedCompile_solvable
    (sound : ∀(x : PlaneWordAndOrNCL.Instance) (hx : SourceChecks x),
      (PhysicalInventory.puzzle (source x) hx.plane hx.typed).Solvable none→
        (Word.compile x.word).graph.Reachable ((Word.compile x.word).config x.initial)
          ((Word.compile x.word).config x.target))
    {x : PlaneWordAndOrNCL.Instance} {cap : Option ℕ} (h : (checkedCompile x).Solvable cap) :
    x∈PlaneWordAndOrNCL := by
  by_cases hx : SourceChecks x
  · rw [checkedCompile_eq x hx] at h
    have hu:=Instance.solvable_unlimited h
    exact ⟨hx.plane,hx.typed,hx.valid,hx.initial_width,hx.target_width,
      (AndOrGraph.checkLegal_eq_true_iff _ hx.valid.1 _).mp hx.initial_legal,sound x hx hu⟩
  · rw [checkedCompile_reject x hx] at h
    exact False.elim (reject_not_solvable cap h)

end PushPuzzle.PushFS.Reduction.PhysicalCompiler
