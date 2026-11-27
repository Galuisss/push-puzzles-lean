/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.EdgeWindow
public import PushS.Source.Diagram.Word.DrawingCompiler
public import PushS.Source.Planar.GridDrawing.Translate
import all PushS.Source.Diagram.Word.EdgeWindow
import all PushS.Source.Planar.GridDrawing.WindowPath

/-!
# Actual grid paths of the emitted native edge routes

The original complete canonical path connects the computed finite window. Translate the selected
window path back to its original source row. It retains the same original native endpoints, and
every lattice point is accepted by the exact original canonical trace query.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_points`: original native trace membership.
* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_unitRoute`: exact emitted standard route.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib GridDrawing.WindowRoute

private theorem pattern_endpoints {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) (e : Fin w.compile.edgeCount) :
    let input := PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val
    let pat := input.pattern width (Strip.Sweep.drawingSpan width bound)
    let P := compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
    (gridPoint pat.source).1 = (P.vertex (P.source e)).1 ∧
      (gridPoint pat.source).2 + (input.position false).2 = (P.vertex (P.source e)).2 ∧
      (gridPoint pat.target).1 = (P.vertex (P.target e)).1 ∧
      (gridPoint pat.target).2 + (input.position false).2 = (P.vertex (P.target e)).2 := by
  have hs := PushPuzzle.NCL.Word.DrawingData.EdgeInput.position_eq (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) hg e false
  have ht := PushPuzzle.NCL.Word.DrawingData.EdgeInput.position_eq (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) hg e true
  simp only [Bool.false_eq_true, ite_false, ite_true] at hs ht
  obtain ⟨start, hwin⟩ := (PushPuzzle.NCL.Word.OrthogonalDrawing.compiled_strip_bounds D) hwidth hIndex e
  have hsrc := hwin _ ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).path e).source_mem
  have htgt := hwin _ ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).path e).target_mem
  have hrow := ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).path e).source_row_le
  dsimp only [PushPuzzle.NCL.Word.DrawingData.EdgeInput.pattern, gridPoint]
  rw [hs, ht, tag_val hsrc.1, tag_val htgt.1, tag_val (show
    ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).target e)).2 -
      ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).source e)).2 ≤
        Strip.Sweep.drawingSpan width bound by omega)]
  exact ⟨rfl, by simp only [Fin.val_zero, Nat.zero_add], rfl, by omega⟩

/-- The selected native route as an actual path between its original native endpoint centers. -/
noncomputable def EdgeInput.selectedPath {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) (e : Fin w.compile.edgeCount) :
    GridRouting.Path ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).source e))
      ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).target e)) :=
  let input := PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val
  let pat := input.pattern width (Strip.Sweep.drawingSpan width bound)
  let h := PushPuzzle.NCL.Word.DrawingData.EdgeInput.pattern_connected D hg hwidth hIndex e
  let he := pattern_endpoints D hg hwidth hIndex e
  ((pat.gridPath h).translate 0 (input.position false).2).cast
    (by
      obtain ⟨hsx, hsy, _, _⟩ := he
      exact Prod.ext (by simpa only [Nat.add_zero] using hsx) hsy)
    (by
      obtain ⟨_, _, htx, hty⟩ := he
      exact Prod.ext (by simpa only [Nat.add_zero] using htx) hty)

/-- Every point of the selected actual native path satisfies its original canonical trace query. -/
theorem EdgeInput.selectedPath_points {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) (e : Fin w.compile.edgeCount)
    (p : GridRouting.Point) (hp : (PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath D hg hwidth hIndex e).Contains p) :
    (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val p.1 p.2).trace width = true := by
  unfold PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath at hp
  erw [GridRouting.Path.contains_cast_iff, GridRouting.Path.contains_translate] at hp
  obtain ⟨q, hq, he⟩ := PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath_points _ _ _ hp.2.2
  dsimp only [gridPoint] at he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val q.1.val
    (((PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position false).2 + q.2.val)).trace width = true at hq
  simp only [Nat.sub_zero] at hx
  have hrow : ((PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position false).2 + q.2.val = p.2 := by omega
  rwa [hx, hrow] at hq

/-- The complete selected native path stays in its emitted fixed rectangle. -/
theorem EdgeInput.selectedPath_window {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) (e : Fin w.compile.edgeCount)
    (p : GridRouting.Point) (hp : (PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath D hg hwidth hIndex e).Contains p) :
    p.1 ≤ Strip.Sweep.drawingWidth width ∧
      ((PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position false).2 ≤ p.2 ∧
      p.2 ≤ ((PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position false).2 + Strip.Sweep.drawingSpan width bound := by
  unfold PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath at hp
  erw [GridRouting.Path.contains_cast_iff, GridRouting.Path.contains_translate] at hp
  obtain ⟨q, _, he⟩ := PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath_points _ _ _ hp.2.2
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have hqx := q.1.isLt
  have hqy := q.2.isLt
  dsimp only [gridPoint, Prod.fst, Prod.snd] at hx hy
  omega

/-- Unit subdivision of the selected actual path is exactly the emitted standard native route. -/
theorem EdgeInput.selectedPath_unitRoute {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) (e : Fin w.compile.edgeCount) :
    (PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath D hg hwidth hIndex e).unitRoute =
      (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).route width (Strip.Sweep.drawingSpan width bound) := by
  let input := PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val
  let pat := input.pattern width (Strip.Sweep.drawingSpan width bound)
  let h := PushPuzzle.NCL.Word.DrawingData.EdgeInput.pattern_connected D hg hwidth hIndex e
  have hs : (PushPuzzle.NCL.GridRouting.Path.unitWalk ((pat.gridPath h).translate 0 (input.position false).2)).support =
      input.route width (Strip.Sweep.drawingSpan width bound) := by
    rw [PushPuzzle.NCL.GridRouting.Path.unitWalk_translate, PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath_unitWalk]
    rfl
  have hn : (input.route width (Strip.Sweep.drawingSpan width bound)).Nodup := by
    have hn0 : pat.integerRoute.Nodup := by
      rw [← PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath_unitRoute pat h]
      exact (pat.gridPath h).unitRoute_nodup
    change (pat.integerRoute.map (· + (0, ((input.position false).2 : ℤ)))).Nodup
    exact hn0.map (fun _ _ he => add_right_cancel he)
  have he : ((pat.gridPath h).translate 0 (input.position false).2).unitRoute =
      input.route width (Strip.Sweep.drawingSpan width bound) := by
    exact (GridRouting.Path.unitRoute_eq_unitWalk _ (by rw [hs]; exact hn)).trans hs
  unfold PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath
  erw [unitRoute_cast]
  exact he

end PushPuzzle.NCL.Word.DrawingData
