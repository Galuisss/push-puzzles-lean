/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.EdgeDrawingCorrectness
public import PushS.Source.Diagram.Word.CompiledTrace
public import PushS.Source.Planar.GridDrawing.Monotone
public import PushS.Source.Strip.Sweep.Window
import all PushS.Source.Diagram.Word.EdgeDrawingData
import all PushS.Source.Planar.GridDrawing.WindowRoute

/-!
# Actual canonical native edges connect their computed finite windows

Normalize the existing actual full path by the actual original false-endpoint row. Its existing
unit route is a source-to-target marked walk in the same finite table emitted by the standard
data compiler.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib

private theorem tag_val {bound n : ℕ} (h : n ≤ bound) : (tag bound n).val = n := by
  have he : tag bound n = (⟨n, by omega⟩ : Fin (bound + 1)) := by
    unfold tag
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp
  exact congrArg Fin.val he

private def normalize (width span base : ℕ) (p : Orthogonal.Point) :
    PushPuzzle.NCL.GridDrawing.WindowRoute.Point (Strip.Sweep.drawingWidth width) span :=
  (tag (Strip.Sweep.drawingWidth width) p.1.toNat, tag span (p.2.toNat - base))

private theorem normalize_point {width span base : ℕ} (p : GridRouting.Point)
    (hx : p.1 ≤ Strip.Sweep.drawingWidth width) (hlo : base ≤ p.2) (hhi : p.2 ≤ base + span) :
    (normalize width span base (GridDrawing.integerPoint p)).1.val = p.1 ∧
      (normalize width span base (GridDrawing.integerPoint p)).2.val = p.2 - base := by
  dsimp only [normalize, GridDrawing.integerPoint, Int.toNat_natCast]
  exact ⟨tag_val hx, tag_val (by omega)⟩

private theorem normalize_step {width span base : ℕ} (a b : GridRouting.Point)
    (ha : a.1 ≤ Strip.Sweep.drawingWidth width ∧ base ≤ a.2 ∧ a.2 ≤ base + span)
    (hb : b.1 ≤ Strip.Sweep.drawingWidth width ∧ base ≤ b.2 ∧ b.2 ≤ base + span)
    (hu : Orthogonal.length (GridDrawing.integerPoint a) (GridDrawing.integerPoint b) = 1)
    (hy : a.2 ≤ b.2) :
    PushPuzzle.NCL.GridDrawing.WindowRoute.step (normalize width span base (GridDrawing.integerPoint a))
      (normalize width span base (GridDrawing.integerPoint b)) = true := by
  have hna := normalize_point a ha.1 ha.2.1 ha.2.2
  have hnb := normalize_point b hb.1 hb.2.1 hb.2.2
  apply decide_eq_true
  constructor
  · change Nat.dist _ _ + Nat.dist _ _ = 1
    rw [hna.1, hnb.1, hna.2, hnb.2]
    have hs : Nat.dist (a.2 - base) (b.2 - base) = Nat.dist a.2 b.2 := by
      simp only [Nat.dist]
      omega
    rw [hs]
    simpa only [Orthogonal.length, GridDrawing.integerPoint,
      GridDrawing.WindowRoute.natAbs_dist, Nat.dist_comm] using hu
  · rw [hna.2, hnb.2]
    omega

private theorem pattern_walk {width span : ℕ} {w : Word} {source target : GridRouting.Point}
    (edge : ℕ) (P : GridRouting.Path source target)
    (hsource : (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w edge).position false = source)
    (htarget : (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w edge).position true = target)
    (hbox : ∀ p, P.Contains p →
      p.1 ≤ Strip.Sweep.drawingWidth width ∧ source.2 ≤ p.2 ∧ p.2 ≤ source.2 + span)
    (hmask : ∀ p, P.Contains p → (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w edge p.1 p.2).trace width = true) :
    let pat := (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w edge).pattern width span
    ∃ r, Cslib.Reachability.IsSrcTgtWalk pat.points PushPuzzle.NCL.GridDrawing.WindowRoute.step
      (fun p => p == pat.source) (fun p => p == pat.target) r := by
  let input : EdgeInput := ⟨w, edge⟩
  let pat := input.pattern width span
  let f := normalize width span source.2
  let r := P.unitRoute.map f
  have hm (u : Orthogonal.Point) (hu : u ∈ P.unitRoute) :
      ∃ p, GridDrawing.integerPoint p = u ∧ P.Contains p ∧
        (f u).1.val = p.1 ∧ (f u).2.val = p.2 - source.2 := by
    obtain ⟨p, hp, ht⟩ := P.unitRoute_trace u hu
    obtain ⟨hx, hlo, hhi⟩ := hbox p ht
    have hn := normalize_point p hx hlo hhi
    exact ⟨p, hp, ht, hp ▸ hn.1, hp ▸ hn.2⟩
  have hfs : f (GridDrawing.integerPoint source) = pat.source := by
    apply Prod.ext
    · change tag _ _ = tag _ _
      simp only [GridDrawing.integerPoint, Int.toNat_natCast, input,
        hsource]
    · apply Fin.ext
      change (tag span _).val = 0
      simp only [GridDrawing.integerPoint, Int.toNat_natCast, Nat.sub_self]
      exact tag_val (Nat.zero_le _)
  have hft : f (GridDrawing.integerPoint target) = pat.target := by
    change normalize width span source.2 (GridDrawing.integerPoint target) =
      ((tag _ (input.position true).1),
        tag span ((input.position true).2 - (input.position false).2))
    simp only [normalize, GridDrawing.integerPoint, Int.toNat_natCast, input, hsource, htarget]
  have hs : r.head? = some pat.source := by
    simp only [r, List.head?_map, P.unitRoute_head, Option.map_some, hfs]
  have ht : r.getLast? = some pat.target := by
    simp only [r, List.getLast?_map, P.unitRoute_last, Option.map_some, hft]
  have hne : r ≠ [] := by intro he; simp [he] at hs
  refine ⟨r, hne, ?_, ?_, ?_, ?_⟩
  · exact beq_iff_eq.mpr (List.head_of_head?_eq_some hs)
  · exact beq_iff_eq.mpr (List.getLast_of_getLast?_eq_some ht)
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    obtain ⟨p, hp, hpath, hx, hy⟩ := hm v hv
    apply List.mem_filter.mpr
    refine ⟨List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩, ?_⟩
    change (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w edge (f v).1.val
      ((input.position false).2 + (f v).2.val)).trace width = true
    rw [hx, hy, hsource]
    have hrow : source.2 + (p.2 - source.2) = p.2 := by have := (hbox p hpath).2.1; omega
    rw [hrow]
    exact hmask p hpath
  · change (P.unitRoute.map f).IsChain _
    rw [List.isChain_map, List.isChain_iff_getElem]
    intro i hi
    have hu := (List.isChain_iff_getElem.mp (PushPuzzle.NCL.GridRouting.Path.unitWalk P).toPath.val.isChain_adj_support) i hi
    change Orthogonal.length P.unitRoute[i] P.unitRoute[i + 1] = 1 at hu
    have hy := (List.isChain_iff_getElem.mp (PushPuzzle.NCL.GridRouting.Path.unitRoute_rows P).isChain) i hi
    obtain ⟨a, ha, hap, hax, hay⟩ := hm _ (List.getElem_mem (by omega : i < P.unitRoute.length))
    obtain ⟨b, hb, hbp, hbx, hby⟩ := hm _ (List.getElem_mem hi)
    have hab : a.2 ≤ b.2 := by
      rw [← ha, ← hb] at hy
      change (a.2 : ℤ) ≤ b.2 at hy
      exact_mod_cast hy
    rw [← ha, ← hb] at hu ⊢
    exact normalize_step a b (hbox a hap) (hbox b hbp) hu hab

/-- Every actual original bounded-span native edge connects its same emitted finite mask. -/
theorem EdgeInput.pattern_connected {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) (e : Fin w.compile.edgeCount) :
    let pat := (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).pattern width (Strip.Sweep.drawingSpan width bound)
    ∃ r, Cslib.Reachability.IsSrcTgtWalk pat.points PushPuzzle.NCL.GridDrawing.WindowRoute.step
      (fun p => p == pat.source) (fun p => p == pat.target) r := by
  let P := compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
  have hs : (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position false = P.vertex (P.source e) := by
    simpa only [Bool.false_eq_true, ite_false] using PushPuzzle.NCL.Word.DrawingData.EdgeInput.position_eq (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) hg e false
  have ht : (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position true = P.vertex (P.target e) := by
    simpa only [ite_true] using PushPuzzle.NCL.Word.DrawingData.EdgeInput.position_eq (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) hg e true
  obtain ⟨start, hwin⟩ := (PushPuzzle.NCL.Word.OrthogonalDrawing.compiled_strip_bounds D) hwidth hIndex e
  have hsrc := hwin _ (P.path e).source_mem
  have htgt := hwin _ (P.path e).target_mem
  apply pattern_walk e.val (P.path e) hs ht
  · intro p hp
    have hb := hwin p hp
    have hy := (P.path e).row_bounds hp
    exact ⟨hb.1, hy.1, by omega⟩
  · intro p hp
    exact PushPuzzle.NCL.Word.DrawingData.TraceInput.compiled_trace D hwidth e p hp

end PushPuzzle.NCL.Word.DrawingData
