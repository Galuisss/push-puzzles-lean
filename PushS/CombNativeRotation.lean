/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNativeFanDarts
import all PushS.CombNativeFanDarts
import all PushS.PreparedRayOrder
import all PushS.CombGenus
import all PushS.CombToothDarts

/-! The genuine native rotation reads the actual compiler's three weighted fan slots in order. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private def nativeRanks (keys : Fin 3 → Fin 4) : Fin 4 → Fin 8 := Fin.cases 2 (fun slot => keyRank (keys slot))

private theorem nativeRanks_injective : ∀ keys : Fin 3 → Fin 4, StrictMono keys → Function.Injective (nativeRanks keys) := by decide

private theorem nativeRanks_first : ∀ keys : Fin 3 → Fin 4, StrictMono keys → ∀ origin other : Fin 4, other ≠ origin →
    ((nativeRanks keys (origin + 1)).val + 7 - (nativeRanks keys origin).val) % 8 ≤
      ((nativeRanks keys other).val + 7 - (nativeRanks keys origin).val) % 8 := by decide

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d)

/-- The downward tooth followed by exactly the original compiler's sorted weighted fan slots. -/
@[expose] def nativeDartCycle (vertex : Fin d.1.length) : Fin 4 → Graph.Dart (augmentedGraph width hd) :=
  Fin.cases (toothTipDart width hd vertex) (nativeFanDart width hg drawing hd vertex)

section Geometry

variable (height : ℕ) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin drawing.incidenceGraph.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition drawing.incidenceGraph d drawing.incidenceGraph.edges[edge].1))

include hfit in
private theorem native_cycle_vertex (vertex : Fin d.1.length) (index : Fin 4) :
    (nativeDartCycle width hg drawing hd vertex index).vertex = stationNumber width d (.tip vertex) := by
  refine Fin.cases (toothTipDart_vertex width hd vertex) (fun slot => ?_) index
  exact nativeFanDart_vertex width hg drawing hd height hfit vertex slot

private theorem native_cycle_direction (vertex : Fin d.1.length) (index : Fin 4) :
    (augmentedDrawing width height hd hfit hhead).direction (nativeDartCycle width hg drawing hd vertex index) =
      octantAngle (nativeRanks (nativeFanKey width hg drawing hd vertex) index).val := by
  refine Fin.cases (toothTipDart_direction width height hd hfit hhead vertex) (fun slot => ?_) index
  rw [show nativeDartCycle width hg drawing hd vertex slot.succ = nativeFanDart width hg drawing hd vertex slot from rfl,
    nativeFanDart_direction]
  rfl

include hfit hhead in
/-- The native source fan's actual geometric cycle follows precisely the compiler's literal sorted slot order. -/
theorem augmentedRotation_native (vertex : Fin d.1.length) (origin : Fin 4) :
    (augmentedRotation width height hd hfit hhead).rotate (nativeDartCycle width hg drawing hd vertex origin) =
      nativeDartCycle width hg drawing hd vertex (origin + 1) := by
  have hmono := nativeFanKey_strictMono width hg drawing hd height hfit hhead vertex
  have hinj : Function.Injective (nativeDartCycle width hg drawing hd vertex) := by
    intro left right he
    apply nativeRanks_injective _ hmono
    apply octantAngle_injective
    change octantAngle (nativeRanks (nativeFanKey width hg drawing hd vertex) left).val =
      octantAngle (nativeRanks (nativeFanKey width hg drawing hd vertex) right).val
    rw [← native_cycle_direction width hg drawing hd height hfit hhead vertex left,
      ← native_cycle_direction width hg drawing hd height hfit hhead vertex right, he]
  apply rotate_eq_of_octant_catalog (augmentedDrawing_realizes_rotation width height hd hfit hhead)
    (nativeDartCycle width hg drawing hd vertex) hinj origin (origin + 1) (by omega)
    (fun index => (native_cycle_vertex width hg drawing hd height hfit vertex index).trans
      (native_cycle_vertex width hg drawing hd height hfit vertex origin).symm) _
    (nativeRanks (nativeFanKey width hg drawing hd vertex)) (native_cycle_direction width hg drawing hd height hfit hhead vertex)
    (nativeRanks_first _ hmono origin)
  intro dart hv
  rw [native_cycle_vertex width hg drawing hd height hfit] at hv
  rcases nativeFanDart_cover width hg drawing hd height hfit vertex dart hv with ⟨slot, he⟩ | he
  · exact ⟨slot.succ, he⟩
  · exact ⟨0, he.symm⟩

end Geometry
end Native
end PushPuzzle.PushS.Comb
