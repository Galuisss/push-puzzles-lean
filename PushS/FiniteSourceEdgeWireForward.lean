/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceWireInput
public import PushS.FiniteSourceEdgeOrder

/-! Every actual ordinary tile on the reversed edge has the concrete prepared interfaces of its full path execution. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical
open scoped Classical

attribute [local irreducible] codes width height inventory Raster.width Raster.height

private theorem wire_predecessor_step {word : Word} {e : ℕ} {p q : GridRouting.Point} {k : Catalog.Kind}
    (hk : Raster.wireAt (word,(e,p)) = some k)
    (hn : neighbor (Catalog.sourceDirection k).opposite p = some q) :
    UnitStep (Route.edgeSegments (refinedProgram word,e)) q p := by
  obtain ⟨q',hq,ha⟩ := (Raster.incoming_named _ _ _ _).mp (Raster.wireAt_source_arc hk)
  have he : q' = q := Option.some.inj (hq.symm.trans hn)
  rw [he] at ha
  exact ⟨Catalog.sourceDirection k,by simpa only [Direction.opposite_opposite] using ha,
    by simpa only [Direction.opposite_opposite] using neighbor_reverse hn⟩

/-- The emitted ordinary record on this genuine edge has its exact old and flipped physical phases. -/
theorem wire_reversed_phases (word : Word) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (p : GridRouting.Point) (d : ℕ) (a : Catalog.Bitmap.Args)
    (hc : CellPlan.cell (oneEdgeSource word c e,p) = some (.inr (d,a)))
    (hp : HasPoint (Route.edgeSegments (refinedProgram word,e.val)) p) :
    d = e.val ∧ Raster.wireAt (word,(e.val,p)) = some a.1 ∧ a.2.1 = !(c e) ∧ a.2.2 = c e := by
  obtain ⟨hv,ho,hw,ha,hb⟩ := CellPlan.wire_sound hc
  have hd : d = e.val := Option.some.inj (ho.symm.trans
    (Raster.owner_unique hP hT ((Raster.vertexAt_none_iff _ _).mp hv) ((Route.edgeSegments_trace _ _ _).mp hp)))
  refine ⟨hd,?_,?_,?_⟩
  · simpa only [hd,oneEdgeSource] using hw
  · change a.2.1 = !(configBits c).getD d false at ha
    rw [hd,configBits_getD c e.val e.isLt] at ha
    exact ha
  · change a.2.2 = !(configBits (reverse c e)).getD d false at hb
    rw [hd,configBits_getD (reverse c e) e.val e.isLt] at hb
    simpa only [reverse_self,Bool.not_not] using hb

namespace WireInput

/-- The genuine source-path frontier prepares the automatically selected physical predecessor identity. -/
private theorem frontier_ready {w : ℕ} {hw : 2 ≤ w} {word : Word}
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    {c : Fin word.compile.edgeCount → Bool} {e : Fin word.compile.edgeCount}
    {a : Catalog.Bitmap.Args} (d : ℕ)
    (t : PathSite w hw (oneEdgeSource word c e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word c e,t.location) = some (.inr (d,a)))
    (I : WireInput t) (phase : GridRouting.Point → Bool)
    (H : TileFrontier word c e phase t.location) :
    t.BoundaryReady I.endpoints (tilePhases phase) := by
  obtain ⟨_,hk,ha,_⟩ := wire_reversed_phases word hP hT c e t.location d a hc H.point
  apply I.ready phase
  have hp := H.previous I.previous (wire_predecessor_step hk I.neighbor)
  unfold edgeWirePhase at hp
  have he : phase I.previous = !(c e) := by
    cases hbit : c e <;> cases hprev : phase I.previous <;> simp_all
  exact he.trans ha.symm

end WireInput

/-- Execute the entire actual ordinary tile of a source-edge traversal, with every dynamic endpoint condition discharged. -/
theorem edge_wire_tile_forward (w : ℕ) (hw : 2 ≤ w) (word : Word)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (ha : (inventory w hw (oneEdgeSource word c e)).Admissible)
    {a : Catalog.Bitmap.Args} (d : ℕ)
    (t : PathSite w hw (oneEdgeSource word c e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word c e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (H : TileFrontier word c e phase t.location)
    (B : Board (width w (oneEdgeSource word c e)) (height w (oneEdgeSource word c e)))
    (F : ∀ cut,cut < PathSite.waveLength (P := wireSpec w a) → ∀ b : PathEvent (wireSpec w a),
      b.rank = PathSite.waveRank (P := wireSpec w a) cut →
      t.EventFrame (wireSpec_geometry w a) (actualWireInput hP hT d t hc).endpoints B (t.wave (tilePhases phase) cut) b)
    (W : t.WaveAccess (wireSpec_geometry w a) (tilePhases phase) B (inventory w hw (oneEdgeSource word c e)).player) :
    Reachable B (some 1) (profileState w hw (oneEdgeSource word c e) phase)
      (profileState w hw (oneEdgeSource word c e) (Function.update phase t.location true)) := by
  obtain ⟨_,_,hinit,htarget⟩ := wire_reversed_phases word hP hT c e t.location d a hc H.point
  apply t.wire_tile_forward ha d hc phase H.fresh (actualWireInput hP hT d t hc).endpoints
    ((actualWireInput hP hT d t hc).frontier_ready hP hT d t hc phase H) ?_ B F W
  rw [hinit,htarget,Bool.not_not]

end PushPuzzle.PushS.FiniteSourceInventory
