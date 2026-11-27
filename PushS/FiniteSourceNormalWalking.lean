/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceOuterFloor
public import PushS.FiniteSourceSideStock
public import PushS.FiniteSourceMeshShoulders
public import PushS.FiniteRoutingNormalWalking

/-! Actual normal primitive profiles support both full outer-lane walks with every global box retained. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

theorem normal_profile_step (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (p q : Cell (width w v) (height w v)) (d : Direction) (hadj : Adjacent d p q)
    (hp : Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) p)
    (hq : Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase p) (PrimitiveProfile.state w hw v phase q) :=
  Relation.ReflTransGen.single ⟨d,Move.single_iff.mpr (SingleMoveView.walk
    ⟨hp.1,PrimitiveProfile.floor ha phase,hp.2⟩ hadj hq.1 hq.2)⟩

theorem adjacent_of_coordinates {W H : ℕ} {d : Direction} {p q : Cell W H}
    (h : Travels d (coordinates p) (coordinates q) 1) : Adjacent d p q := by
  cases d <;> dsimp [Adjacent,Travels,coordinates] at * <;> constructor <;> omega

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem normal_outer_free (phase : Fin (codes w v).length → Bool) (north : Bool) (x : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase)
      (s.actualEmbedding.cells (Line.outerCell w s.atoms north x)) :=
  ⟨s.outerCell_floor north x hx hx',s.outerCell_empty phase north x hx hx'⟩

theorem normal_outer_walk (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (north : Bool) (x y : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerCell w s.atoms north x)))
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerCell w s.atoms north y))) :=
  Line.NormalWalking.outer_walk s.actualEmbedding (PrimitiveProfile.floor ha phase) (s.normal_outer_free phase)
    north x y hx hx' hy hy'

/-- Both literal mouths of the mandatory first flip are free in the actual profile. -/
@[expose] def MouthsFree (phase : Fin (codes w v).length → Bool) : Prop :=
  ∀ (j : Fin 2) (p : Cell (Line.width w s.atoms) (Line.height w)),
    p.1.val = FiniteTools.radius w+2*Line.buffer w+w+1+j.val →
    FiniteTools.radius w-w-1 ≤ p.2.val → p.2.val ≤ FiniteTools.radius w+w+1 →
    (if Line.flipMouthNorth s.code.above [.line (Line.buffer w)] j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) →
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) (s.actualEmbedding.cells p)

theorem normal_connected_of_mouth_free (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool)
    (hm : ∀ (j : Fin 2) (p : Cell (Line.width w s.atoms) (Line.height w)),
      p.1.val = FiniteTools.radius w+2*Line.buffer w+w+1+j.val →
      FiniteTools.radius w-w-1 ≤ p.2.val → p.2.val ≤ FiniteTools.radius w+w+1 →
      (if Line.flipMouthNorth s.code.above [.line (Line.buffer w)] j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) →
      Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) (s.actualEmbedding.cells p))
    (north north' : Bool) (x y : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerCell w s.atoms north x)))
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerCell w s.atoms north' y))) :=
  Line.NormalWalking.program_connected (segmentLength s.code.segment) (s.code.above != s.code.desiredSide) s.code.above
    s.actualEmbedding (PrimitiveProfile.floor ha phase) (s.normal_outer_free phase) hm north north' x y hx hx' hy hy'

theorem normal_end_connected_of_mouths (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool) (hm : s.MouthsFree phase) (north north' : Bool) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (s.endLane north)))
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (s.endLane north'))) := by
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have hpos : 1 ≤ Line.span w s.atoms := by have h := s.good.2.1; omega
  exact s.normal_connected_of_mouth_free ha phase hm north north' _ _ (by change _ ≤ FiniteTools.radius w+Line.span w s.atoms; omega)
    (le_refl _) (by change _ ≤ FiniteTools.radius w+Line.span w s.atoms; omega) (le_refl _)

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
