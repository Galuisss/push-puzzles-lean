/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingArmGeometry
public import PushS.FiniteRoutingCollinear

/-! Indexed actual path instructions and their inherited physical footprints. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

structure PathSpec where
  segments : List Segment
  initialSide : Bool
  targetSide : Bool
  keepEndpoint : Bool
  initial : Bool
  target : Bool

namespace PathSpec

def line (P : PathSpec) (i : ℕ) : LineCode :=
  lineCodeAt P.segments P.initialSide P.targetSide P.keepEndpoint P.initial P.target i

def turn (P : PathSpec) (i : ℕ) : TurnCode := turnCodeAt P.segments P.initial P.target i

def hasTurn (P : PathSpec) (i : ℕ) : Prop :=
  i+1 < P.segments.length ∧
    segmentDirection (segmentAt P.segments i) ≠ segmentDirection (segmentAt P.segments (i+1))

instance (P : PathSpec) (i : ℕ) : Decidable (P.hasTurn i) := by unfold hasTurn; infer_instance

def block (P : PathSpec) (i : ℕ) : List PrimitiveCode :=
  [.line (P.line i)] ++ if P.hasTurn i then [.turn (P.turn i)] else []

def codes (P : PathSpec) : List PrimitiveCode := (List.range P.segments.length).flatMap P.block

structure Geometry (w : ℕ) (P : PathSpec) : Prop where
  good : ∀ s ∈ P.segments, SegmentGood w s
  joined : P.segments.IsChain (fun s t => s.finish = t.start)
  directions : (P.segments.map segmentDirection).IsChain (fun d e => d = e ∨ Perpendicular d e)
  gap : ∀ (i j : Fin P.segments.length), i.val+1 < j.val →
    (segmentAt P.segments i.val).gapTest (FiniteGeometry.origin w) (segmentAt P.segments j.val) = true

theorem segment_mem (P : PathSpec) (i : ℕ) (hi : i < P.segments.length) : segmentAt P.segments i ∈ P.segments := by
  rw [segmentAt,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem start_contains (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ) (hi : i < P.segments.length) :
    (segmentAt P.segments i).Contains (segmentAt P.segments i).start := by
  rcases (G.good _ (P.segment_mem i hi)).1 with hx | hy
  · exact Or.inl ⟨hx,rfl,min_le_left _ _,le_max_left _ _⟩
  · exact Or.inr ⟨hy,rfl,min_le_left _ _,le_max_left _ _⟩

theorem finish_contains (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ) (hi : i < P.segments.length) :
    (segmentAt P.segments i).Contains (segmentAt P.segments i).finish := by
  rcases (G.good _ (P.segment_mem i hi)).1 with hx | hy
  · exact Or.inl ⟨hx,hx.symm,min_le_right _ _,le_max_right _ _⟩
  · exact Or.inr ⟨hy,hy.symm,min_le_right _ _,le_max_right _ _⟩

theorem join_eq (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ) (hi : i+1 < P.segments.length) :
    (segmentAt P.segments i).finish = (segmentAt P.segments (i+1)).start := by
  have h := G.joined.getElem i hi
  simpa only [segmentAt,List.getD_eq_getElem _ _ (by omega : i < P.segments.length),List.getD_eq_getElem _ _ hi] using h

theorem line_good (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ) (hi : i < P.segments.length) :
    LineGood w (P.line i).segment := trimmedSegment_lineGood w P.segments G.good i hi

theorem turn_perpendicular (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ) (hi : P.hasTurn i) :
    Perpendicular (P.turn i).incoming (P.turn i).outgoing :=
  (directions_chain_adjacent P.segments G.directions i hi.1).resolve_left hi.2

theorem junction_contract (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ) (hi : P.hasTurn i) :
    JunctionContract w (P.line i) (P.turn i) (P.line (i+1)) :=
  path_junction_contract w P.segments G.good G.joined _ _ _ _ _ i hi.1 (P.turn_perpendicular w G i hi)

theorem collinear_contract (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ)
    (hi : i+1 < P.segments.length) (hn : ¬P.hasTurn i) : CollinearContract w (P.line i) (P.line (i+1)) := by
  apply path_collinear_contract w P.segments G.good G.joined _ _ _ _ _ i hi
  exact Classical.not_not.mp (fun he => hn ⟨hi,he⟩)

theorem line_actor_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) (goal : Bool) (l : (PrimitiveCode.line (P.line i)).Labels w) :
    ∃ u, (segmentAt P.segments i).Contains u ∧
      Nearby 1 ((PrimitiveCode.line (P.line i)).actor w hw goal l) (padding w+u.1,padding w+u.2) := by
  obtain ⟨u,hu,ha⟩ := line_actor_footprint w hw (P.line i) (P.line_good w G i hi) goal l
  refine ⟨u,?_,ha⟩
  have hs := G.good _ (P.segment_mem i hi)
  exact trimmed_trace_subset _ hs.1 _ _
    (by have hf := startTrim_bound P.segments i; have hb := finishTrim_bound P.segments i
        have hl := hs.2.1; omega) hu

theorem line_wall_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length)
    (p : Cell ((PrimitiveCode.line (P.line i)).instanceOf w hw).width ((PrimitiveCode.line (P.line i)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line i)).instanceOf w hw).board.walls) :
    ∃ u, (segmentAt P.segments i).Contains u ∧
      Nearby (w+1) ((PrimitiveCode.line (P.line i)).world w hw p) (padding w+u.1,padding w+u.2) := by
  obtain ⟨u,hu,ha⟩ := line_wall_footprint w hw (P.line i) (P.line_good w G i hi) p hp
  refine ⟨u,?_,ha⟩
  have hs := G.good _ (P.segment_mem i hi)
  exact trimmed_trace_subset _ hs.1 _ _
    (by have hf := startTrim_bound P.segments i; have hb := finishTrim_bound P.segments i
        have hl := hs.2.1; omega) hu

theorem turn_actor_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (goal : Bool) (l : Fin 2) :
    Nearby 2 ((PrimitiveCode.turn (P.turn i)).actor w hw goal l)
      (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) :=
  turn_actor_footprint w hw (P.turn i) (P.turn_perpendicular w G i hi) goal l

theorem turn_wall_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (i : ℕ)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    Nearby (FiniteTools.radius w) ((PrimitiveCode.turn (P.turn i)).world w hw p)
      (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) :=
  turn_window_footprint w hw (P.turn i) p

theorem marks_ne (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i j : ℕ)
    (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i+1 < j)
    (m n : ℕ) (hm : m+n ≤ FiniteGeometry.origin w) {u v a b : ℕ × ℕ}
    (hu : (segmentAt P.segments i).Contains u) (hv : (segmentAt P.segments j).Contains v)
    (ha : Nearby m a (padding w+u.1,padding w+u.2))
    (hb : Nearby n b (padding w+v.1,padding w+v.2)) : a ≠ b := by
  apply footprint_ne (w := w) _ ha hb
  exact fun h => Segment.not_nearby_of_gap (G.gap ⟨i,hi⟩ ⟨j,hj⟩ hij) hu hv (nearby_of_le hm h)

end PathSpec

def armSpec (w : ℕ) (g : GateTileState) (role : Fin 3) : PathSpec :=
  ⟨armRoute w g role,coreSide g.core.isAND role,g.incoming.get role,!(g.incoming.get role),
    portInflow g.core.initial.left g.core.initial.upper g.core.initial.right role,
    portInflow g.core.target.left g.core.target.upper g.core.target.right role⟩

theorem armSpec_geometry (w : ℕ) (g : GateTileState) (role : Fin 3) : (armSpec w g role).Geometry w :=
  ⟨armRoute_good w g role,armRoute_joined w g role,armRoute_directions_chain w g role,
    armRoute_nonadjacent_gap w g role⟩

end PushPuzzle.PushS.FiniteRouting
