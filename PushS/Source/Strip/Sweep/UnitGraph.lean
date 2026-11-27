/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Source
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Subdivision
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Reorient

/-!
# The actual unit-subdivision graph of a strip routing

The old edges are subdivided at every interior point of their actual unit traversals. Segment
names are the actual `PushPuzzle.NCL.Strip.Sweep.Arc` labels and reference directions are rebased to increasing scan
level. The construction carries the standard subdivision simulation.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.jointCount`: actual number of interior unit-path sites of an old edge.
* `PushPuzzle.NCL.Strip.Sweep.segmentEquiv`: the standard subdivision's segments as actual arc labels.
* `PushPuzzle.NCL.Strip.Sweep.unitGraph`: the original graph subdivided and rebased along the actual routing.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.unitSimulation`: dynamic preservation and reflection for the actual unit graph.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal ConstraintGraph

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

private theorem pairs_pos (e : E) : 0 < (R.unitRoute e).consecutivePairs.length := by
  have h := Nat.zero_lt_of_lt (portArc R e false).index.isLt
  simpa only [(portArc_spec R e false).1] using h

/-- One joint for every interior site of the actual unit traversal. -/
@[expose] def jointCount (e : E) : ℕ := (R.unitRoute e).consecutivePairs.length - 1

/-- The actual arc list has one more segment than its number of inserted joints. -/
theorem jointCount_succ (e : E) :
    jointCount R e + 1 = (R.unitRoute e).consecutivePairs.length :=
  Nat.sub_add_cancel (pairs_pos R e)

/-- Standard subdivided segments retain their original-edge and actual-unit-position labels. -/
@[expose] def segmentEquiv : Subdivision.Segment (jointCount R) ≃ Arc R where
  toFun s := ⟨s.1, s.2.cast (jointCount_succ R s.1)⟩
  invFun a := ⟨a.edge, a.index.cast (jointCount_succ R a.edge).symm⟩
  left_inv s := by cases s; rfl
  right_inv a := by cases a; rfl

/-- Original vertices and one joint for each interior site in each original carrier. -/
abbrev UnitVertex := V ⊕ Subdivision.Joint (jointCount R)

/-- The actual strip unit graph, using canonical sweep directions on its actual arc labels. -/
@[expose] def unitGraph (G : ConstraintGraph V E) (w : E → ℕ) :
    ConstraintGraph (UnitVertex R) (Arc R) :=
  ConstraintGraph.map
    ((Subdivision.graph G (jointCount R) w).reorient
      (fun s => (segmentEquiv R s).reversed R)) (segmentEquiv R)

/-- Subdivision, actual arc naming, and geometric direction changes preserve reachability. -/
@[expose] def unitSimulation [DecidableEq E] (G : ConstraintGraph V E) (w : E → ℕ)
    (hw : ∀ e, 0 < w e) (hl : G.LoopFree) : ConstraintGraph.Simulation G (unitGraph R G w) :=
  ((Subdivision.simulation G (jointCount R) w hw hl).trans
    (ConstraintGraph.reorientSimulation (Subdivision.graph G (jointCount R) w)
      (fun s => (segmentEquiv R s).reversed R))).trans
    (ConstraintGraph.Simulation.ofEquiv
      ((Subdivision.graph G (jointCount R) w).reorient
        (fun s => (segmentEquiv R s).reversed R)) (segmentEquiv R) (Equiv.refl _))

/-- Every unit arc in the canonical encoding follows its original edge, with its actual reversal.
-/
theorem unitSimulation_enc [DecidableEq E] (G : ConstraintGraph V E) (w : E → ℕ)
    (hw : ∀ e, 0 < w e) (hl : G.LoopFree) (s : E → Bool) (a : Arc R) :
    (unitSimulation R G w hw hl).enc s a = (a.reversed R ^^ s a.edge) := by
  change ((segmentEquiv R ((segmentEquiv R).symm a)).reversed R ^^
    s ((segmentEquiv R).symm a).1) = (a.reversed R ^^ s a.edge)
  rw [Equiv.apply_symm_apply]
  rfl

private theorem pairs_length (e : E) :
    (R.unitRoute e).consecutivePairs.length = (R.unitRoute e).length - 1 := by
  simp [List.consecutivePairs]

/-- The old endpoint segment is exactly the actual arc selected by its original incidence. -/
private theorem segmentEquiv_port (p : Port E) :
    segmentEquiv R (if p.dir then Subdivision.last (jointCount R) p.edge
      else Subdivision.first (jointCount R) p.edge) = portArc R p.edge p.dir := by
  have hp := (portArc_spec R p.edge p.dir).2
  have hpt : (portArc R p.edge p.dir).lower R = R.center (R.endpoint p.edge p.dir) ∨
      (portArc R p.edge p.dir).upper R = R.center (R.endpoint p.edge p.dir) := by
    split at hp
    · exact Or.inr hp.2
    · exact Or.inl hp.1
  rcases p with ⟨e, d⟩
  cases d
  · let a := segmentEquiv R (Subdivision.first (jointCount R) e)
    apply endpoint_arc_unique R e false rfl (portArc_spec R e false).1 ?_ hpt
    have hh : (R.unitRoute e)[0]? = some (R.center (R.endpoint e false)) := by
      rw [← List.head?_eq_getElem?, PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_head]
      rfl
    obtain ⟨_, hh⟩ := List.getElem_of_getElem? hh
    have hfst : (a.pair R).1 = R.center (R.endpoint e false) := by
      rw [a.pair_at_index R]
      exact hh
    rcases a.pair_eq R with ha | ha
    · exact Or.inl ((congrArg Prod.fst ha).symm.trans hfst)
    · exact Or.inr ((congrArg Prod.fst ha).symm.trans hfst)
  · let a := segmentEquiv R (Subdivision.last (jointCount R) e)
    apply endpoint_arc_unique R e true rfl (portArc_spec R e true).1 ?_ hpt
    have hh : (R.unitRoute e)[(R.unitRoute e).length - 1]? =
        some (R.center (R.endpoint e true)) := by
      rw [← List.getLast?_eq_getElem?, PushPuzzle.NCL.Strip.Environment.unitRoute,
        subdivide_last (R.route_orthogonal e)]
      rfl
    obtain ⟨_, hh⟩ := List.getElem_of_getElem? hh
    have hidx : a.index.val + 1 = (R.unitRoute e).length - 1 :=
      (jointCount_succ R e).trans (pairs_length R e)
    have hsnd : (a.pair R).2 = R.center (R.endpoint e true) := by
      rw [a.pair_at_index R]
      simpa only [hidx, show a.edge = e from rfl] using hh
    rcases a.pair_eq R with ha | ha
    · exact Or.inr ((congrArg Prod.snd ha).symm.trans hsnd)
    · exact Or.inl ((congrArg Prod.snd ha).symm.trans hsnd)

/-- At every original vertex the actual unit graph keeps the original weights and minimum inflow.
Its ports are the actual source arc labels with exactly their geometric direction changes. -/
theorem unitGraph_source (G : ConstraintGraph V E) (w : E → ℕ) (v : V) :
    unitGraph R G w (.inl v) =
      ⟨(G v).ports.map (fun p =>
        ⟨⟨portArc R p.1.edge p.1.dir, (portArc R p.1.edge p.1.dir).reversed R ^^ p.1.dir⟩,
          p.2⟩), (G v).minInflow⟩ := by
  simp only [unitGraph, ConstraintGraph.map, Function.comp_def, ConstraintGraph.reorient,
    Subdivision.graph, Vertex.reorient, Vertex.map, List.map_map, WeightedPort.reorient, WeightedPort.map, Port.reorient, Port.map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [segmentEquiv_port]

/-- The physical grid site of an original vertex or an actual interior unit-path joint. -/
@[expose] def unitPoint : UnitVertex R → Point
  | .inl v => R.center v
  | .inr ⟨e, j⟩ => (((segmentEquiv R) ⟨e, j.succ⟩).pair R).1

/-- The left and right traversal segments of an actual joint meet at its recorded grid site. -/
theorem joint_pair_endpoints (j : Subdivision.Joint (jointCount R)) :
    (((segmentEquiv R) ⟨j.1, j.2.castSucc⟩).pair R).2 = unitPoint R (.inr j) := by
  rcases j with ⟨e, j⟩
  rw [PushPuzzle.NCL.Strip.Sweep.Arc.pair_at_index, unitPoint, PushPuzzle.NCL.Strip.Sweep.Arc.pair_at_index]
  rfl

/-- Each inserted joint has its two actual adjacent arc labels and their geometric incidence bits.
-/
theorem unitGraph_joint (G : ConstraintGraph V E) (w : E → ℕ)
    (j : Subdivision.Joint (jointCount R)) :
    let a := segmentEquiv R ⟨j.1, j.2.castSucc⟩
    let b := segmentEquiv R ⟨j.1, j.2.succ⟩
    unitGraph R G w (.inr j) =
      ⟨[⟨⟨a, decide (a.upper R = unitPoint R (.inr j))⟩, w j.1⟩,
        ⟨⟨b, decide (b.upper R = unitPoint R (.inr j))⟩, w j.1⟩], w j.1⟩ := by
  dsimp only
  have ha := PushPuzzle.NCL.Strip.Sweep.Arc.direction_at R ((segmentEquiv R) ⟨j.1, j.2.castSucc⟩) true
  have hb := PushPuzzle.NCL.Strip.Sweep.Arc.direction_at R ((segmentEquiv R) ⟨j.1, j.2.succ⟩) false
  simp only [Bool.false_eq_true, ite_false, ite_true] at ha hb
  have hpa := joint_pair_endpoints R j
  simp only [hpa] at ha
  have hpb : (((segmentEquiv R) ⟨j.1, j.2.succ⟩).pair R).1 = unitPoint R (.inr j) := rfl
  simp only [hpb] at hb
  dsimp only [unitGraph, ConstraintGraph.map, ConstraintGraph.reorient]
  simp only [Subdivision.graph, Vertex.reorient, Vertex.map, List.map_cons, List.map_nil,
    WeightedPort.reorient, WeightedPort.map, Port.reorient, Port.map, ha, hb, eq_comm]

end PushPuzzle.NCL.Strip.Sweep
