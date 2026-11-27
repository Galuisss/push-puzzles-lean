/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Planar.GridDrawing.UnitRoute
import all PushS.Source.Planar.GridDrawing.UnitRoute
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute
public import PushS.Source.Orthogonal.UnitSegments
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
public import CslibFrontier.Algorithms.Reachability.ShortestWalk
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Geometry.Orthogonal.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Dist
import Mathlib.Data.Int.NatAbs

/-!
# Deterministic simple routes inside fixed marked grid windows

Use the library's breadth-first search on the marked lattice points of a fixed rectangle,
with unit steps that never go upward. Erase cycles and retain the source-to-target direction. The
finite window table has standard canonical-coordinate encodings.

## Main definitions

* `PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern`: actual marked window and prescribed ordered endpoints.
* `PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.route`: source-to-target simple unit route selected by BFS.

## Main results

* `PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.computableInPolyTime_route`: fixed-window table dispatch.
* `PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.integerRoute_spec`: exact endpoints and marked simple units.
-/

public section

namespace PushPuzzle.NCL.GridDrawing.WindowRoute

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing Cslib _root_.Turing.MultiTapeTM

/-- A lattice point in the fixed closed rectangle `[0,width] × [0,span]`. -/
abbrev Point (width span : ℕ) := Fin (width + 1) × Fin (span + 1)

/-- Canonical finite coordinate encodings, horizontal coordinate followed by vertical. -/
abbrev encPoint (width span : ℕ) : Point width span ↪ List Bool :=
  encPair (encFinEnum (Fin (width + 1))) (encFinEnum (Fin (span + 1)))

/-- The actual undirected unit-grid graph of the fixed rectangle. -/
@[expose] def graph (width span : ℕ) : SimpleGraph (Point width span) where
  Adj p q := Nat.dist p.1.val q.1.val + Nat.dist p.2.val q.2.val = 1
  symm := ⟨by intro p q h; simpa only [Nat.dist_comm] using h⟩
  loopless := ⟨by intro p h; simp at h⟩

instance (width span : ℕ) : DecidableRel (graph width span).Adj := fun _ _ => inferInstanceAs
  (Decidable (_ + _ = 1))

/-- Original unit-grid steps that preserve the downward direction of the native word drawing. -/
@[expose] def step {width span : ℕ} (p q : Point width span) : Bool :=
  decide ((graph width span).Adj p q ∧ p.2.val ≤ q.2.val)

/-- A fixed local marked trace and its original ordered source and target. -/
structure Pattern (width span : ℕ) where
  /-- Original source point in the translated window. -/
  source : Point width span
  /-- Original target point in the same window. -/
  target : Point width span
  /-- Original trace membership, in canonical horizontal/vertical coordinate order. -/
  marked : Fin (width + 1) → Fin (span + 1) → Bool

/-- Standard finite endpoint coordinates followed by the canonical two-dimensional Boolean table.
-/
enc_structure encPattern (width : ℕ) (span : ℕ) : Pattern width span where
  source : (encPoint width span), target : (encPoint width span),
  marked : (encFinFn (width + 1) (encFinFn (span + 1) encBool))

private instance (width span : ℕ) : Finite (Pattern width span) :=
  Finite.of_injective (fun q : Pattern width span => (q.source, q.target, q.marked))
    (by rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h; cases h; rfl)

/-- Actual marked lattice points, in canonical coordinate order. -/
@[expose] def Pattern.points {width span : ℕ} (P : Pattern width span) : List (Point width span) :=
  ((List.finRange (width + 1)).product (List.finRange (span + 1))).filter
    (fun p => P.marked p.1 p.2)

/-- Search the same marked unit-grid graph from the prescribed source to prescribed target. -/
@[expose] def Pattern.search {width span : ℕ} (P : Pattern width span) :
    List (Point width span) ⊕ List (Point width span) :=
  Cslib.Reachability.findWalk P.points step
    (fun p => p == P.source) (fun p => p == P.target)

private def foundWalk {width span : ℕ} (P : Pattern width span) (r : List (Point width span))
    (hr : P.search = .inl r) : (graph width span).Walk P.source P.target :=
  let h := (Cslib.Reachability.isShortestSrcTgtWalk_of_findWalk_eq_inl hr).1
  (SimpleGraph.Walk.ofSupport r h.choose
    (h.choose_spec.2.2.2.imp (fun _ _ h => (of_decide_eq_true h).1))).copy
      (by exact of_decide_eq_true (by simpa using h.choose_spec.1))
      (by exact of_decide_eq_true (by simpa using h.choose_spec.2.1))

/-- The actual BFS path after cycle erasure, retaining its original ordered endpoints. -/
def Pattern.path {width span : ℕ} (P : Pattern width span) :
    Option ((graph width span).Path P.source P.target) :=
  match h : P.search with
  | .inl r => some (foundWalk P r h).toPath
  | .inr _ => none

/-- The finite marked-window route is serialized in its original source-to-target direction. -/
def Pattern.route {width span : ℕ} (P : Pattern width span) : List (Point width span) :=
  (P.path.map (fun p => p.val.support)).getD []

/-- Fixed-window BFS route selection is polynomial-time under its standard finite data encoding.
-/
theorem Pattern.computableInPolyTime_route (width span : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.route (width := width) (span := span))
      (encPattern width span) (encList (encPoint width span)) :=
  ComputableInPolyTime.of_finite _

private theorem support_foundWalk {width span : ℕ} (P : Pattern width span)
    (r : List (Point width span)) (hr : P.search = .inl r) :
    (foundWalk P r hr).support = r := by
  simp only [foundWalk, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]

/-- A connected marked window returns a simple marked unit path with its ordered endpoints. -/
theorem Pattern.route_spec {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points
      step
      (fun p => p == P.source) (fun p => p == P.target) r) :
    P.route.head? = some P.source ∧ P.route.getLast? = some P.target ∧ P.route.Nodup ∧
      (∀ p ∈ P.route, P.marked p.1 p.2 = true) ∧
      P.route.IsChain ((graph width span).Adj) ∧
      P.route.Pairwise (fun p q => p.2.val ≤ q.2.val) := by
  have hex := (Cslib.Reachability.findWalk_isLeft_iff).mpr h
  change P.search.isLeft = true at hex
  cases hr : P.search with
  | inr r => simp only [hr, Sum.isLeft_inr, Bool.false_eq_true] at hex
  | inl r =>
    let path := (foundWalk P r hr).toPath
    have heq : P.route = path.val.support := by
      unfold PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.route PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.path
      split
      · rename_i r' hr'
        have he : r' = r := Sum.inl.inj (hr'.symm.trans hr)
        subst r'
        rfl
      · rename_i r' hr'
        have he := hr'.symm.trans hr
        cases he
    rw [heq]
    have hs := (Cslib.Reachability.isShortestSrcTgtWalk_of_findWalk_eq_inl hr).1
    refine ⟨?_, ?_, path.property.support_nodup, ?_, path.val.isChain_adj_support, ?_⟩
    · exact (List.head?_eq_some_head path.val.support_ne_nil).trans
        (congrArg some path.val.head_support)
    · exact (List.getLast?_eq_some_getLast path.val.support_ne_nil).trans
        (congrArg some path.val.getLast_support)
    · intro p hp
      have hm := (foundWalk P r hr).support_toPath_subset_support hp
      rw [support_foundWalk P r hr] at hm
      exact (List.mem_filter.mp (hs.choose_spec.2.2.1 p hm)).2
    · let : Trans (fun p q : Point width span => p.2.val ≤ q.2.val)
          (fun p q : Point width span => p.2.val ≤ q.2.val)
          (fun p q : Point width span => p.2.val ≤ q.2.val) :=
        ⟨by intro p q t hp hq; omega⟩
      have hc := hs.choose_spec.2.2.2.imp (fun _ _ h => (of_decide_eq_true h).2)
      have hraw : (foundWalk P r hr).support.Pairwise (fun p q => p.2.val ≤ q.2.val) := by
        rw [support_foundWalk P r hr]
        exact hc.pairwise
      exact hraw.sublist (foundWalk P r hr).support_bypass_sublist_support

/-- Include the actual finite-window point in the integer coordinate plane. -/
@[expose] def point {width span : ℕ} (p : Point width span) : Orthogonal.Point :=
  ((p.1.val : ℤ), (p.2.val : ℤ))

private theorem point_injective (width span : ℕ) :
    Function.Injective (point (width := width) (span := span)) := by
  intro p q h
  have hx : p.1.val = q.1.val := Int.natCast_inj.mp (congrArg Prod.fst h)
  have hy : p.2.val = q.2.val := Int.natCast_inj.mp (congrArg Prod.snd h)
  exact Prod.ext (Fin.ext hx) (Fin.ext hy)

private theorem natAbs_dist (a b : ℕ) : ((a : ℤ) - b).natAbs = Nat.dist a b := by
  cases le_total a b with
  | inl h => rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.dist_eq_sub_of_le h]
  | inr h => rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.dist_eq_sub_of_le_right h]

private def gridHom (width span : ℕ) : graph width span →g GridDrawing.unitGraph where
  toFun := point
  map_rel' := by
    intro p q h
    change Orthogonal.length (point p) (point q) = 1
    simpa only [graph, Orthogonal.length, point, natAbs_dist, Nat.dist_comm] using h

/-- Integer-coordinate serialization of the same ordered marked-window BFS route. -/
def Pattern.integerRoute {width span : ℕ} (P : Pattern width span) : Orthogonal.Route :=
  P.route.map point

/-- The same selected integer route emits in the standard binary coordinate encoding. -/
theorem Pattern.computableInPolyTime_integerRoute (width span : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.integerRoute (width := width) (span := span))
      (encPattern width span) Orthogonal.encRoute := by
  have hp : ComputableInPolyTime (point (width := width) (span := span))
      (encPoint width span) Orthogonal.encPoint := ComputableInPolyTime.of_finite _
  unfold PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.integerRoute
  apply ComputableInPolyTime.mapWithInput (PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.computableInPolyTime_route width span)
  exact hp.comp (ComputableInPolyTime.snd _ _)

/-- A connected marked window gives the ordered, continuously simple original unit-grid route.
-/
theorem Pattern.integerRoute_spec {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points
      step
      (fun p => p == P.source) (fun p => p == P.target) r) :
    P.integerRoute.head? = some (point P.source) ∧
      P.integerRoute.getLast? = some (point P.target) ∧
      Orthogonal.IsSimple P.integerRoute ∧
      (∀ e ∈ P.integerRoute.consecutivePairs, Orthogonal.length e.1 e.2 = 1) ∧
      (∀ p ∈ P.integerRoute, ∃ q, P.marked q.1 q.2 = true ∧ point q = p) ∧
      P.integerRoute.Pairwise (fun p q => p.2 ≤ q.2) := by
  obtain ⟨hs, ht, hn, hm, hc, hy⟩ := P.route_spec h
  have hne : P.route ≠ [] := by intro he; simp [he] at hs
  let walk := SimpleGraph.Walk.ofSupport P.route hne hc
  have heq : (walk.map (gridHom width span)).support = P.integerRoute := by
    rw [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_ofSupport]
    rfl
  have hu : ∀ e ∈ P.integerRoute.consecutivePairs, Orthogonal.length e.1 e.2 = 1 := by
    rw [← heq]
    exact GridDrawing.unit_walk_support _
  refine ⟨?_, ?_, Cslib.Orthogonal.isSimple_of_unit_nodup (hn.map (point_injective width span)) hu,
    hu, ?_, ?_⟩
  · simp only [PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.integerRoute, List.head?_map, hs, Option.map_some]
  · simp only [PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.integerRoute, List.getLast?_map, ht, Option.map_some]
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨q, hm q hq, rfl⟩
  · apply List.pairwise_map.mpr
    exact hy.imp (fun {p q} h => by simpa only [point, Nat.cast_le] using h)

end PushPuzzle.NCL.GridDrawing.WindowRoute
