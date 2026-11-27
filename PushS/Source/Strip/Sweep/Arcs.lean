/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.CarrierEvents
public import PushS.Source.Orthogonal.UnitSegments
import Mathlib.Data.List.ProdSigma
import all CslibFrontier.Foundations.Geometry.Orthogonal.UnitSegments

/-!
# Actual unit-arc labels for the strip sweep

A unit arc is an original edge together with one position in its actual unit traversal. Distinct
arc labels never share an undirected unit segment. The proof uses the actual carrier contact
classification: all shared grid sites are even in both coordinates, while a unit step changes
one coordinate's parity.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Arc`: an actual unit segment occurrence of an original carrier.
* `PushPuzzle.NCL.Strip.Sweep.arcs`: finite unit-arc enumeration from the original edge list.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Arc.undirected_injective`: geometric unit segments identify their original labels.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- An original carrier and one position in its actual unit-segment list. -/
structure Arc where
  /-- Original edge of the carrier. -/
  edge : E
  /-- Position in the actual consecutive-pair list. -/
  index : Fin (R.unitRoute edge).consecutivePairs.length

instance [DecidableEq E] : DecidableEq (Arc R) := fun a b => by
  rcases a with ⟨e, i⟩
  rcases b with ⟨f, j⟩
  by_cases he : e = f
  · subst f
    by_cases hi : i = j
    · exact isTrue (by cases hi; rfl)
    · exact isFalse (fun h => by cases h; exact hi rfl)
  · exact isFalse (fun h => he (congrArg PushPuzzle.NCL.Strip.Sweep.Arc.edge h))

namespace Arc

open Cslib.Complexity Cslib.Complexity.NCL

/-- The actual ordered endpoints of the selected unit segment. -/
@[expose] def pair (a : Arc R) : Point × Point := (R.unitRoute a.edge).consecutivePairs.get a.index

/-- Every arc label selects an actual consecutive pair. -/
theorem pair_mem (a : Arc R) : a.pair R ∈ (R.unitRoute a.edge).consecutivePairs :=
  List.get_mem _ _

/-- An actual unit-segment position has its successor inside the original unit-point list. -/
theorem index_succ_lt (a : Arc R) : a.index.val + 1 < (R.unitRoute a.edge).length := by
  have h := a.index.isLt
  simp only [List.consecutivePairs, List.length_zip, List.length_tail] at h
  omega

/-- The selected pair consists of the actual point at the arc index and its successor. -/
theorem pair_at_index (a : Arc R) : a.pair R =
    ((R.unitRoute a.edge)[a.index.val]'(by have := a.index_succ_lt R; omega),
      (R.unitRoute a.edge)[a.index.val + 1]'(a.index_succ_lt R)) := by
  simp only [pair, List.get_eq_getElem, List.consecutivePairs, List.getElem_zip, List.getElem_tail]

/-- Every actual arc has Manhattan length one. -/
theorem unit (a : Arc R) : length (a.pair R).1 (a.pair R).2 = 1 :=
  subdivide_unit (R.route_orthogonal a.edge) (a.pair_mem R)

/-- Both unit-arc endpoints belong to the original complete real carrier. -/
theorem endpoints_mem (a : Arc R) :
    realPoint (a.pair R).1 ∈ support (R.route a.edge) ∧
      realPoint (a.pair R).2 ∈ support (R.route a.edge) := by
  have hm := List.of_mem_zip (a.pair_mem R)
  exact ⟨(R.mem_unitRoute _ _).mp hm.1,
    (R.mem_unitRoute _ _).mp (List.mem_of_mem_tail hm.2)⟩

private theorem pairs_nodup (e : E) : (R.unitRoute e).consecutivePairs.Nodup := by
  have hn : ((R.unitRoute e).consecutivePairs.map Prod.snd).Nodup := by
    rw [List.consecutivePairs, List.map_snd_zip (by simp)]
    exact (R.unitRoute_nodup e).tail
  exact hn.of_map _

/-- Within one original carrier, the selected ordered unit segment identifies its position. -/
theorem eq_of_pair_eq {a b : Arc R} (he : a.edge = b.edge) (hp : a.pair R = b.pair R) : a = b := by
  rcases a with ⟨e, i⟩
  rcases b with ⟨f, j⟩
  dsimp only at he
  subst f
  have hij := (List.nodup_iff_injective_get.mp (pairs_nodup R e)) hp
  cases hij
  rfl

private theorem site_even (e f : E) (d : Bool) :
    (R.crossingSite e f d).1 % 2 = 0 ∧ (R.crossingSite e f d).2 % 2 = 0 := by
  simp only [PushPuzzle.NCL.Strip.Environment.crossingSite, PushPuzzle.NCL.Strip.Tracks.column, Layout.column, PushPuzzle.NCL.Strip.Tracks.rail]
  constructor <;> omega

private theorem contact_even {e f : E} (hef : e ≠ f) {p : Point}
    (hp : realPoint p ∈ support (R.route e)) (hq : realPoint p ∈ support (R.route f)) :
    p.1 % 2 = 0 ∧ p.2 % 2 = 0 := by
  have even_cross {a b : E} {d : Bool} (h : R.Crossing a b d (realPoint p)) :
      p.1 % 2 = 0 ∧ p.2 % 2 = 0 := by
    have he := realPoint_injective (R.crossing_point h)
    rw [he]
    exact site_even R _ _ _
  rcases R.route_contact hef hp hq with hc | hc | hc | hc | hc
  · obtain ⟨v, _, _, hc⟩ := hc
    have he := realPoint_injective hc
    rw [he]
    simp only [PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.center]
    constructor <;> omega
  all_goals exact even_cross hc

/-- No two different unit-arc labels share the same undirected geometric unit segment. -/
theorem undirected_injective {a b : Arc R}
    (h : a.pair R = b.pair R ∨ a.pair R = ((b.pair R).2, (b.pair R).1)) : a = b := by
  have he : a.edge = b.edge := by
    by_contra hne
    have ha := a.endpoints_mem R
    have hb := b.endpoints_mem R
    have hp : realPoint (a.pair R).1 ∈ support (R.route b.edge) := by
      rcases h with h | h
      · simpa only [h] using hb.1
      · simpa only [h] using hb.2
    have hq : realPoint (a.pair R).2 ∈ support (R.route b.edge) := by
      rcases h with h | h
      · simpa only [h] using hb.2
      · simpa only [h] using hb.1
    have he₀ := contact_even R hne ha.1 hp
    have he₁ := contact_even R hne ha.2 hq
    have hu := a.unit R
    simp only [length] at hu
    omega
  rcases h with h | h
  · exact eq_of_pair_eq R he h
  · by_cases hp : a.pair R = b.pair R
    · exact eq_of_pair_eq R he hp
    · have hb : b.pair R ∈ (R.unitRoute a.edge).consecutivePairs := by
        simpa only [he] using b.pair_mem R
      exact False.elim (no_reverse_pairs (R.unitRoute_nodup a.edge) (a.pair_mem R) hb hp h)

end Arc

/-- Actual unit-arc occurrences, in original-edge order and then original traversal order. -/
@[expose] def arcs (es : List E) : List (Arc R) :=
  es.flatMap fun e => List.ofFn (fun i => ⟨e, i⟩)

/-- Every position on every declared carrier occurs in the explicit unit-arc list. -/
theorem mem_arcs (es : List E) (a : Arc R) : a ∈ arcs R es ↔ a.edge ∈ es := by
  constructor
  · intro ha
    obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    have h := congrArg PushPuzzle.NCL.Strip.Sweep.Arc.edge hi
    exact h ▸ he
  · intro ha
    exact List.mem_flatMap.mpr ⟨a.edge, ha, List.mem_ofFn.mpr ⟨a.index, rfl⟩⟩

/-- The unit-arc enumeration introduces no repeated labels. -/
theorem arcs_nodup {es : List E} (hes : es.Nodup) : (arcs R es).Nodup := by
  rw [arcs, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro e _
    apply List.nodup_ofFn.mpr
    intro i j hij
    exact Fin.ext (congrArg (fun a : Arc R => a.index.val) hij)
  · apply hes.imp
    intro e f hef a ha hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hf
    exact hef (congrArg PushPuzzle.NCL.Strip.Sweep.Arc.edge hj).symm

end PushPuzzle.NCL.Strip.Sweep
