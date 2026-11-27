/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Environment
public import PushS.Source.Orthogonal.Transverse
import Mathlib.Tactic.Linarith

/-!
# Crossings of the actual parity-track carriers

Every nonvertex contact is a strict bridge/stem crossing. A crossing site identifies its one
horizontal edge and its one vertical incidence, even though tracks are reused in distant panels.

## Main definitions

* `PushPuzzle.NCL.Strip.Environment.Crossing`: a strict crossing of one bridge and another edge's port stem.

## Main results

* `PushPuzzle.NCL.Strip.Environment.route_contact`: complete real contact classification.
* `PushPuzzle.NCL.Strip.Environment.crossing_unique`: each crossing site has one bridge and one stem.
-/

public section

namespace PushPuzzle.NCL.Strip.Environment

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- A strict bridge/stem crossing of two actual carriers. -/
@[expose] def Crossing (e f : E) (d : Bool) (p : ℝ × ℝ) : Prop :=
  Transverse
    (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint e false)) (R.port e false),
      PushPuzzle.NCL.Strip.Tracks.rail (R.track e))
    (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint e true)) (R.port e true),
      PushPuzzle.NCL.Strip.Tracks.rail (R.track e))
    (PushPuzzle.NCL.Strip.Tracks.elbow (R.vertices.address (R.endpoint f d)) (R.port f d))
    (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f d)) (R.port f d), PushPuzzle.NCL.Strip.Tracks.rail (R.track f)) p

private theorem incidence_address_injective : Function.Injective
    (fun p : E × Bool => (R.vertices.address (R.endpoint p.1 p.2), R.port p.1 p.2)) := by
  intro p q h
  have ha := congrArg (fun x : ℕ × Fin 3 => x.1) h
  have hp := congrArg (fun x : ℕ × Fin 3 => x.2) h
  apply R.incidence_injective
  exact Prod.ext (R.vertices.address_injective ha) hp

/-- Any contact of distinct actual carriers is a shared endpoint center or a strict crossing. -/
theorem route_contact {e f : E} (hef : e ≠ f) {p : ℝ × ℝ}
    (he : p ∈ support (R.route e)) (hf : p ∈ support (R.route f)) :
    (∃ v, (v = R.endpoint e false ∨ v = R.endpoint e true) ∧
      (v = R.endpoint f false ∨ v = R.endpoint f true) ∧ p = realPoint (R.center v)) ∨
      R.Crossing e f false p ∨ R.Crossing e f true p ∨
      R.Crossing f e false p ∨ R.Crossing f e true p := by
  by_cases ht : R.track e = R.track f
  · exact False.elim (Set.disjoint_left.mp (R.same_track_disjoint hef ht) he hf)
  have hp (d d' : Bool) :
      (R.vertices.address (R.endpoint e d), R.port e d) ≠
        (R.vertices.address (R.endpoint f d'), R.port f d') :=
    by
      intro h
      have h' : (e, d) = (f, d') := R.incidence_address_injective h
      exact hef (congrArg Prod.fst h')
  rcases PushPuzzle.NCL.Strip.Tracks.route_contact ht (hp false false) (hp false true) (hp true false)
    (hp true true) he hf with hc | hc | hc | hc | hc
  · obtain ⟨w, hw, hv, hc⟩ := hc
    rcases hw with rfl | rfl
    · exact Or.inl ⟨_, Or.inl rfl, hv.imp (fun h => R.vertices.address_injective h)
        (fun h => R.vertices.address_injective h), hc⟩
    · exact Or.inl ⟨_, Or.inr rfl, hv.imp (fun h => R.vertices.address_injective h)
        (fun h => R.vertices.address_injective h), hc⟩
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))

/-- Integer site of the bridge/port-stem crossing candidate. -/
@[expose] def crossingSite (e f : E) (d : Bool) : Point :=
  (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f d)) (R.port f d), PushPuzzle.NCL.Strip.Tracks.rail (R.track e))

/-- A crossing has its exact integer port-column and rail-height coordinates. -/
theorem crossing_point {e f : E} {d : Bool} {p : ℝ × ℝ} (h : R.Crossing e f d p) :
    p = realPoint (R.crossingSite e f d) := PushPuzzle.NCL.Strip.Tracks.bridge_stem_crossing_point h

/-- The original bridge is part of its complete carrier support. -/
theorem bridge_mem_support (e : E) {p : ℝ × ℝ}
    (h : p ∈ PushPuzzle.NCL.Strip.Tracks.bridge (R.track e)
      (R.vertices.address (R.endpoint e false)) (R.vertices.address (R.endpoint e true))
      (R.port e false) (R.port e true)) : p ∈ support (R.route e) := by
  rw [route, PushPuzzle.NCL.Strip.Tracks.support_route]
  exact Or.inl (Or.inl (Or.inr h))

/-- Either original endpoint stem is part of the complete carrier support. -/
theorem stem_mem_support (e : E) (d : Bool) {p : ℝ × ℝ}
    (h : p ∈ PushPuzzle.NCL.Strip.Tracks.stem (R.track e) (R.vertices.address (R.endpoint e d)) (R.port e d)) :
    p ∈ support (R.route e) := by
  rw [route, PushPuzzle.NCL.Strip.Tracks.support_route]
  cases d
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inr h)

private theorem bridge_unique {e f : E} {p : ℝ × ℝ}
    (he : p ∈ PushPuzzle.NCL.Strip.Tracks.bridge (R.track e)
      (R.vertices.address (R.endpoint e false)) (R.vertices.address (R.endpoint e true))
      (R.port e false) (R.port e true))
    (hf : p ∈ PushPuzzle.NCL.Strip.Tracks.bridge (R.track f)
      (R.vertices.address (R.endpoint f false)) (R.vertices.address (R.endpoint f true))
      (R.port f false) (R.port f true)) : e = f := by
  by_contra hef
  by_cases ht : R.track e = R.track f
  · exact Set.disjoint_left.mp (R.same_track_disjoint hef ht)
      (R.bridge_mem_support e he) (R.bridge_mem_support f hf)
  · exact Set.disjoint_left.mp (PushPuzzle.NCL.Strip.Tracks.bridge_disjoint ht _ _ _ _) he hf

/-- One geometric crossing site identifies its unique horizontal edge and vertical incidence.
Consequently a site never carries three lines. -/
theorem crossing_unique {e f e' f' : E} {d d' : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) (h' : R.Crossing e' f' d' p) :
    e = e' ∧ (f, d) = (f', d') := by
  have he := (PushPuzzle.Orthogonal.Transverse.mem h).1
  have he' := (PushPuzzle.Orthogonal.Transverse.mem h').1
  have hx := congrArg Prod.fst ((R.crossing_point h).symm.trans (R.crossing_point h'))
  change (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f d)) (R.port f d) : ℝ) =
    (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f' d')) (R.port f' d') : ℝ) at hx
  have hcol : PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f d)) (R.port f d) =
      PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f' d')) (R.port f' d') := by exact_mod_cast hx
  obtain ⟨ha, hp⟩ := Layout.column_injective hcol
  exact ⟨R.bridge_unique he he', R.incidence_address_injective (Prod.ext ha hp)⟩

/-- Strict crossings are above every original vertex center. -/
theorem crossing_not_center {e f : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) (v : V) : p ≠ realPoint (R.center v) := by
  intro he
  have hy := congrArg Prod.snd ((R.crossing_point h).symm.trans he)
  simp only [realPoint, crossingSite, center, PushPuzzle.NCL.Strip.Tracks.center, PushPuzzle.NCL.Strip.Tracks.rail,
    Int.cast_add, Int.cast_mul,
    Int.cast_natCast, Int.cast_ofNat] at hy
  have ht : (0 : ℝ) ≤ R.track e := by positivity
  linarith

/-- The only carriers through a strict crossing are its two participating original edges. -/
theorem crossing_routes_eq {e f g : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) (hg : p ∈ support (R.route g)) : g = e ∨ g = f := by
  by_cases heg : e = g
  · exact Or.inl heg.symm
  have he := R.bridge_mem_support e (PushPuzzle.Orthogonal.Transverse.mem h).1
  rcases R.route_contact heg he hg with hc | hc | hc | hc | hc
  · obtain ⟨v, _, _, hv⟩ := hc
    exact False.elim (R.crossing_not_center h v hv)
  · exact Or.inr (congrArg Prod.fst (R.crossing_unique h hc).2).symm
  · exact Or.inr (congrArg Prod.fst (R.crossing_unique h hc).2).symm
  · exact False.elim (heg (R.crossing_unique h hc).1)
  · exact False.elim (heg (R.crossing_unique h hc).1)

private theorem crossing_not_low {e f : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) {a : Point} (ha : a.2 ≤ 6) : p ≠ realPoint a := by
  intro he
  have hy := congrArg Prod.snd ((R.crossing_point h).symm.trans he)
  have ha' : (a.2 : ℝ) ≤ 6 := by exact_mod_cast ha
  change (PushPuzzle.NCL.Strip.Tracks.rail (R.track e) : ℝ) = a.2 at hy
  simp only [PushPuzzle.NCL.Strip.Tracks.rail, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at hy
  have ht : (0 : ℝ) ≤ R.track e := by positivity
  linarith

private theorem crossing_not_top_left {e f : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) (d' : Bool) :
    p ≠ realPoint (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint e d')) (R.port e d'),
      PushPuzzle.NCL.Strip.Tracks.rail (R.track e)) := by
  intro he
  have hx := congrArg Prod.fst ((R.crossing_point h).symm.trans he)
  simp only [realPoint, crossingSite, Int.cast_inj] at hx
  have hcol := PushPuzzle.NCL.Strip.Tracks.bridge_stem_column_ne h
  cases d'
  · exact hcol.1 hx
  · exact hcol.2 hx

private theorem crossing_not_top_right {e f : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) (d' : Bool) :
    p ≠ realPoint (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint f d')) (R.port f d'),
      PushPuzzle.NCL.Strip.Tracks.rail (R.track f)) := by
  intro he
  have hy := congrArg Prod.snd ((R.crossing_point h).symm.trans he)
  simp only [realPoint, crossingSite, Int.cast_inj, PushPuzzle.NCL.Strip.Tracks.rail] at hy
  have hlt := PushPuzzle.NCL.Strip.Tracks.bridge_stem_track_lt h
  omega

private theorem point_cases (e : E) {a : Point} (ha : a ∈ R.route e) :
    a.2 ≤ 6 ∨ ∃ d, a =
      (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint e d)) (R.port e d),
        PushPuzzle.NCL.Strip.Tracks.rail (R.track e)) := by
  simp only [route, PushPuzzle.NCL.Strip.Tracks.route, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by norm_num [PushPuzzle.NCL.Strip.Tracks.center])
  · exact Or.inl (by simp only [PushPuzzle.NCL.Strip.Tracks.elbow]; split_ifs <;> omega)
  · exact Or.inr ⟨false, rfl⟩
  · exact Or.inr ⟨true, rfl⟩
  · exact Or.inl (by simp only [PushPuzzle.NCL.Strip.Tracks.elbow]; split_ifs <;> omega)
  · exact Or.inl (by norm_num [PushPuzzle.NCL.Strip.Tracks.center])

/-- Strict crossings avoid every listed source center, fan elbow, and bridge bend of every
carrier in the entire environment. -/
theorem crossing_not_points {e f g : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) {a : Point} (ha : a ∈ R.route g) : p ≠ realPoint a := by
  rcases R.point_cases g ha with hlow | ⟨d', htop⟩
  · exact R.crossing_not_low h hlow
  · intro he
    have hm : p ∈ support (R.route g) := Or.inl ⟨a, ha, he⟩
    subst a
    rcases R.crossing_routes_eq h hm with rfl | rfl
    · exact R.crossing_not_top_left h d' he
    · exact R.crossing_not_top_right h d' he

end PushPuzzle.NCL.Strip.Environment
