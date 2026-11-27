/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Contact
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# Enumerating the actual carrier crossings

A crossing has a distinguished horizontal bridge and a distinguished vertical endpoint stem.
The explicit finite edge list supplies all candidate triples. An integer interval test selects
exactly the strict real crossings of the already constructed six-point carriers.

## Main definitions

* `PushPuzzle.NCL.Strip.Event`: the two original edges and vertical incidence of one crossing candidate.
* `PushPuzzle.NCL.Strip.Environment.events`: the actual filtered finite crossing list.

## Main results

* `PushPuzzle.NCL.Strip.Event.test_iff`: the computable integer test is exact for continuous transversality.
* `PushPuzzle.NCL.Strip.Environment.events_sites_nodup`: distinct listed events have distinct integer sites.
-/

public section

namespace PushPuzzle.NCL.Strip

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

/-- A horizontal bridge crossing one endpoint stem of another original edge. -/
@[ext] structure Event (E : Type*) where
  /-- Original edge providing the horizontal bridge. -/
  bridge : E
  /-- Original edge providing the vertical stem. -/
  stem : E
  /-- The vertical stem's original endpoint direction. -/
  dir : Bool
  deriving @[expose] DecidableEq

namespace Event

open Cslib.Complexity Cslib.Complexity.NCL

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Integer site associated with the candidate bridge and stem. -/
@[expose] def site (c : Event E) : Point := R.crossingSite c.bridge c.stem c.dir

/-- This candidate is an actual strict bridge/stem crossing. -/
@[expose] def Valid (c : Event E) : Prop :=
  R.Crossing c.bridge c.stem c.dir (realPoint (c.site R))

/-- Test two strict horizontal inequalities and the vertical ordering of the two rails. -/
@[expose] def test (c : Event E) : Bool := decide (
  min (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.bridge false)) (R.port c.bridge false))
      (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.bridge true)) (R.port c.bridge true)) <
    (c.site R).1 ∧
  (c.site R).1 <
    max (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.bridge false)) (R.port c.bridge false))
      (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.bridge true)) (R.port c.bridge true)) ∧
  R.track c.bridge < R.track c.stem)

/-- The integer test selects exactly the strict continuous crossings. -/
theorem test_iff (c : Event E) : c.test R = true ↔ c.Valid R := by
  rw [test, decide_eq_true_eq]
  constructor
  · rintro ⟨hx₀, hx₁, ht⟩
    have hlo := PushPuzzle.NCL.Strip.Tracks.elbow_below_rail (R.track c.bridge)
      (R.vertices.address (R.endpoint c.stem c.dir)) (R.port c.stem c.dir)
    have hi := PushPuzzle.NCL.Strip.Tracks.elbow_below_rail (R.track c.stem)
      (R.vertices.address (R.endpoint c.stem c.dir)) (R.port c.stem c.dir)
    refine Or.inl ⟨rfl, rfl, rfl, hx₀, hx₁, ?_, ?_⟩
    · change min _ _ < PushPuzzle.NCL.Strip.Tracks.rail (R.track c.bridge)
      rw [min_eq_left hi.le]
      exact hlo
    · change PushPuzzle.NCL.Strip.Tracks.rail (R.track c.bridge) < max _ _
      rw [max_eq_right hi.le]
      simp only [PushPuzzle.NCL.Strip.Tracks.rail]
      omega
  · intro h
    have ht := PushPuzzle.NCL.Strip.Tracks.bridge_stem_track_lt h
    rcases h with ⟨_, _, _, hx₀, hx₁, _⟩ | ⟨_, _, _, hx₀, hx₁, _⟩
    · exact ⟨hx₀, hx₁, ht⟩
    · simp only [PushPuzzle.NCL.Strip.Tracks.elbow, min_self, max_self] at hx₀ hx₁
      omega

/-- A strict crossing always joins two distinct original edges. -/
theorem Valid.ne {c : Event E} (h : c.Valid R) : c.bridge ≠ c.stem := by
  have ht := PushPuzzle.NCL.Strip.Tracks.bridge_stem_track_lt h
  exact fun he => (ne_of_lt ht) (congrArg R.track he)

/-- Distinct actual events cannot occupy the same integer routing site. -/
theorem site_injective {c d : Event E} (hc : c.Valid R) (hd : d.Valid R)
    (h : c.site R = d.site R) : c = d := by
  have hd' : R.Crossing d.bridge d.stem d.dir (realPoint (c.site R)) := by
    simpa only [Valid, h] using hd
  obtain ⟨hb, hs⟩ := R.crossing_unique hc hd'
  exact PushPuzzle.NCL.Strip.Event.ext hb (congrArg Prod.fst hs) (congrArg Prod.snd hs)

/-- All bridge/stem/direction combinations of an explicit finite edge list.
The product is the Cartesian enumeration of candidates. -/
@[expose] def candidates (es : List E) : List (Event E) :=
  (es ×ˢ (es ×ˢ [false, true])).map fun ⟨e, f, d⟩ => ⟨e, f, d⟩

/-- A candidate occurs exactly when both of its original edges occur. -/
theorem mem_candidates (es : List E) (c : Event E) :
    c ∈ candidates es ↔ c.bridge ∈ es ∧ c.stem ∈ es := by
  rcases c with ⟨e, f, d⟩
  cases d <;> simp [candidates, PushPuzzle.NCL.Strip.Event.mk.injEq]

/-- A nonrepeating edge enumeration produces a nonrepeating candidate list. -/
private theorem candidates_nodup {es : List E} (h : es.Nodup) : (candidates es).Nodup := by
  apply (h.product (h.product (by decide : ([false, true] : List Bool).Nodup))).map
  rintro ⟨e, f, b⟩ ⟨e', f', b'⟩ hh
  simpa only [PushPuzzle.NCL.Strip.Event.mk.injEq, Prod.mk.injEq] using hh

end Event

namespace Environment

open Cslib.Complexity Cslib.Complexity.NCL

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- All actual strict crossings, in finite bridge/stem/direction enumeration order. -/
@[expose] def events (es : List E) : List (Event E) :=
  (PushPuzzle.NCL.Strip.Event.candidates es).filter (PushPuzzle.NCL.Strip.Event.test R)

/-- Filtering retains precisely the actual crossings on the declared original edges. -/
theorem mem_events (es : List E) (c : Event E) :
    c ∈ R.events es ↔ c.bridge ∈ es ∧ c.stem ∈ es ∧ c.Valid R := by
  simp only [events, List.mem_filter, PushPuzzle.NCL.Strip.Event.mem_candidates, PushPuzzle.NCL.Strip.Event.test_iff, and_assoc]

/-- Every nonvertex contact of two declared carriers belongs to the actual finite event list.
The participating original edges are retained in the event. -/
theorem nonvertex_contact_event (es : List E) {e f : E} (he : e ∈ es) (hf : f ∈ es)
    (hef : e ≠ f) {p : ℝ × ℝ} (hp : p ∈ support (R.route e))
    (hq : p ∈ support (R.route f)) (hv : ∀ v, p ≠ realPoint (R.center v)) :
    ∃ c ∈ R.events es, p = realPoint (c.site R) ∧
      (c.bridge = e ∧ c.stem = f ∨ c.bridge = f ∧ c.stem = e) := by
  have add {a b : E} (d : Bool) (ha : a ∈ es) (hb : b ∈ es)
      (hc : R.Crossing a b d p) :
      (⟨a, b, d⟩ : Event E) ∈ R.events es := by
    apply (R.mem_events es _).mpr
    refine ⟨ha, hb, ?_⟩
    simpa only [PushPuzzle.NCL.Strip.Event.Valid, PushPuzzle.NCL.Strip.Event.site, ← R.crossing_point hc] using hc
  rcases R.route_contact hef hp hq with hc | hc | hc | hc | hc
  · obtain ⟨v, _, _, hc⟩ := hc
    exact False.elim (hv v hc)
  · exact ⟨_, add false he hf hc, R.crossing_point hc, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, add true he hf hc, R.crossing_point hc, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, add false hf he hc, R.crossing_point hc, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨_, add true hf he hc, R.crossing_point hc, Or.inr ⟨rfl, rfl⟩⟩

/-- Actual crossing events are nonrepeating. -/
private theorem events_nodup {es : List E} (h : es.Nodup) : (R.events es).Nodup :=
  (PushPuzzle.NCL.Strip.Event.candidates_nodup h).filter _

/-- The integer sites of all actual crossings are nonrepeating. -/
theorem events_sites_nodup {es : List E} (h : es.Nodup) :
    ((R.events es).map (PushPuzzle.NCL.Strip.Event.site R)).Nodup := by
  apply List.Nodup.map_on _ (R.events_nodup h)
  intro c hc d hd hh
  exact PushPuzzle.NCL.Strip.Event.site_injective R ((R.mem_events es c).mp hc).2.2
    ((R.mem_events es d).mp hd).2.2 hh

end Environment
end PushPuzzle.NCL.Strip
