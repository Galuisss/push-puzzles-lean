/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Events
public import PushS.Source.Strip.UnitRoute

/-!
# Crossing events in actual carrier traversal order

Scan the complete unit route of an original edge and look up the crossing at each visited
integer site. Geometric site uniqueness makes the lookup exact. Thus the resulting site list
is a sublist of the actual traversal, and each participating crossing occurs exactly once.

## Main definitions

* `PushPuzzle.NCL.Strip.Environment.eventAt`: lookup of the actual event at an integer site.
* `PushPuzzle.NCL.Strip.Environment.carrierEvents`: events in order along one original carrier.

## Main results

* `PushPuzzle.NCL.Strip.Environment.mem_carrierEvents`: exactly the two participating edges list each event.
* `PushPuzzle.NCL.Strip.Environment.carrierEvents_sites_sublist`: the actual geometric traversal order.
* `PushPuzzle.NCL.Strip.Environment.carrierEvents_length_le`: a fixed capacity-dependent event budget per edge.
-/

public section

namespace PushPuzzle.NCL.Strip.Environment

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

open scoped List

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Find the event whose unique crossing site equals the queried integer point. -/
@[expose] def eventAt (es : List E) (p : Point) : Option (Event E) :=
  (R.events es).find? (fun c => decide (c.site R = p))

/-- Lookup returns exactly the declared event at the specified integer site. -/
theorem eventAt_eq_some (es : List E) (p : Point) (c : Event E) :
    R.eventAt es p = some c ↔ c ∈ R.events es ∧ c.site R = p := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h,
      of_decide_eq_true (List.find?_some (p := fun c : Event E => decide (c.site R = p)) h)⟩
  · rintro ⟨hc, hp⟩
    have hh : (R.eventAt es p).isSome :=
      List.find?_isSome.mpr ⟨c, hc, by simp only [hp, decide_true]⟩
    cases h : R.eventAt es p with
    | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at hh
    | some d =>
      have hd := List.mem_of_find?_eq_some h
      have hs := of_decide_eq_true
        (List.find?_some (p := fun c : Event E => decide (c.site R = p)) h)
      have hdc := PushPuzzle.NCL.Strip.Event.site_injective R ((R.mem_events es d).mp hd).2.2
        ((R.mem_events es c).mp hc).2.2 (hs.trans hp.symm)
      simp only [hdc]

/-- Scan the actual unit grid path, retaining each crossing event encountered along it. -/
@[expose] def carrierEvents (es : List E) (e : E) : List (Event E) :=
  (R.unitRoute e).filterMap (R.eventAt es)

/-- Exactly the two participating original carriers contain an actual crossing site. -/
theorem site_mem_unitRoute {c : Event E} (hc : c.Valid R) (e : E) :
    c.site R ∈ R.unitRoute e ↔ e = c.bridge ∨ e = c.stem := by
  rw [R.mem_unitRoute]
  constructor
  · exact R.crossing_routes_eq hc
  · rintro (rfl | rfl)
    · exact R.bridge_mem_support _ (PushPuzzle.Orthogonal.Transverse.mem hc).1
    · exact R.stem_mem_support _ _ (PushPuzzle.Orthogonal.Transverse.mem hc).2

/-- A carrier lists precisely the actual events in which it participates. -/
theorem mem_carrierEvents (es : List E) (e : E) (c : Event E) :
    c ∈ R.carrierEvents es e ↔ c ∈ R.events es ∧ (e = c.bridge ∨ e = c.stem) := by
  simp only [carrierEvents, List.mem_filterMap, R.eventAt_eq_some]
  constructor
  · rintro ⟨p, hp, hc, hsite⟩
    refine ⟨hc, ?_⟩
    exact (R.site_mem_unitRoute ((R.mem_events es c).mp hc).2.2 e).mp (hsite ▸ hp)
  · rintro ⟨hc, he⟩
    exact ⟨c.site R, (R.site_mem_unitRoute ((R.mem_events es c).mp hc).2.2 e).mpr he, hc, rfl⟩

private theorem map_sites_lookup (es : List E) (ps : List Point) :
    ((ps.filterMap (R.eventAt es)).map (PushPuzzle.NCL.Strip.Event.site R)) =
      ps.filter (fun p => (R.eventAt es p).isSome) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases h : R.eventAt es p with
    | none => simp [h, ih]
    | some c =>
      have hc := ((R.eventAt_eq_some es p c).mp h).2
      simp [h, ih, hc]

/-- The crossing sites occur as an actual sublist of the original unit traversal. -/
theorem carrierEvents_sites_sublist (es : List E) (e : E) :
    ((R.carrierEvents es e).map (PushPuzzle.NCL.Strip.Event.site R)) <+ R.unitRoute e := by
  rw [carrierEvents, R.map_sites_lookup]
  exact List.filter_sublist

/-- The ordered event list has a capacity-dependent bound independent of the source length. -/
theorem carrierEvents_length_le (es : List E) (e : E) :
    (R.carrierEvents es e).length ≤ routeBudget A K + 1 := by
  have h := (R.carrierEvents_sites_sublist es e).length_le
  rw [List.length_map] at h
  exact h.trans (R.unitRoute_length_le e)

end PushPuzzle.NCL.Strip.Environment
