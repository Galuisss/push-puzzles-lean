/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Slices
public import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-!
# Actual local carrier neighborhoods

The strict bridge/stem crossings retain horizontal and vertical three-point neighborhoods in the
actual unit subdivisions. Their four unit-arc labels are selected from the original carrier data.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.crossing_straight`: both original carriers pass straight through their crossing.
* `PushPuzzle.NCL.Strip.Sweep.crossing_slice`: the actual local edit exchanges the two original edge labels.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

private theorem triple_pairs {r : Route} {a p b : Point} (ht : [a, p, b] <:+: r) :
    (a, p) ∈ r.consecutivePairs ∧ (p, b) ∈ r.consecutivePairs := by
  obtain ⟨s, t, rfl⟩ := ht
  constructor
  · have h := List.getElem_mem_consecutivePairs (s ++ [a, p, b] ++ t) s.length (by simp)
    simpa using h
  · have h := List.getElem_mem_consecutivePairs (s ++ [a, p, b] ++ t) (s.length + 1)
      (by simp; omega)
    simpa [Nat.add_assoc] using h

private theorem straight_pairs {r : Route} {p d : Point} (ht : StraightThrough r p d) :
    ((p - d, p) ∈ r.consecutivePairs ∨ (p, p - d) ∈ r.consecutivePairs) ∧
      ((p, p + d) ∈ r.consecutivePairs ∨ (p + d, p) ∈ r.consecutivePairs) := by
  rcases ht with ht | ht
  · have h := triple_pairs ht
    exact ⟨Or.inl h.1, Or.inl h.2⟩
  · have h := triple_pairs ht
    exact ⟨Or.inr h.2, Or.inr h.1⟩

private theorem exists_arc (e : E) {p q : Point}
    (hpq : p.1 ≤ q.1 ∧ p.2 ≤ q.2)
    (hm : (p, q) ∈ (R.unitRoute e).consecutivePairs ∨
      (q, p) ∈ (R.unitRoute e).consecutivePairs) :
    ∃ a : Arc R, a.edge = e ∧ a.lower R = p ∧ a.upper R = q := by
  rcases hm with hm | hm
  all_goals obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  all_goals refine ⟨⟨e, i⟩, rfl, ?_, ?_⟩
  all_goals simp only [PushPuzzle.NCL.Strip.Sweep.Arc.lower, PushPuzzle.NCL.Strip.Sweep.Arc.upper, PushPuzzle.NCL.Strip.Sweep.Arc.pair, hi, Prod.ext_iff]
  all_goals omega

/-- A horizontal three-point neighborhood provides the actual left and right arc labels. -/
theorem horizontal_arcs (e : E) (p : Point) (ht : StraightThrough (R.unitRoute e) p (1, 0)) :
    (∃ a : Arc R, a.edge = e ∧ a.lower R = (p.1 - 1, p.2) ∧ a.upper R = p) ∧
      ∃ a : Arc R, a.edge = e ∧ a.lower R = p ∧ a.upper R = (p.1 + 1, p.2) := by
  have h := straight_pairs ht
  have hm : p - (1, 0) = (p.1 - 1, p.2) := Prod.ext rfl (sub_zero _)
  have hp : p + (1, 0) = (p.1 + 1, p.2) := Prod.ext rfl (add_zero _)
  rw [hm, hp] at h
  exact ⟨exists_arc R e (by simp) h.1, exists_arc R e (by simp) h.2⟩

/-- A vertical three-point neighborhood provides the actual bottom and top arc labels. -/
theorem vertical_arcs (e : E) (p : Point) (ht : StraightThrough (R.unitRoute e) p (0, 1)) :
    (∃ a : Arc R, a.edge = e ∧ a.lower R = (p.1, p.2 - 1) ∧ a.upper R = p) ∧
      ∃ a : Arc R, a.edge = e ∧ a.lower R = p ∧ a.upper R = (p.1, p.2 + 1) := by
  have h := straight_pairs ht
  have hm : p - (0, 1) = (p.1, p.2 - 1) := Prod.ext (sub_zero _) rfl
  have hp : p + (0, 1) = (p.1, p.2 + 1) := Prod.ext (add_zero _) rfl
  rw [hm, hp] at h
  exact ⟨exists_arc R e (by simp) h.1, exists_arc R e (by simp) h.2⟩

/-- The two original carriers have their exact straight neighborhoods at every actual crossing. -/
theorem crossing_straight {c : Event E} (hc : c.Valid R) :
    StraightThrough (R.unitRoute c.bridge) (c.site R) (1, 0) ∧
      StraightThrough (R.unitRoute c.stem) (c.site R) (0, 1) := by
  have ht := (PushPuzzle.NCL.Strip.Event.test_iff R c).mpr hc
  simp only [PushPuzzle.NCL.Strip.Event.test, decide_eq_true_eq] at ht
  constructor
  · apply subdivide_horizontal (R.route_orthogonal c.bridge)
      (a := (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.bridge false))
          (R.port c.bridge false), PushPuzzle.NCL.Strip.Tracks.rail (R.track c.bridge)))
      (b := (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.bridge true))
          (R.port c.bridge true), PushPuzzle.NCL.Strip.Tracks.rail (R.track c.bridge)))
    · simp [PushPuzzle.NCL.Strip.Environment.route, PushPuzzle.NCL.Strip.Tracks.route, List.consecutivePairs]
    · rfl
    · rfl
    · exact ⟨ht.1, ht.2.1⟩
  · have hlo := PushPuzzle.NCL.Strip.Tracks.elbow_below_rail (R.track c.bridge)
      (R.vertices.address (R.endpoint c.stem c.dir)) (R.port c.stem c.dir)
    have hhi : PushPuzzle.NCL.Strip.Tracks.rail (R.track c.bridge) < PushPuzzle.NCL.Strip.Tracks.rail (R.track c.stem) := by
      simp only [PushPuzzle.NCL.Strip.Tracks.rail]
      omega
    have he : (PushPuzzle.NCL.Strip.Tracks.elbow (R.vertices.address (R.endpoint c.stem c.dir))
        (R.port c.stem c.dir)).2 < PushPuzzle.NCL.Strip.Tracks.rail (R.track c.stem) := hlo.trans hhi
    cases hd : c.dir
    · apply subdivide_vertical (R.route_orthogonal c.stem)
        (a := PushPuzzle.NCL.Strip.Tracks.elbow (R.vertices.address (R.endpoint c.stem false)) (R.port c.stem false))
        (b := (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.stem false)) (R.port c.stem false),
            PushPuzzle.NCL.Strip.Tracks.rail (R.track c.stem)))
      · simp [PushPuzzle.NCL.Strip.Environment.route, PushPuzzle.NCL.Strip.Tracks.route, List.consecutivePairs]
      · rfl
      · simp only [PushPuzzle.NCL.Strip.Event.site, PushPuzzle.NCL.Strip.Environment.crossingSite, hd, PushPuzzle.NCL.Strip.Tracks.elbow]
      · simp only [hd] at hlo he
        simpa only [PushPuzzle.NCL.Strip.Event.site, PushPuzzle.NCL.Strip.Environment.crossingSite, hd, min_eq_left he.le,
          max_eq_right he.le] using And.intro hlo hhi
    · apply subdivide_vertical (R.route_orthogonal c.stem)
        (a := (PushPuzzle.NCL.Strip.Tracks.column (R.vertices.address (R.endpoint c.stem true)) (R.port c.stem true),
            PushPuzzle.NCL.Strip.Tracks.rail (R.track c.stem)))
        (b := PushPuzzle.NCL.Strip.Tracks.elbow (R.vertices.address (R.endpoint c.stem true)) (R.port c.stem true))
      · simp [PushPuzzle.NCL.Strip.Environment.route, PushPuzzle.NCL.Strip.Tracks.route, List.consecutivePairs]
      · rfl
      · simp only [PushPuzzle.NCL.Strip.Event.site, PushPuzzle.NCL.Strip.Environment.crossingSite, hd]
      · simp only [hd] at hlo he
        simpa only [PushPuzzle.NCL.Strip.Event.site, PushPuzzle.NCL.Strip.Environment.crossingSite, hd, min_eq_right he.le,
          max_eq_left he.le] using And.intro hlo hhi

/-- At an actual crossing, the original edge labels exchange their geometric frontier order. -/
theorem crossing_slice {es : List E} (hes : es.Nodup) {c : Event E}
    (hc : c ∈ R.events es) :
    ((slice R es (c.site R)).incoming.map PushPuzzle.NCL.Strip.Sweep.Arc.edge = [c.bridge, c.stem]) ∧
      ((slice R es (c.site R)).outgoing.map PushPuzzle.NCL.Strip.Sweep.Arc.edge = [c.stem, c.bridge]) := by
  obtain ⟨heb, hes', hc'⟩ := (R.mem_events es c).mp hc
  have hn := crossing_straight R hc'
  obtain ⟨⟨l, hle, hll, hlu⟩, r, hre, hrl, hru⟩ := horizontal_arcs R _ _ hn.1
  obtain ⟨⟨b, hbe, hbl, hbu⟩, t, hte, htl, htu⟩ := vertical_arcs R _ _ hn.2
  have hlm : l ∈ (slice R es (c.site R)).incoming :=
    (mem_slice_incoming R es _ l).mpr ⟨hle ▸ heb, hlu⟩
  have hbm : b ∈ (slice R es (c.site R)).incoming :=
    (mem_slice_incoming R es _ b).mpr ⟨hbe ▸ hes', hbu⟩
  have htm : t ∈ (slice R es (c.site R)).outgoing :=
    (mem_slice_outgoing R es _ t).mpr ⟨hte ▸ hes', htl⟩
  have hrm : r ∈ (slice R es (c.site R)).outgoing :=
    (mem_slice_outgoing R es _ r).mpr ⟨hre ▸ heb, hrl⟩
  have hli : (slice R es (c.site R)).incoming = [l, b] := by
    apply incoming_eq_pair R hes hlm hbm
    simp only [PushPuzzle.NCL.Strip.Sweep.Arc.position, hll, hlu, hbl, hbu]
    split_ifs <;> omega
  have hlo : (slice R es (c.site R)).outgoing = [t, r] := by
    apply outgoing_eq_pair R hes htm hrm
    simp only [PushPuzzle.NCL.Strip.Sweep.Arc.position, htl, htu, hrl, hru]
    split_ifs <;> omega
  simp only [hli, hlo, List.map_cons, List.map_nil, hle, hbe, hte, hre, and_self]

end PushPuzzle.NCL.Strip.Sweep
