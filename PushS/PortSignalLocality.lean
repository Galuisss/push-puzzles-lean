/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCoreCrossing
public import Mathlib.Data.Nat.Dist
import all PushS.PortCoreCrossing
import all PushS.PortEndpointEnumeration
import all PushS.PortEndpointSeparation
import all PushS.PortSegments

/-! Actual signal locality and the remote wide separators. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe PageLevels

private theorem center_of_gate (l : PortLayout) {kind : Shuttle.Kind} {first : ℕ}
    (hg : .gate kind first ∈ l.lowerGroups) : first + 1 ∈ centers l := by
  apply List.mem_filterMap.mpr
  refine ⟨.gate kind first, hg, ?_⟩
  simp [encLowerGroup_elim, encLowerGroup_toSum]

private theorem endpoint_in_pageColumns (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = side) :
    p.x e.port ∈ pageColumns l (coordinates p) side := by
  simp only [pageColumns, List.mem_append, or_assoc]
  right
  left
  apply List.mem_flatMap.mpr
  refine ⟨e, List.mem_filter.mpr ⟨he, by simp [hs]⟩, ?_⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

private theorem axis_in_pageColumns (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {k : ℕ} (hk : k < l.portCount) : p.x k ∈ pageColumns l (coordinates p) side := by
  cases side with
  | upper =>
    obtain ⟨e, he, hs, hp⟩ := l.endpoints_upper_exists hl hk
    rw [← hp]
    exact endpoint_in_pageColumns l p .upper he hs
  | lower =>
    rcases l.endpoints_lower_or_gate hl hk with he | ⟨kind, first, hg, rfl⟩
    · obtain ⟨e, he, hs, hp⟩ := he
      rw [← hp]
      exact endpoint_in_pageColumns l p .lower he hs
    · simp only [pageColumns, List.mem_append, or_assoc]
      right
      right
      simp only [ite_true]
      apply List.mem_flatMap.mpr
      exact ⟨first + 1, center_of_gate l hg, List.mem_cons_self⟩

private theorem gate_middle_lt (l : PortLayout) (hl : l.pages.Valid)
    {kind : Shuttle.Kind} {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups) : first + 1 < l.portCount := by
  have hm : Group.triple first ∈ l.pages.lowerPage.groups :=
    List.mem_map.mpr ⟨.gate kind first, hg, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  have hb := hl.lower.bounded i
  change l.pages.lowerPage.group i = .triple first at hi
  simp only [hi, PageLevels.Group.left, PageLevels.Group.right] at hb
  have hb' : first + 2 < l.portCount := hb.2
  omega

/-- Every actual signal hole is within twelve horizontal cells of an actual port axis. -/
theorem signalSegments_near_axis (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {q : ℕ × ℕ} (hq : q ∈ pointHoles (l.signalSegments p state)) :
    ∃ i < l.portCount, Nat.dist q.1 (p.x i) ≤ 12 := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    have hb := signal_span p state e ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)
    refine ⟨e.port, l.endpoints_port_lt hl he, ?_⟩
    simp only [Nat.dist_eq_max_sub_min]
    omega
  · obtain ⟨g, hg, hs⟩ := List.mem_flatMap.mp hs
    cases hgate : g.gate with
    | none => simp [tripleSignal, hgate] at hs
    | some kind =>
      have hraw := placement_gate_mem l hg hgate
      have hb := gate_signal_span p state kind g.left g.internal
        ((mem_pointHoles _ q).mpr ⟨s, by simpa [tripleSignal, hgate] using hs, hq⟩)
      refine ⟨g.left + 1, gate_middle_lt l hl hraw, ?_⟩
      simp only [Nat.dist_eq_max_sub_min]
      omega

private theorem adjacentPair_gap {xs : List ℕ} {a b : ℕ} (hab : (a, b) ∈ adjacentPairs xs) :
    a < b ∧ ∀ x ∈ xs, ¬(a < x ∧ x < b) := by
  obtain ⟨x, hx, hab⟩ := List.mem_flatMap.mp hab
  obtain ⟨y, hy, hab⟩ := List.mem_filterMap.mp hab
  split at hab
  · rename_i hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩
    refine ⟨hcond.1, ?_⟩
    intro z hz hmid
    have ht : xs.any (fun c => decide (x < c ∧ c < y)) = true :=
      List.any_eq_true.mpr ⟨z, hz, by simp [hmid]⟩
    have hc := hcond.2
    rw [ht] at hc
    cases hc
  · cases hab

private theorem wide_midpoint_far (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {a b : ℕ} (hab : (a, b) ∈ adjacentPairs (pageColumns l (coordinates p) side))
    (hgap : readLength p p.levels < b - a) {k : ℕ} (hk : k < l.portCount) :
    14 < Nat.dist ((a + b) / 2) (p.x k) := by
  have hp := adjacentPair_gap hab
  have hno := hp.2 _ (axis_in_pageColumns l p hl side hk)
  have hL := readLength_ge p p.levels_pos (le_refl p.levels)
  simp only [Nat.dist_eq_max_sub_min]
  omega

private theorem wideFixed_disjoint_signals (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) (side : Side) :
    Disjoint (pointHoles (wideFixed l (coordinates p) side))
      (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  obtain ⟨k, hk, hdist⟩ := l.signalSegments_near_axis p hl state hsignal
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
  dsimp only [wideFixed] at hs
  obtain ⟨⟨a, b⟩, hab, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  · rename_i hgap
    obtain ⟨y, _, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      have hp := point_coordinates hq
      have hfar := wide_midpoint_far l p hl side hab hgap hk
      rw [← hp.1] at hfar
      omega
  · cases hs

end PushPuzzle.PushS.PortLayout
