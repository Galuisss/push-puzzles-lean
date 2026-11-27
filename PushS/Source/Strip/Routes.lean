/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Xuyang Peng
-/

module

public import PushS.Source.Strip.Tracks

/-!
# Continuous geometry of the flat six-point carriers

The flat carriers satisfy the standard simplicity, vertex-avoidance, and strict-transversality
interfaces. Distinct incidences use distinct vertex ports. Equal-height carriers will be
separated by their owner windows in the strip environment.

## Main results

* `PushPuzzle.NCL.Strip.Tracks.route_simple`: continuous simplicity of each actual carrier.
* `PushPuzzle.NCL.Strip.Tracks.center_mem_support_iff`: the carrier avoids every other vertex center.
* `PushPuzzle.NCL.Strip.Tracks.bridge_stem_transverse`: contacts away from centers are strict crossings.
* `PushPuzzle.NCL.Strip.Tracks.route_contact`: classification of contacts between different-height carriers.

## References

The proofs use the six-point decomposition of `Cslib.Orthogonal.Layout`.
-/

public section

namespace PushPuzzle.NCL.Strip.Tracks

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

/-- Each full carrier is simple, including the two consecutive vertical middle-port segments. -/
theorem route_simple {k u v : ℕ} (huv : u ≠ v) (s t : Fin 3) :
    IsSimple (route k u v s t) := by
  have hport : (u, s) ≠ (v, t) := fun h => huv (congrArg Prod.fst h)
  have h01 := fan_stem_endpointContacts k u s
  have h02 := endpointContacts_of_disjoint (fan_bridge_disjoint k u v u s t s)
  have h03 := (endpointContacts_of_disjoint (fan_stem_disjoint (k := k) hport)).reverse_right
  have h04 := (endpointContacts_of_disjoint (fan_disjoint huv s t)).reverse_right
  have h12 := stem_bridge_endpointContacts k u v s t
  have h13 := (endpointContacts_of_disjoint
    (stem_disjoint (k := k) (l := k) hport)).reverse_right
  have h14 := (endpointContacts_of_disjoint
    (fan_stem_disjoint (k := k) hport.symm).symm).reverse_right
  have h23 := (stem_bridge_endpointContacts k v u t s).reverse_right.symm.reverse_right
  have h24 := (endpointContacts_of_disjoint
    (fan_bridge_disjoint k u v v s t t).symm).reverse_right
  have h34 := (fan_stem_endpointContacts k v t).symm.reverse_left.reverse_right
  refine ⟨route_nodup huv s t, ?_⟩
  intro first hf second hg hne
  simp only [route, List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hf hg
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    rcases hg with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hne rfl)
    | exact h01 | exact h01.symm | exact h02 | exact h02.symm
    | exact h03 | exact h03.symm | exact h04 | exact h04.symm
    | exact h12 | exact h12.symm | exact h13 | exact h13.symm
    | exact h14 | exact h14.symm | exact h23 | exact h23.symm
    | exact h24 | exact h24.symm | exact h34 | exact h34.symm

private theorem center_mem_fan {u w : ℕ} {s : Fin 3}
    (h : realPoint (center w) ∈ fan u s) : w = u := by
  have hb := fan_bounds h
  have hx : 8 * (u : ℤ) + 2 ≤ 8 * (w : ℤ) + 4 ∧
      8 * (w : ℤ) + 4 ≤ 8 * (u : ℤ) + 6 := by
    have hx := And.intro hb.1 hb.2.1
    simp only [realPoint, center, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat] at hx
    exact_mod_cast hx
  omega

private theorem center_not_mem_stem (k u w : ℕ) (s : Fin 3) :
    realPoint (center w) ∉ stem k u s := by
  intro hp
  have h := fan_stem_port_eq (s := (1 : Fin 3))
    (show realPoint (center w) ∈ fan w 1 from left_mem_segment ℝ _ _) hp
  obtain ⟨rfl, rfl⟩ := h
  have hy := (mem_stem.mp hp).2
  have ht : ((elbow w 1).2 : ℝ) ≤ rail k := by exact_mod_cast (elbow_below_rail k w 1).le
  rw [Set.uIcc_of_le ht] at hy
  norm_num [elbow, center, realPoint] at hy

private theorem center_not_mem_bridge (k u v w : ℕ) (s t : Fin 3) :
    realPoint (center w) ∉ bridge k u v s t := by
  intro hp
  exact Set.disjoint_left.mp (fan_bridge_disjoint k u v w s t 0)
    (left_mem_segment ℝ _ _) hp

/-- The complete continuous carrier visits precisely its endpoint vertex centers. -/
theorem center_mem_support_iff {k u v w : ℕ} (s t : Fin 3) :
    realPoint (center w) ∈ support (route k u v s t) ↔ w = u ∨ w = v := by
  rw [support_route]
  constructor
  · intro hp
    rcases hp with (((hp | hp) | hp) | hp) | hp
    · exact Or.inl (center_mem_fan hp)
    · exact (center_not_mem_stem k u w s hp).elim
    · exact (center_not_mem_bridge k u v w s t hp).elim
    · exact (center_not_mem_stem k v w t hp).elim
    · exact Or.inr (center_mem_fan hp)
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (left_mem_segment ℝ _ _))))
    · exact Or.inr (left_mem_segment ℝ _ _)

/-- A bridge/stem contact is strictly internal to both segments when their heights differ. -/
theorem bridge_stem_transverse {k l u v w : ℕ} (hkl : k ≠ l)
    {s t q : Fin 3} (hu : (w, q) ≠ (u, s)) (hv : (w, q) ≠ (v, t)) {p : ℝ × ℝ}
    (hp : p ∈ bridge k u v s t) (hq : p ∈ stem l w q) :
    Transverse (column u s, rail k) (column v t, rail k)
      (elbow w q) (column w q, rail l) p := by
  have hb := mem_bridge.1 hp
  have hs := mem_stem.1 hq
  have hcu : column w q ≠ column u s := fun h => hu (Prod.ext
    (Layout.column_injective h).1 (Layout.column_injective h).2)
  have hcv : column w q ≠ column v t := fun h => hv (Prod.ext
    (Layout.column_injective h).1 (Layout.column_injective h).2)
  have hx : min (column u s) (column v t) < column w q ∧
      column w q < max (column u s) (column v t) := by
    have hmem := hb.2
    rw [hs.1, Set.mem_uIcc] at hmem
    norm_cast at hmem
    omega
  have hlow := elbow_below_rail k w q
  have hfhigh := elbow_below_rail l w q
  have hy : (elbow w q).2 < rail k ∧ rail k < rail l := by
    have hmem := hs.2
    rw [Set.uIcc_of_le (show ((elbow w q).2 : ℝ) ≤ rail l by exact_mod_cast hfhigh.le),
      hb.1] at hmem
    have hupper : rail k ≤ rail l := by exact_mod_cast hmem.2
    have hne : rail k ≠ rail l := by
      simp only [rail]
      intro h
      exact hkl (by omega)
    exact ⟨hlow, lt_of_le_of_ne hupper hne⟩
  refine Or.inl ⟨rfl, rfl, Prod.ext hs.1 hb.1, hx.1, hx.2, ?_, ?_⟩
  · change min (elbow w q).2 (rail l) < rail k
    omega
  · change rail k < max (elbow w q).2 (rail l)
    omega

/-- The strict crossing occurs at its explicit integer column/rail pair. -/
theorem bridge_stem_crossing_point {k l u v w : ℕ} {s t q : Fin 3} {p : ℝ × ℝ}
    (h : Transverse (column u s, rail k) (column v t, rail k)
      (elbow w q) (column w q, rail l) p) :
    p = realPoint (column w q, rail k) := by
  rcases h with ⟨_, _, hp, _⟩ | ⟨_, _, _, hlo, hhi, _⟩
  · exact hp
  · simp only [elbow, min_self, max_self] at hlo hhi
    omega

/-- A bridge can cross another carrier's stem only below that carrier's own rail. -/
theorem bridge_stem_track_lt {k l u v w : ℕ} {s t q : Fin 3} {p : ℝ × ℝ}
    (h : Transverse (column u s, rail k) (column v t, rail k)
      (elbow w q) (column w q, rail l) p) : k < l := by
  rcases h with ⟨_, _, _, _, _, _, hhi⟩ | ⟨_, _, _, hlo, hhi, _⟩
  · have helbow := elbow_below_rail l w q
    change rail k < max (elbow w q).2 (rail l) at hhi
    rw [max_eq_right helbow.le] at hhi
    simp only [rail] at hhi
    omega
  · simp only [elbow, min_self, max_self] at hlo hhi
    omega

/-- A strict crossing has a column distinct from both ends of its horizontal bridge. -/
theorem bridge_stem_column_ne {k l u v w : ℕ} {s t q : Fin 3} {p : ℝ × ℝ}
    (h : Transverse (column u s, rail k) (column v t, rail k)
      (elbow w q) (column w q, rail l) p) :
    column w q ≠ column u s ∧ column w q ≠ column v t := by
  rcases h with ⟨_, _, _, hlo, hhi, _⟩ | ⟨_, _, _, hlo, hhi, _⟩
  · constructor <;> intro he <;> omega
  · simp only [elbow, min_self, max_self] at hlo hhi
    omega

private theorem fan_pair_contact {u v : ℕ} {s t : Fin 3} (h : (u, s) ≠ (v, t))
    {p : ℝ × ℝ} (hp : p ∈ fan u s) (hq : p ∈ fan v t) :
    u = v ∧ p = realPoint (center u) := by
  by_cases huv : u = v
  · subst v
    exact ⟨rfl, fan_contact (fun hst => h (Prod.ext rfl hst)) hp hq⟩
  · exact False.elim (Set.disjoint_left.1 (fan_disjoint huv s t) hp hq)

/-- The standard contact classification: a shared vertex or one of four strict bridge/stem
crossings. The incidence inequalities include distinct ports at a shared graph vertex. -/
theorem route_contact {k l u v a b : ℕ} (hkl : k ≠ l)
    {s t q r : Fin 3} (huaq : (u, s) ≠ (a, q)) (hubr : (u, s) ≠ (b, r))
    (hvaq : (v, t) ≠ (a, q)) (hvbr : (v, t) ≠ (b, r)) {p : ℝ × ℝ}
    (hp : p ∈ support (route k u v s t)) (hq : p ∈ support (route l a b q r)) :
    (∃ w, (w = u ∨ w = v) ∧ (w = a ∨ w = b) ∧ p = realPoint (center w)) ∨
    Transverse (column u s, rail k) (column v t, rail k)
      (elbow a q) (column a q, rail l) p ∨
    Transverse (column u s, rail k) (column v t, rail k)
      (elbow b r) (column b r, rail l) p ∨
    Transverse (column a q, rail l) (column b r, rail l)
      (elbow u s) (column u s, rail k) p ∨
    Transverse (column a q, rail l) (column b r, rail l)
      (elbow v t) (column v t, rail k) p := by
  rw [support_route] at hp hq
  simp only [Set.mem_union] at hp hq
  rcases hp with (((hp | hp) | hp) | hp) | hp <;>
    rcases hq with (((hq | hq) | hq) | hq) | hq
  · exact Or.inl ⟨u, Or.inl rfl, Or.inl (fan_pair_contact huaq hp hq).1,
      (fan_pair_contact huaq hp hq).2⟩
  · exact False.elim (huaq (Prod.ext (fan_stem_port_eq hp hq).1 (fan_stem_port_eq hp hq).2))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint _ _ _ _ _ _ _) hp hq)
  · exact False.elim (hubr (Prod.ext (fan_stem_port_eq hp hq).1 (fan_stem_port_eq hp hq).2))
  · exact Or.inl ⟨u, Or.inl rfl, Or.inr (fan_pair_contact hubr hp hq).1,
      (fan_pair_contact hubr hp hq).2⟩
  · exact False.elim (huaq.symm
      (Prod.ext (fan_stem_port_eq hq hp).1 (fan_stem_port_eq hq hp).2))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint huaq) hp hq)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (bridge_stem_transverse hkl.symm huaq hubr hq hp))))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint hubr) hp hq)
  · exact False.elim (hubr.symm
      (Prod.ext (fan_stem_port_eq hq hp).1 (fan_stem_port_eq hq hp).2))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint _ _ _ _ _ _ _) hq hp)
  · exact Or.inr (Or.inl (bridge_stem_transverse hkl huaq.symm hvaq.symm hp hq))
  · exact False.elim (Set.disjoint_left.1 (bridge_disjoint hkl _ _ _ _) hp hq)
  · exact Or.inr (Or.inr (Or.inl (bridge_stem_transverse hkl hubr.symm hvbr.symm hp hq)))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint _ _ _ _ _ _ _) hq hp)
  · exact False.elim (hvaq.symm
      (Prod.ext (fan_stem_port_eq hq hp).1 (fan_stem_port_eq hq hp).2))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint hvaq) hp hq)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (bridge_stem_transverse hkl.symm hvaq hvbr hq hp))))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint hvbr) hp hq)
  · exact False.elim (hvbr.symm
      (Prod.ext (fan_stem_port_eq hq hp).1 (fan_stem_port_eq hq hp).2))
  · exact Or.inl ⟨v, Or.inr rfl, Or.inl (fan_pair_contact hvaq hp hq).1,
      (fan_pair_contact hvaq hp hq).2⟩
  · exact False.elim (hvaq (Prod.ext (fan_stem_port_eq hp hq).1 (fan_stem_port_eq hp hq).2))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint _ _ _ _ _ _ _) hp hq)
  · exact False.elim (hvbr (Prod.ext (fan_stem_port_eq hp hq).1 (fan_stem_port_eq hp hq).2))
  · exact Or.inl ⟨v, Or.inr rfl, Or.inr (fan_pair_contact hvbr hp hq).1,
      (fan_pair_contact hvbr hp hq).2⟩

end PushPuzzle.NCL.Strip.Tracks
