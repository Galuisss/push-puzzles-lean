/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Xuyang Peng
-/

module

public import PushS.Source.Init
public import CslibFrontier.Foundations.Geometry.Orthogonal.Layout
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Flat vertex boxes and a fixed family of tracks

The three ports of address `v` leave a center on the common baseline four. A track of index
`k` lies at height `10 + 2k`. The six listed points give an actual orthogonal route in either
horizontal direction. Addresses will be assigned by panel and tracks by owner parity.

## Main definitions

* `PushPuzzle.NCL.Strip.Tracks.center`, `PushPuzzle.NCL.Strip.Tracks.column`: centers and three distinct port columns.
* `PushPuzzle.NCL.Strip.Tracks.route`: the six-point carrier on an indexed horizontal track.

## Main results

* `PushPuzzle.NCL.Strip.Tracks.support_route`: the whole continuous support splits into five segments.
* `PushPuzzle.NCL.Strip.Tracks.route_orthogonal`: distinct source addresses give proper orthogonal routes.
* `PushPuzzle.NCL.Strip.Tracks.support_bounds`: listed-point rectangles contain the full real support.

## References

This is the flat-box version of `Cslib.Orthogonal.Layout`'s six-point construction.
-/

public section

namespace PushPuzzle.NCL.Strip.Tracks

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

/-- A vertex center on the common baseline. -/
@[expose] def center (v : ℕ) : Point := (8 * (v : ℤ) + 4, 4)

/-- The three port columns of a vertex box. -/
abbrev column := Cslib.Orthogonal.Layout.column

/-- The first bend, two units left, up, or right of the center. -/
@[expose] def elbow (v : ℕ) (s : Fin 3) : Point :=
  (column v s, 4 + if s = 1 then 2 else 0)

/-- The height of a horizontal rail, above all local vertex fans. -/
@[expose] def rail (k : ℕ) : ℤ := 10 + 2 * (k : ℤ)

/-- The six-point carrier from one vertex port to another. -/
@[expose] def route (k u v : ℕ) (s t : Fin 3) : Route :=
  [center u, elbow u s, (column u s, rail k),
    (column v t, rail k), elbow v t, center v]

/-- The first segment inside one vertex box. -/
@[expose] def fan (v : ℕ) (s : Fin 3) : Set (ℝ × ℝ) := segment (center v) (elbow v s)

/-- The vertical segment between a port's elbow and its rail. -/
@[expose] def stem (k v : ℕ) (s : Fin 3) : Set (ℝ × ℝ) :=
  segment (elbow v s) (column v s, rail k)

/-- The horizontal part of the carrier. -/
@[expose] def bridge (k u v : ℕ) (s t : Fin 3) : Set (ℝ × ℝ) :=
  segment (column u s, rail k) (column v t, rail k)

/-- The complete real support consists of the two fans, two stems, and the bridge. -/
theorem support_route (k u v : ℕ) (s t : Fin 3) :
    support (route k u v s t) =
      fan u s ∪ stem k u s ∪ bridge k u v s t ∪ stem k v t ∪ fan v t := by
  simp only [route, support_cons_cons]
  have hstem : segment (column v t, rail k) (elbow v t) = stem k v t :=
    segment_symm ℝ _ _
  have hfan : segment (elbow v t) (center v) = fan v t := segment_symm ℝ _ _
  rw [hstem, hfan]
  have hsingle : support [center v] = {realPoint (center v)} := by
    ext p
    simp [support, List.consecutivePairs]
  rw [hsingle]
  ext p
  have hc : realPoint (center v) ∈ fan v t := left_mem_segment ℝ _ _
  simp only [fan, stem, bridge, Set.mem_union, Set.mem_singleton_iff] at *
  aesop

/-- A stem is exactly its fixed column and its vertical interval. -/
theorem mem_stem {k v : ℕ} {s : Fin 3} {p : ℝ × ℝ} :
    p ∈ stem k v s ↔ p.1 = (column v s : ℝ) ∧
      p.2 ∈ Set.uIcc ((elbow v s).2 : ℝ) (rail k : ℝ) := mem_vertical

/-- A bridge is exactly its fixed row and its horizontal interval. -/
theorem mem_bridge {k u v : ℕ} {s t : Fin 3} {p : ℝ × ℝ} :
    p ∈ bridge k u v s t ↔ p.2 = (rail k : ℝ) ∧
      p.1 ∈ Set.uIcc (column u s : ℝ) (column v t : ℝ) := mem_horizontal

/-- The rail is strictly above every local elbow. -/
theorem elbow_below_rail (k v : ℕ) (s : Fin 3) : (elbow v s).2 < rail k := by
  simp only [elbow, rail]
  split_ifs <;> omega

/-- The local port segment is proper and axis aligned. -/
private theorem center_elbow_axisAligned (v : ℕ) (s : Fin 3) : AxisAligned (center v)
    (elbow v s) := by
  fin_cases s <;> norm_num only [AxisAligned, center, elbow, column, Layout.column,
    ne_eq, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two,
    ↓reduceIte, Prod.fst, Prod.snd] <;> simp only [and_true, true_and, and_false,
      or_true, or_false, not_false_eq_true] <;> omega

/-- The carrier has exactly five proper axis-aligned segments. -/
theorem route_orthogonal {k u v : ℕ} (huv : u ≠ v) (s t : Fin 3) :
    IsOrthogonal (route k u v s t) := by
  have hus := center_elbow_axisAligned u s
  have hvt := center_elbow_axisAligned v t
  have hut := elbow_below_rail k u s
  have hvt' := elbow_below_rail k v t
  intro a ha
  simp only [route, List.consecutivePairs, List.tail_cons, List.zip_cons_cons,
    List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact hus
  · exact ⟨Or.inl rfl, fun h => (ne_of_lt hut) (congrArg Prod.snd h)⟩
  · exact ⟨Or.inr rfl, fun h => huv (Layout.column_injective (congrArg Prod.fst h)).1⟩
  · exact ⟨Or.inl rfl, fun h => (ne_of_gt hvt') (congrArg Prod.snd h)⟩
  · exact ⟨hvt.1.imp Eq.symm Eq.symm, hvt.2.symm⟩

/-- The carrier starts at its declared source center. -/
@[simp] theorem route_head (k u v : ℕ) (s t : Fin 3) :
    (route k u v s t).head? = some (center u) := rfl

/-- The carrier ends at its declared target center. -/
@[simp] theorem route_last (k u v : ℕ) (s t : Fin 3) :
    (route k u v s t).getLast? = some (center v) := rfl

/-- The carrier contains exactly five segments. -/
@[simp] theorem route_segments_length (k u v : ℕ) (s t : Fin 3) :
    (route k u v s t).consecutivePairs.length = 5 := rfl

/-- Bounds for all six listed points, with a fixed track budget and address interval. -/
theorem point_bounds {K k u v : ℕ} (hk : k < K) {lo hi : ℤ}
    (hu : lo ≤ 8 * (u : ℤ) + 2 ∧ 8 * (u : ℤ) + 6 ≤ hi)
    (hv : lo ≤ 8 * (v : ℤ) + 2 ∧ 8 * (v : ℤ) + 6 ≤ hi)
    (s t : Fin 3) {p : Point} (hp : p ∈ route k u v s t) :
    lo ≤ p.1 ∧ p.1 ≤ hi ∧ 4 ≤ p.2 ∧ p.2 ≤ 2 * (K : ℤ) + 8 := by
  have hs := s.isLt
  have ht := t.isLt
  simp only [route, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [center, elbow, column, Layout.column, rail] <;> (try split_ifs) <;> omega

/-- The entire continuous support stays in the same rectangle as the listed points. -/
theorem support_bounds {K k u v : ℕ} (hk : k < K) {lo hi : ℤ}
    (hu : lo ≤ 8 * (u : ℤ) + 2 ∧ 8 * (u : ℤ) + 6 ≤ hi)
    (hv : lo ≤ 8 * (v : ℤ) + 2 ∧ 8 * (v : ℤ) + 6 ≤ hi)
    (s t : Fin 3) {p : ℝ × ℝ} (hp : p ∈ support (route k u v s t)) :
    (lo : ℝ) ≤ p.1 ∧ p.1 ≤ hi ∧ 4 ≤ p.2 ∧ p.2 ≤ 2 * (K : ℝ) + 8 := by
  have h := support_bounds_of_points (fun q hq => point_bounds hk hu hv s t hq) hp
  simpa only [Int.cast_ofNat, Int.cast_add, Int.cast_mul, Int.cast_natCast] using h

/-- The three local fans have explicit horizontal or vertical interval supports. -/
private theorem mem_fan {v : ℕ} {s : Fin 3} {p : ℝ × ℝ} :
    p ∈ fan v s ↔
      (s = 0 ∧ p.2 = 4 ∧ 8 * (v : ℝ) + 2 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 4) ∨
      (s = 1 ∧ p.1 = 8 * (v : ℝ) + 4 ∧ 4 ≤ p.2 ∧ p.2 ≤ 6) ∨
      (s = 2 ∧ p.2 = 4 ∧ 8 * (v : ℝ) + 4 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 6) := by
  fin_cases s <;> norm_num only [fan, Cslib.Orthogonal.segment, realPoint, center, elbow, column,
    Layout.column,
    Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
    and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals ring_nf
  all_goals first | rw [mem_horizontal] | rw [mem_vertical]
  all_goals simp only [Set.mem_uIcc]
  all_goals constructor
  all_goals first
    | rintro ⟨h, h' | h'⟩ <;> exact ⟨h, by constructor <;> linarith⟩
    | rintro ⟨h, h'⟩; first | exact ⟨h, Or.inl h'⟩ | exact ⟨h, Or.inr h'⟩

/-- A fan stays in its box, between heights four and six. -/
theorem fan_bounds {v : ℕ} {s : Fin 3} {p : ℝ × ℝ} (hp : p ∈ fan v s) :
    8 * (v : ℝ) + 2 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 6 ∧ 4 ≤ p.2 ∧ p.2 ≤ 6 := by
  rw [mem_fan] at hp
  rcases hp with ⟨_, hy, hx⟩ | ⟨_, hx, hy⟩ | ⟨_, hy, hx⟩ <;>
    constructor <;> (try constructor) <;> (try constructor) <;> linarith

/-- Fans in different vertex boxes are disjoint. -/
theorem fan_disjoint {u v : ℕ} (huv : u ≠ v) (s t : Fin 3) :
    Disjoint (fan u s) (fan v t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := fan_bounds hp
  have hq' := fan_bounds hq
  rcases lt_or_gt_of_ne huv with h | h
  · have h' : (u : ℝ) + 1 ≤ v := by exact_mod_cast h
    linarith
  · have h' : (v : ℝ) + 1 ≤ u := by exact_mod_cast h
    linarith

/-- Different fans in one vertex box meet only at their common center. -/
theorem fan_contact {v : ℕ} {s t : Fin 3} (hst : s ≠ t) {p : ℝ × ℝ}
    (hs : p ∈ fan v s) (ht : p ∈ fan v t) : p = realPoint (center v) := by
  rw [mem_fan] at hs ht
  rcases hs with ⟨hs, hy, hx⟩ | ⟨hs, hx, hy⟩ | ⟨hs, hy, hx⟩ <;>
    rcases ht with ⟨ht, hy', hx'⟩ | ⟨ht, hx', hy'⟩ | ⟨ht, hy', hx'⟩ <;>
    subst s <;> subst t <;> try contradiction
  all_goals apply Prod.ext <;> simp only [realPoint, center, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, Int.cast_ofNat] <;> linarith

/-- A fan can meet a stem only at the same vertex and the same port. -/
theorem fan_stem_port_eq {k u v : ℕ} {s t : Fin 3} {p : ℝ × ℝ}
    (hp : p ∈ fan u s) (hq : p ∈ stem k v t) : u = v ∧ s = t := by
  have hb := fan_bounds hp
  have hcol := (mem_stem.1 hq).1
  have ht : (t : ℝ) ≤ 2 := by exact_mod_cast (show (t : ℕ) ≤ 2 by omega)
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have huv : u = v := by
    by_contra h
    simp only [column, Layout.column] at hcol
    push_cast at hcol
    rcases lt_or_gt_of_ne h with h | h
    · have h' : (u : ℝ) + 1 ≤ v := by exact_mod_cast h
      linarith
    · have h' : (v : ℝ) + 1 ≤ u := by exact_mod_cast h
      linarith
  subst v
  refine ⟨rfl, ?_⟩
  have hhigh : ((elbow u t).2 : ℝ) < rail k := by exact_mod_cast elbow_below_rail k u t
  rw [mem_stem, Set.uIcc_of_le hhigh.le] at hq
  rw [mem_fan] at hp
  rcases hp with ⟨rfl, hy, hx⟩ | ⟨rfl, hx, hy⟩ | ⟨rfl, hy, hx⟩ <;>
    fin_cases t <;> norm_num only [column, Layout.column, elbow, Fin.ext_iff, Fin.val_mk,
      Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Set.mem_Icc] at hq ⊢ <;>
    linarith

/-- Different port columns give disjoint stems, independently of their heights. -/
theorem stem_disjoint {k l u v : ℕ} {s t : Fin 3} (h : (u, s) ≠ (v, t)) :
    Disjoint (stem k u s) (stem l v t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hx := (mem_stem.1 hp).1.symm.trans (mem_stem.1 hq).1
  have hcol : column u s = column v t := by exact_mod_cast hx
  obtain ⟨rfl, rfl⟩ := Layout.column_injective hcol
  exact h rfl

/-- Every fan lies strictly below every bridge. -/
theorem fan_bridge_disjoint (k u v w : ℕ) (s t q : Fin 3) :
    Disjoint (fan w q) (bridge k u v s t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hb := fan_bounds hp
  have hy := (mem_bridge.1 hq).1
  simp only [rail, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at hy
  have hk : (0 : ℝ) ≤ k := by positivity
  linarith

/-- Bridges at different heights are disjoint. -/
theorem bridge_disjoint {k l u v a b : ℕ} (hkl : k ≠ l) (s t q r : Fin 3) :
    Disjoint (bridge k u v s t) (bridge l a b q r) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hy := (mem_bridge.1 hp).1.symm.trans (mem_bridge.1 hq).1
  have hrail : rail k = rail l := by exact_mod_cast hy
  simp only [rail] at hrail
  exact hkl (by omega)

/-- Fans and stems belonging to distinct ports are disjoint. -/
theorem fan_stem_disjoint {k u v : ℕ} {s t : Fin 3}
    (h : (u, s) ≠ (v, t)) : Disjoint (fan u s) (stem k v t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  obtain ⟨huv, hst⟩ := fan_stem_port_eq hp hq
  exact h (Prod.ext huv hst)

/-- The two segments at one port contact only at their elbow. -/
theorem fan_stem_endpointContacts (k v : ℕ) (s : Fin 3) :
    EndpointContacts (center v) (elbow v s) (elbow v s) (column v s, rail k) := by
  intro p hp hq
  change p ∈ fan v s at hp
  change p ∈ stem k v s at hq
  rw [mem_stem, Set.uIcc_of_le (show ((elbow v s).2 : ℝ) ≤ rail k by
    exact_mod_cast (elbow_below_rail k v s).le)] at hq
  have heq : p = realPoint (elbow v s) := by
    apply Prod.ext hq.1
    rw [mem_fan] at hp
    rcases hp with ⟨rfl, hy, hx⟩ | ⟨rfl, hx, hy⟩ | ⟨rfl, hy, hx⟩ <;>
      norm_num only [realPoint, elbow, column, Layout.column, Fin.ext_iff, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
        Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Set.mem_Icc] at hq ⊢ <;>
      linarith
  exact ⟨Or.inr heq, Or.inl heq⟩

/-- A stem meets its own bridge only at their shared top endpoint. -/
theorem stem_bridge_endpointContacts (k u v : ℕ) (s t : Fin 3) :
    EndpointContacts (elbow u s) (column u s, rail k)
      (column u s, rail k) (column v t, rail k) := by
  intro p hp hq
  have heq : p = realPoint (column u s, rail k) :=
    Prod.ext (mem_stem.1 hp).1 (mem_bridge.1 hq).1
  exact ⟨Or.inr heq, Or.inl heq⟩

/-- The six listed points are distinct when the endpoint addresses are distinct. -/
theorem route_nodup {k u v : ℕ} (huv : u ≠ v) (s t : Fin 3) :
    (route k u v s t).Nodup := by
  fin_cases s <;> fin_cases t <;>
    norm_num only [route, center, elbow, column, Layout.column, rail, List.nodup_cons,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two,
      ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
      not_false_eq_true, and_true, List.nodup_nil] <;>
    simp only [and_true, true_and, and_false, or_false, false_or, not_false_eq_true] <;> omega

end PushPuzzle.NCL.Strip.Tracks
