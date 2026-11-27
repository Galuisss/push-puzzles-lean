/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingAdapters
import Mathlib.Tactic.FinCases

/-! Separation of complete parameterized gate routing paths. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

set_option maxRecDepth 65536 in
/-- Each adapter remains on the outward side of its actual core port. -/
private theorem adapter_trace_sides (w : ℕ) (kind : Bool) (role : Fin 3) {p : ℕ × ℕ}
    (hp : ∃ s ∈ adapter w kind role, s.Contains p) :
    (role = 0 → p.1 ≤ (corePort w kind 0).1) ∧
      (role = 1 → 25*spacing w ≤ p.1 ∧ p.2 ≤ (corePort w kind 1).2) ∧
      (role = 2 → 25*spacing w ≤ p.2 ∧ (corePort w kind 2).1 ≤ p.1) := by
  obtain ⟨s, hs, hp⟩ := hp
  have hb := Segment.coordinate_bounds hp
  clear hp
  cases kind <;> fin_cases role <;>
    simp [adapter, adapterVertices, corePort, spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    simp [corePort, spacing] at * <;> omega

/-- Distinct complete adapters have a gap wider than the thick wall. -/
theorem adapters_separated (w : ℕ) (kind : Bool) {i j : Fin 3} (hij : i ≠ j)
    {p q : ℕ × ℕ} (hp : ∃ s ∈ adapter w kind i, s.Contains p)
    (hq : ∃ t ∈ adapter w kind j, t.Contains q) : ¬Nearby (w+1) p q := by
  have hi := adapter_trace_sides w kind i hp
  have hj := adapter_trace_sides w kind j hq
  intro hn
  cases kind <;> fin_cases i <;> fin_cases j <;>
    simp_all [corePort, spacing, Nearby] <;> omega

/-- The complete thin centerlines have room for a wall strip and another primitive's actors. -/
theorem adapters_separated_wide (w : ℕ) (kind : Bool) {i j : Fin 3} (hij : i ≠ j)
    {p q : ℕ × ℕ} (hp : ∃ s ∈ adapter w kind i, s.Contains p)
    (hq : ∃ t ∈ adapter w kind j, t.Contains q) : ¬Nearby (2*w+6) p q := by
  have hi := adapter_trace_sides w kind i hp
  have hj := adapter_trace_sides w kind j hq
  intro hn
  cases kind <;> fin_cases i <;> fin_cases j <;>
    simp_all [corePort, spacing, Nearby] <;> omega

set_option maxRecDepth 65536 in
private theorem adapter_tail_trace_sides (w : ℕ) (kind : Bool) (role : Fin 3) {p : ℕ × ℕ}
    (hp : ∃ s ∈ (adapter w kind role).tail, s.Contains p) :
    (role = 0 → p.1 ≤ 24*spacing w) ∧
      (role = 1 → p.2 ≤ 24*spacing w) ∧
      (role = 2 → 26*spacing w ≤ p.1) := by
  obtain ⟨s,hs,hp⟩ := hp
  have hb := Segment.coordinate_bounds hp
  clear hp
  cases kind <;> fin_cases role <;>
    simp [adapter,adapterVertices,corePort,spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl <;>
    dsimp only at hb <;> simp [spacing] <;> omega

set_option maxRecDepth 65536 in
private theorem adapter_trace_far_or_lane (w : ℕ) (kind : Bool) (role : Fin 3) {p : ℕ × ℕ}
    (hp : ∃ s ∈ adapter w kind role, s.Contains p) :
    (role = 0 → p.1 ≤ 24*spacing w ∨ p.2 = (corePort w kind 0).2) ∧
      (role = 1 → p.2 ≤ 24*spacing w ∨ p.1 = (corePort w kind 1).1) ∧
      (role = 2 → 26*spacing w ≤ p.1 ∨ p.2 = 25*spacing w) := by
  obtain ⟨s,hs,hp⟩ := hp
  have hb := Segment.coordinate_bounds hp
  clear hp
  cases kind <;> fin_cases role <;>
    simp [adapter,adapterVertices,corePort,spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    dsimp only at hb <;> simp [corePort,spacing] <;> omega

set_option maxRecDepth 65536 in
/-- Away from the short core-facing rays, distinct adapters have a full linear tool-window gap. -/
theorem adapter_tail_separated (w : ℕ) (kind : Bool) {i j : Fin 3} (hij : i ≠ j)
    {p q : ℕ × ℕ} (hp : ∃ s ∈ (adapter w kind i).tail, s.Contains p)
    (hq : ∃ t ∈ adapter w kind j, t.Contains q) : ¬Nearby (FiniteGeometry.origin w) p q := by
  have hi := adapter_tail_trace_sides w kind i hp
  have hip := adapter_trace_sides w kind i
    (by obtain ⟨s,hs,hp⟩ := hp; exact ⟨s,List.mem_of_mem_tail hs,hp⟩)
  have hj := adapter_trace_sides w kind j hq
  have hjs := adapter_trace_far_or_lane w kind j hq
  intro hn
  cases kind <;> fin_cases i <;> fin_cases j <;>
    simp_all [corePort,spacing,Nearby,FiniteGeometry.origin] <;> omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Nonconsecutive segments of an adapter leave a full linear walking margin. -/
theorem adapter_nonadjacent_gap (w : ℕ) (kind : Bool) (role : Fin 3)
    (i j : Fin 5) (hij : i.val+1 < j.val) :
    ((adapter w kind role).getD i.val ⟨(0,0),(0,0)⟩).gapTest (FiniteGeometry.origin w)
      ((adapter w kind role).getD j.val ⟨(0,0),(0,0)⟩) = true := by
  fin_cases i <;> fin_cases j <;> try omega
  all_goals cases kind <;> fin_cases role <;>
    simp_all [adapter, adapterVertices, corePort, spacing, FiniteGeometry.origin,
      Segment.gapTest] <;> omega

/-- The first four adapter segments stay well inside the annulus's reserved square. -/
private theorem adapter_prefix_bounds (w : ℕ) (kind : Bool) (role : Fin 3)
    {s : Segment} (hs : s ∈ (adapter w kind role).take 4) :
    22*spacing w ≤ s.start.1 ∧ s.start.1 ≤ 28*spacing w ∧
      22*spacing w ≤ s.start.2 ∧ s.start.2 ≤ 28*spacing w ∧
      22*spacing w ≤ s.finish.1 ∧ s.finish.1 ≤ 28*spacing w ∧
      22*spacing w ≤ s.finish.2 ∧ s.finish.2 ≤ 28*spacing w := by
  cases kind <;> fin_cases role <;>
    simp [adapter, adapterVertices, corePort, spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl <;> simp [spacing] <;> omega

/-- A smaller requested margin preserves a certified interval gap. -/
private theorem gap_mono {s t : Segment} {a b : ℕ} (hab : a ≤ b)
    (hgap : s.gapTest b t = true) : s.gapTest a t = true := by
  simp only [Segment.gapTest, decide_eq_true_eq] at *
  omega

/-- Integer separation before scaling leaves every margin smaller than the scale free. -/
private theorem scaleSegment_gap_zero {factor margin : ℕ} (hm : margin < factor) {s t : Segment}
    (hgap : s.gapTest 0 t = true) :
    (scaleSegment factor s).gapTest margin (scaleSegment factor t) = true := by
  simp only [Segment.gapTest, decide_eq_true_eq, Nat.add_zero] at hgap ⊢
  simp only [scaleSegment, scalePoint, Nat.mul_min_mul_left, Nat.mul_max_mul_left]
  rcases hgap with hgap | hgap | hgap | hgap
  all_goals
    have hh := Nat.mul_le_mul_left factor (show _+1 ≤ _ from hgap)
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega

private def sourceCoreCheck (q : Key) : Bool :=
  (PortAnnulus.curve q).all fun s => decide
    (max s.start.1 s.finish.1 ≤ 20 ∨ 30 ≤ min s.start.1 s.finish.1 ∨
      max s.start.2 s.finish.2 ≤ 20 ∨ 30 ≤ min s.start.2 s.finish.2)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_core_checked : ∀ q : Key, sourceCoreCheck q = true := by decide +kernel

/-- The first four segments of every adapter are separated from every annular curve. -/
theorem adapter_prefix_ring_gap (w : ℕ) (kind : Bool) (role : Fin 3) (q : Key)
    {s t : Segment} (hs : s ∈ (adapter w kind role).take 4) (ht : t ∈ curve w q) :
    s.gapTest (FiniteGeometry.origin w) t = true := by
  have hb := adapter_prefix_bounds w kind role hs
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  have hh := of_decide_eq_true (List.all_eq_true.mp (source_core_checked q) t' ht')
  simp only [Segment.gapTest, decide_eq_true_eq, scaleSegment, scalePoint,
    Nat.mul_min_mul_left, Nat.mul_max_mul_left]
  rcases hh with hh | hh | hh | hh
  all_goals
    have hh' := Nat.mul_le_mul_left (spacing w) hh
    dsimp [spacing, FiniteGeometry.origin] at *
    omega

/-- The short inward radial continuation of each checked annular port. -/
def radial (role : Fin 3) : Segment :=
  if role = 0 then ⟨(22,25),(20,25)⟩
  else if role = 1 then ⟨(25,22),(25,20)⟩
  else ⟨(28,25),(30,25)⟩

private theorem adapter_decompose (w : ℕ) (kind : Bool) (role : Fin 3) :
    adapter w kind role = (adapter w kind role).take 4 ++ [scaleSegment (spacing w) (radial role)] := by
  cases kind <;> fin_cases role <;>
    simp [adapter, adapterVertices, corePort, radial, scaleSegment, scalePoint, Nat.mul_comm]

private def radialGapCheck (q : Key) (role : Fin 3) : Bool :=
  (if role = q.2.2 then (PortAnnulus.curve q).tail else PortAnnulus.curve q).all
    fun t => (radial role).gapTest 1 t

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem radial_gap_checked : ∀ q : Key, ∀ role : Fin 3,
    radialGapCheck q role = true := by decide +kernel

/-- Each radial continuation misses the other arms and its own post-turn annular suffix. -/
private theorem radial_ring_gap (w : ℕ) (role : Fin 3) (q : Key) {t : Segment}
    (ht : t ∈ if role = q.2.2 then (curve w q).tail else curve w q) :
    (scaleSegment (spacing w) (radial role)).gapTest (spacing w) t = true := by
  have hm : (if role = q.2.2 then (curve w q).tail else curve w q) =
      (if role = q.2.2 then (PortAnnulus.curve q).tail else PortAnnulus.curve q).map
        (scaleSegment (spacing w)) := by
    split_ifs <;> simp only [curve, List.map_tail]
  rw [hm] at ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  have hh := List.all_eq_true.mp (radial_gap_checked q role) t' ht'
  simpa only [Nat.mul_one] using scaleSegment_gap (spacing_pos w) hh

/-- A complete adapter is separated from every annular arm with a different role. -/
theorem adapter_ring_gap (w : ℕ) (kind : Bool) (role : Fin 3) (q : Key)
    (hrole : role ≠ q.2.2) {s t : Segment}
    (hs : s ∈ adapter w kind role) (ht : t ∈ curve w q) :
    s.gapTest (FiniteGeometry.origin w) t = true := by
  rw [adapter_decompose] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact adapter_prefix_ring_gap w kind role q hs ht
  · have he := List.mem_singleton.mp hs
    subst s
    apply gap_mono (show FiniteGeometry.origin w ≤ spacing w by unfold FiniteGeometry.origin spacing; omega)
    apply radial_ring_gap w role q
    simpa only [hrole, ↓reduceIte] using ht

private def sourceSimpleCheck (q : Key) : Bool :=
  (List.range (PortAnnulus.curve q).length).all fun i =>
    (List.range (PortAnnulus.curve q).length).all fun j =>
      if i+1 < j then
        ((PortAnnulus.curve q).getD i ⟨(0,0),(0,0)⟩).gapTest 0
          ((PortAnnulus.curve q).getD j ⟨(0,0),(0,0)⟩)
      else true

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_simple_checked : ∀ q : Key, sourceSimpleCheck q = true := by decide +kernel

set_option maxRecDepth 65536 in
/-- Nonconsecutive ring segments retain a full linear walking margin after scaling. -/
theorem curve_nonadjacent_gap (w : ℕ) (q : Key) (i j : Fin (curve w q).length)
    (hij : i.val+1 < j.val) :
    ((curve w q).getD i.val ⟨(0,0),(0,0)⟩).gapTest (FiniteGeometry.origin w)
      ((curve w q).getD j.val ⟨(0,0),(0,0)⟩) = true := by
  have hi : i.val < (PortAnnulus.curve q).length := by
    simpa only [curve_length] using i.isLt
  have hj : j.val < (PortAnnulus.curve q).length := by
    simpa only [curve_length] using j.isLt
  have hh := List.all_eq_true.mp
    (List.all_eq_true.mp (source_simple_checked q) i.val (List.mem_range.mpr hi))
      j.val (List.mem_range.mpr hj)
  simp only [hij, ↓reduceIte] at hh
  have hg := scaleSegment_gap_zero
    (show FiniteGeometry.origin w < spacing w by unfold FiniteGeometry.origin spacing; omega) hh
  have hzero : scaleSegment (spacing w) ⟨(0,0),(0,0)⟩ = ⟨(0,0),(0,0)⟩ := by
    simp [scaleSegment, scalePoint]
  have hget : ∀ n, (curve w q).getD n ⟨(0,0),(0,0)⟩ =
      scaleSegment (spacing w) ((PortAnnulus.curve q).getD n ⟨(0,0),(0,0)⟩) := by
    intro n
    simpa only [curve, hzero] using @List.getD_map _ _ (PortAnnulus.curve q) ⟨(0,0),(0,0)⟩ n
      (scaleSegment (spacing w))
  rw [hget, hget]
  exact hg

/-- Every adapter misses its own ring once the ring's initial straight segment is passed. -/
theorem adapter_ring_tail_gap (w : ℕ) (kind : Bool) (q : Key)
    {s t : Segment} (hs : s ∈ adapter w kind q.2.2) (ht : t ∈ (curve w q).tail) :
    s.gapTest (FiniteGeometry.origin w) t = true := by
  rw [adapter_decompose] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact adapter_prefix_ring_gap w kind q.2.2 q hs (List.mem_of_mem_tail ht)
  · have he := List.mem_singleton.mp hs
    subst s
    apply gap_mono (show FiniteGeometry.origin w ≤ spacing w by unfold FiniteGeometry.origin spacing; omega)
    apply radial_ring_gap w q.2.2 q
    simpa only [ite_true] using ht

end PushPuzzle.PushS.FiniteRouting
