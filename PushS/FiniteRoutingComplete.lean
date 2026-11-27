/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSeparation

/-! Complete, separated physical gate-to-boundary route families. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

/-- The real core port, its offset adapter, and its checked annular continuation. -/
def route (w : ℕ) (kind : Bool) (q : Key) : List Segment :=
  adapter w kind q.2.2 ++ curve w q

theorem route_length (w : ℕ) (kind : Bool) (q : Key) :
    (route w kind q).length = 5 + (curve w q).length := by
  simp only [route, List.length_append, adapter_length]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_first : ∀ q : Key,
    ((PortAnnulus.curve q).headD ⟨(0,0),(0,0)⟩).start = PortAnnulus.innerPoint q.2.2 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_last : ∀ q : Key,
    ((PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩).finish =
      PortAnnulus.outerPoint (PortAnnulus.outerDirection q) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_nonempty : ∀ q : Key, PortAnnulus.curve q ≠ [] := by decide +kernel

theorem curve_nonempty (w : ℕ) (q : Key) : curve w q ≠ [] := by
  intro h
  have hh : PortAnnulus.curve q = [] := by
    have hlen := congrArg List.length h
    simp only [curve, List.length_map, List.length_nil] at hlen
    exact List.length_eq_zero_iff.mp hlen
  exact source_nonempty q hh

private theorem adapter_first_start (w : ℕ) (kind : Bool) (role : Fin 3) :
    ((adapter w kind role).headD ⟨(0,0),(0,0)⟩).start = corePort w kind role := by
  fin_cases role <;> simp [adapter, adapterVertices]

private theorem curve_first_start (w : ℕ) (q : Key) :
    ((curve w q).headD ⟨(0,0),(0,0)⟩).start =
      scalePoint (spacing w) (PortAnnulus.innerPoint q.2.2) := by
  have hzero : scaleSegment (spacing w) ⟨(0,0),(0,0)⟩ = ⟨(0,0),(0,0)⟩ := by
    simp [scaleSegment, scalePoint]
  have hmap := @List.headD_map _ _ (scaleSegment (spacing w)) (PortAnnulus.curve q) ⟨(0,0),(0,0)⟩
  have hh : (curve w q).headD ⟨(0,0),(0,0)⟩ =
      scaleSegment (spacing w) ((PortAnnulus.curve q).headD ⟨(0,0),(0,0)⟩) := by
    simpa only [curve, hzero] using hmap
  rw [hh]
  change scalePoint (spacing w) ((PortAnnulus.curve q).headD ⟨(0,0),(0,0)⟩).start = _
  rw [source_first]

private theorem curve_last_finish (w : ℕ) (q : Key) :
    ((curve w q).getLastD ⟨(0,0),(0,0)⟩).finish =
      scalePoint (spacing w) (PortAnnulus.outerPoint (PortAnnulus.outerDirection q)) := by
  have hzero : scaleSegment (spacing w) ⟨(0,0),(0,0)⟩ = ⟨(0,0),(0,0)⟩ := by
    simp [scaleSegment, scalePoint]
  have hmap := @List.getLastD_map _ _ (scaleSegment (spacing w)) (PortAnnulus.curve q) ⟨(0,0),(0,0)⟩
  have hh : (curve w q).getLastD ⟨(0,0),(0,0)⟩ =
      scaleSegment (spacing w) ((PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩) := by
    simpa only [curve, hzero] using hmap
  rw [hh]
  change scalePoint (spacing w) ((PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩).finish = _
  rw [source_last]

private theorem adapter_last_finish (w : ℕ) (kind : Bool) (role : Fin 3) :
    ((adapter w kind role).getLastD ⟨(0,0),(0,0)⟩).finish =
      scalePoint (spacing w) (PortAnnulus.innerPoint role) := by
  cases kind <;> fin_cases role <;>
    simp [adapter, adapterVertices, corePort, scalePoint, PortAnnulus.innerPoint, Nat.mul_comm]

private theorem option_getD_of_mem {α : Type} {o : Option α} {a : α} (d : α)
    (ha : a ∈ o) : o.getD d = a := by
  cases o <;> simp_all

/-- The adapter and ring join at the same literal core-facing annular port. -/
theorem route_joined (w : ℕ) (kind : Bool) (q : Key) :
    (route w kind q).IsChain (fun s t => s.finish = t.start) := by
  apply (adapter_joined w kind q.2.2).append (joined w q)
  intro s hs t ht
  have hs' : (adapter w kind q.2.2).getLastD ⟨(0,0),(0,0)⟩ = s := by
    rw [List.getLastD_eq_getLast?]
    exact option_getD_of_mem _ hs
  have ht' : (curve w q).headD ⟨(0,0),(0,0)⟩ = t := by
    rw [List.headD_eq_head?_getD]
    exact option_getD_of_mem _ ht
  rw [←hs', ←ht', adapter_last_finish, curve_first_start]

theorem route_first_start (w : ℕ) (kind : Bool) (q : Key) :
    ((route w kind q).headD ⟨(0,0),(0,0)⟩).start = corePort w kind q.2.2 := by
  have hne : adapter w kind q.2.2 ≠ [] := by
    intro hh
    have := adapter_length w kind q.2.2
    rw [hh] at this
    contradiction
  obtain ⟨s, ss, he⟩ := List.exists_cons_of_ne_nil hne
  simpa only [route, he, List.cons_append, List.headD_cons] using adapter_first_start w kind q.2.2

theorem route_last_finish (w : ℕ) (kind : Bool) (q : Key) :
    ((route w kind q).getLastD ⟨(0,0),(0,0)⟩).finish =
      scalePoint (spacing w) (PortAnnulus.outerPoint (PortAnnulus.outerDirection q)) := by
  have hne := curve_nonempty w q
  cases he : (curve w q).getLast? with
  | none => simp_all
  | some t =>
    simpa only [route, List.getLastD_eq_getLast?, List.getLast?_append, he,
      Option.some_or, Option.getD_some] using curve_last_finish w q

private theorem nearby_mono {a b : ℕ} (hab : a ≤ b) {p q : ℕ × ℕ}
    (h : ¬Nearby b p q) : ¬Nearby a p q := by
  unfold Nearby at *
  omega

/-- Different complete arms retain a gap wider than the thick wall. -/
theorem routes_separated (w : ℕ) (kind : Bool) (pattern rotation : Fin 3)
    {i j : Fin 3} (hij : i ≠ j) {p q : ℕ × ℕ}
    (hp : ∃ s ∈ route w kind (pattern,rotation,i), s.Contains p)
    (hq : ∃ t ∈ route w kind (pattern,rotation,j), t.Contains q) :
    ¬Nearby (w+1) p q := by
  obtain ⟨s, hs, hp⟩ := hp
  obtain ⟨t, ht, hq⟩ := hq
  rcases List.mem_append.mp hs with hs | hs <;> rcases List.mem_append.mp ht with ht | ht
  · exact adapters_separated w kind hij ⟨s,hs,hp⟩ ⟨t,ht,hq⟩
  · apply nearby_mono (show w+1 ≤ FiniteGeometry.origin w by unfold FiniteGeometry.origin; omega)
    exact Segment.not_nearby_of_gap (adapter_ring_gap w kind i (pattern,rotation,j) hij hs ht) hp hq
  · apply nearby_mono (show w+1 ≤ FiniteGeometry.origin w by unfold FiniteGeometry.origin; omega)
    have hh := Segment.not_nearby_of_gap
      (adapter_ring_gap w kind j (pattern,rotation,i) (Ne.symm hij) ht hs) hq hp
    unfold Nearby at *
    omega
  · exact nearby_mono (show w+1 ≤ spacing w by unfold spacing; omega)
      (separated w pattern rotation hij ⟨s,hs,hp⟩ ⟨t,ht,hq⟩)

theorem route_trace_bounded (w : ℕ) (kind : Bool) (q : Key) {p : ℕ × ℕ}
    (hp : ∃ s ∈ route w kind q, s.Contains p) : p.1 < side w ∧ p.2 < side w := by
  obtain ⟨s, hs, hp⟩ := hp
  rcases List.mem_append.mp hs with hs | hs
  · exact adapter_trace_bounded w kind q.2.2 ⟨s,hs,hp⟩
  · exact trace_bounded w q ⟨s,hs,hp⟩

theorem route_segment_length (w : ℕ) (kind : Bool) (q : Key) {s : Segment}
    (hs : s ∈ route w kind q) :
    (s.start.1 = s.finish.1 ∧ min s.start.2 s.finish.2 + FiniteGeometry.origin w ≤
      max s.start.2 s.finish.2) ∨
    (s.start.2 = s.finish.2 ∧ min s.start.1 s.finish.1 + FiniteGeometry.origin w ≤
      max s.start.1 s.finish.1) := by
  rcases List.mem_append.mp hs with hs | hs
  · exact adapter_segment_length w kind q.2.2 hs
  · have hh := segment_length w q hs
    have hm : FiniteGeometry.origin w ≤ spacing w := by unfold FiniteGeometry.origin spacing; omega
    rcases hh with hh | hh <;> omega

private theorem getD_mem {α : Type} {l : List α} {n : ℕ} (d : α) (hn : n < l.length) :
    l.getD n d ∈ l :=
  List.mem_iff_get.mpr ⟨⟨n,hn⟩, (List.getD_eq_get l d ⟨n,hn⟩).symm⟩

private theorem getD_mem_take {α : Type} {l : List α} {n m : ℕ} (d : α)
    (hn : n < l.length) (hm : n < m) : l.getD n d ∈ l.take m := by
  apply List.mem_take_iff_getElem.mpr
  exact ⟨n, by omega, (List.getD_eq_getElem l d hn).symm⟩

private theorem getD_mem_tail {α : Type} {l : List α} {n : ℕ} (d : α)
    (hn : n < l.length) (hpos : 0 < n) : l.getD n d ∈ l.tail := by
  cases n with
  | zero => omega
  | succ n =>
    cases l with
    | nil => simp at hn
    | cons a l =>
      simp only [List.getD_cons_succ, List.tail_cons]
      exact getD_mem d (by simpa using hn)

set_option maxRecDepth 65536 in
/-- Nonconsecutive fragments of a complete arm leave the full linear walking margin. -/
theorem route_nonadjacent_gap (w : ℕ) (kind : Bool) (q : Key)
    (i j : Fin (route w kind q).length) (hij : i.val+1 < j.val) :
    ((route w kind q).getD i.val ⟨(0,0),(0,0)⟩).gapTest (FiniteGeometry.origin w)
      ((route w kind q).getD j.val ⟨(0,0),(0,0)⟩) = true := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [route_length] at hi hj
  by_cases hjA : j.val < 5
  · have hiA : i.val < 5 := by omega
    simp only [route]
    rw [List.getD_append _ _ _ _ (by simpa only [adapter_length] using hiA),
      List.getD_append _ _ _ _ (by simpa only [adapter_length] using hjA)]
    exact adapter_nonadjacent_gap w kind q.2.2 ⟨i.val,hiA⟩ ⟨j.val,hjA⟩ hij
  · have hjR : 5 ≤ j.val := by omega
    have hjR' : j.val-5 < (curve w q).length := by omega
    by_cases hiA : i.val < 5
    · simp only [route]
      rw [List.getD_append _ _ _ _ (by simpa only [adapter_length] using hiA),
        List.getD_append_right _ _ _ _ (by simpa only [adapter_length] using hjR), adapter_length]
      by_cases hiP : i.val < 4
      · exact adapter_prefix_ring_gap w kind q.2.2 q
          (getD_mem_take _ (by simpa only [adapter_length] using hiA) hiP)
          (getD_mem _ hjR')
      · have hjpos : 0 < j.val-5 := by omega
        exact adapter_ring_tail_gap w kind q
          (getD_mem _ (by simpa only [adapter_length] using hiA))
          (getD_mem_tail _ hjR' hjpos)
    · have hiR : 5 ≤ i.val := by omega
      have hiR' : i.val-5 < (curve w q).length := by omega
      simp only [route]
      rw [List.getD_append_right _ _ _ _ (by simpa only [adapter_length] using hiR),
        List.getD_append_right _ _ _ _ (by simpa only [adapter_length] using hjR), adapter_length]
      exact curve_nonadjacent_gap w q ⟨i.val-5,hiR'⟩ ⟨j.val-5,hjR'⟩ (by change i.val-5+1 < j.val-5; omega)

end PushPuzzle.PushS.FiniteRouting
