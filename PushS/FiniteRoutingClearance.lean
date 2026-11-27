/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingInitial

/-! Clearance of actual narrow primitive marks along distinct arms and nonadjacent segments. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

theorem nearby_of_le {a b : ℕ} (hab : a ≤ b) {p q : ℕ × ℕ} (h : Nearby a p q) :
    Nearby b p q := by unfold Nearby at *; omega

/-- Literal padded footprints with a separated centerline have distinct physical cells. -/
theorem footprint_ne {w m n : ℕ} {p q a b : ℕ × ℕ}
    (hsep : ¬Nearby (m+n) p q)
    (ha : Nearby m a (padding w+p.1,padding w+p.2))
    (hb : Nearby n b (padding w+q.1,padding w+q.2)) : a ≠ b := by
  intro he
  rw [he] at ha
  unfold Nearby at *
  omega

theorem footprint_not_nearby {w m n r : ℕ} {p q a b : ℕ × ℕ}
    (hsep : ¬Nearby (m+n+r) p q)
    (ha : Nearby m a (padding w+p.1,padding w+p.2))
    (hb : Nearby n b (padding w+q.1,padding w+q.2)) : ¬Nearby r a b := by
  unfold Nearby at *
  omega

theorem routes_separated_wide (w : ℕ) (kind : Bool) (pattern rotation : Fin 3)
    {i j : Fin 3} (hij : i ≠ j) {p q : ℕ × ℕ}
    (hp : ∃ s ∈ route w kind (pattern,rotation,i), s.Contains p)
    (hq : ∃ t ∈ route w kind (pattern,rotation,j), t.Contains q) :
    ¬Nearby (2*w+6) p q := by
  obtain ⟨s,hs,hp⟩ := hp
  obtain ⟨t,ht,hq⟩ := hq
  rcases List.mem_append.mp hs with hs | hs <;> rcases List.mem_append.mp ht with ht | ht
  · exact adapters_separated_wide w kind hij ⟨s,hs,hp⟩ ⟨t,ht,hq⟩
  · intro hn
    exact Segment.not_nearby_of_gap (adapter_ring_gap w kind i (pattern,rotation,j) hij hs ht) hp hq
      (nearby_of_le (by unfold FiniteGeometry.origin; omega) hn)
  · intro hn
    have hh := Segment.not_nearby_of_gap
      (adapter_ring_gap w kind j (pattern,rotation,i) (Ne.symm hij) ht hs) hq hp
    unfold Nearby at *
    unfold FiniteGeometry.origin at hh
    omega
  · intro hn
    exact separated w pattern rotation hij ⟨s,hs,hp⟩ ⟨t,ht,hq⟩
      (nearby_of_le (by unfold spacing; omega) hn)

private theorem route_tail_parts (w : ℕ) (kind : Bool) (q : Key) {p : ℕ × ℕ}
    (hp : ∃ s ∈ (route w kind q).tail, s.Contains p) :
    (∃ s ∈ (adapter w kind q.2.2).tail, s.Contains p) ∨
      (∃ s ∈ curve w q, s.Contains p) := by
  have hne : adapter w kind q.2.2 ≠ [] := by
    intro h
    have hh := adapter_length w kind q.2.2
    rw [h] at hh
    contradiction
  obtain ⟨a,atoms,he⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨s,hs,hp⟩ := hp
  change s ∈ (adapter w kind q.2.2 ++ curve w q).tail at hs
  rw [he] at hs
  simp only [List.cons_append,List.tail_cons] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact Or.inl ⟨s,by simpa only [he,List.tail_cons] using hs,hp⟩
  · exact Or.inr ⟨s,hs,hp⟩

/-- Every noninitial fragment has room for its full tool window against every other arm. -/
theorem route_tail_separated (w : ℕ) (kind : Bool) (pattern rotation : Fin 3)
    {i j : Fin 3} (hij : i ≠ j) {p q : ℕ × ℕ}
    (hp : ∃ s ∈ (route w kind (pattern,rotation,i)).tail, s.Contains p)
    (hq : ∃ t ∈ route w kind (pattern,rotation,j), t.Contains q) :
    ¬Nearby (FiniteGeometry.origin w) p q := by
  rcases route_tail_parts w kind (pattern,rotation,i) hp with hp | hp
  all_goals obtain ⟨s,hs,hp⟩ := hp; obtain ⟨t,ht,hq⟩ := hq
  · rcases List.mem_append.mp ht with ht | ht
    · exact adapter_tail_separated w kind hij ⟨s,hs,hp⟩ ⟨t,ht,hq⟩
    · exact Segment.not_nearby_of_gap
        (adapter_ring_gap w kind i (pattern,rotation,j) hij (List.mem_of_mem_tail hs) ht) hp hq
  · rcases List.mem_append.mp ht with ht | ht
    · have hh := Segment.not_nearby_of_gap
        (adapter_ring_gap w kind j (pattern,rotation,i) (Ne.symm hij) ht hs) hq hp
      unfold Nearby at *
      omega
    · intro hn
      exact separated w pattern rotation hij ⟨s,hs,hp⟩ ⟨t,ht,hq⟩
        (nearby_of_le (by unfold FiniteGeometry.origin spacing; omega) hn)

theorem segment_shrink_contains (d : Direction) (p q : ℕ × ℕ) (length front back : ℕ)
    (ht : Travels d p q length) (hl : front+back ≤ length) {u : ℕ × ℕ}
    (hu : (⟨advance d p front,advance d.opposite q back⟩ : Segment).Contains u) :
    (⟨p,q⟩ : Segment).Contains u := by
  cases d <;> dsimp [Travels,advance,Direction.opposite,Segment.Contains] at * <;> omega

theorem trimmed_trace_subset (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2)
    (front back : ℕ) (hl : front+back ≤ segmentLength s) {u : ℕ × ℕ}
    (hu : (trimmed s front back).Contains u) : s.Contains u :=
  segment_shrink_contains _ _ _ _ front back (segment_travels s hs) hl hu

end PushPuzzle.PushS.FiniteRouting
