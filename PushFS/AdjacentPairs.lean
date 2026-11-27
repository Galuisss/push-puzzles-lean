/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Components

/-!
# Adjacent boxes on straight static components

On a successful component-preserving path, two adjacent boxes on a straight
component cannot separate. This is Step 3 of the SCC transfer argument.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

private theorem adjacent_on_line {d e : Direction} {rear p q next : Cell w h}
    (hr : Adjacent d rear p) (hn : Adjacent d p next) (hq : Adjacent e p q)
    (hl : (p.1 = q.1 ∧ p.1 = next.1) ∨ (p.2 = q.2 ∧ p.2 = next.2)) :
    q = rear ∨ q = next := by
  have he : e = d ∨ e = d.opposite := by
    cases d <;> cases e <;> first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | simp only [Adjacent] at hn hq
      rcases hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩ <;> omega
  rcases he with rfl | rfl
  · exact Or.inr (hq.functional hn)
  · exact Or.inl (hq.functional hr.reverse)

/-- Every cell of a component lies on one row or on one column. -/
def ComponentLinear {B : Board w h} (c : Component B) : Prop :=
  (∀ p q, component B p = c → component B q = c → p.1 = q.1) ∨
    (∀ p q, component B p = c → component B q = c → p.2 = q.2)

/-- A same-component adjacent box pair. -/
def AdjacentPair {B : Board w h} (c : Component B) (s : State w h) : Prop :=
  ∃ p ∈ s.boxes, ∃ q ∈ s.boxes,
    component B p = c ∧ component B q = c ∧ ∃ d, Adjacent d p q

private theorem run_target_mem {B : Board w h} {d : Direction} {s t : State w h}
    {n : ℕ} (r : Run B d s n)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (i : Fin (n + 2)) (hi : 2 ≤ i.val) : r.cell i ∈ t.boxes := by
  rw [hb, Finset.mem_insert, Finset.mem_erase]
  by_cases he : i.val = n + 1
  · exact Or.inl (congrArg r.cell (Fin.ext he))
  · refine Or.inr ⟨?_, r.occupied_at i (by omega) (by omega)⟩
    intro h
    have hval := congrArg Fin.val (r.injective h)
    simp only [Fin.val_one] at hval
    omega

private theorem run_pair_of_first {B : Board w h} {d e : Direction}
    {s t : State w h} {n : ℕ} (r : Run B d s n) (hn : 0 < n)
    (hv : s.Valid B)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (he : component B (r.cell 1) = component B (r.cell ⟨n + 1, by omega⟩))
    {c : Component B} (hline : ComponentLinear c)
    (hfirst : component B (r.cell 1) = c) {q : Cell w h}
    (hq : q ∈ s.boxes) (hqc : component B q = c) (ha : Adjacent e (r.cell 1) q) :
    AdjacentPair c t := by
  let second : Fin (n + 2) := ⟨2, by omega⟩
  have hadj : Adjacent d (r.cell 1) (r.cell second) := r.adjacent ⟨1, by omega⟩
  have hscomp : component B (r.cell second) = c :=
    (r.component_eq_first he second (by change 0 < 2; omega)).trans hfirst
  have hl : ((r.cell 1).1 = q.1 ∧ (r.cell 1).1 = (r.cell second).1) ∨
      ((r.cell 1).2 = q.2 ∧ (r.cell 1).2 = (r.cell second).2) := by
    rcases hline with hx | hy
    · exact Or.inl ⟨hx _ _ hfirst hqc, hx _ _ hfirst hscomp⟩
    · exact Or.inr ⟨hy _ _ hfirst hqc, hy _ _ hfirst hscomp⟩
  have hrear : Adjacent d s.player (r.cell 1) := r.start ▸ r.adjacent 0
  have hqsecond : q = r.cell second := by
    rcases adjacent_on_line hrear hadj ha hl with heq | heq
    · exact False.elim (hv.2.2 (heq ▸ hq))
    · exact heq
  have hn2 : 2 ≤ n := by
    by_contra hh
    have hen : second = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      change 2 = n + 1
      omega
    rw [hqsecond, hen] at hq
    exact r.empty hq
  let third : Fin (n + 2) := ⟨3, by omega⟩
  refine ⟨r.cell second, run_target_mem r hb second (by rfl), r.cell third,
    run_target_mem r hb third (by change 2 ≤ 3; omega), hscomp, ?_, d, ?_⟩
  · exact (r.component_eq_first he third (by change 0 < 3; omega)).trans hfirst
  · exact r.adjacent ⟨2, by omega⟩

/-- A potential-preserving move retains an adjacent pair in a straight component. -/
private theorem AdjacentPair.move {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : State w h} {c : Component B} (hp : AdjacentPair c s)
    (hline : ComponentLinear c) (hm : Move B cap d s t)
    (he : potential B s = potential B t) : AdjacentPair c t := by
  obtain ⟨p, hp, q, hq, hpc, hqc, e, ha⟩ := hp
  cases hm with
  | walk _ _ _ _ hb => exact ⟨p, hb ▸ hp, q, hb ▸ hq, hpc, hqc, e, ha⟩
  | push hv hn _ r _ hb =>
    have hc := r.component_eq_of_potential_eq hn hb he
    by_cases hpf : p = r.cell 1
    · subst p
      exact run_pair_of_first r hn hv hb hc hline hpc hq hqc ha
    · by_cases hqf : q = r.cell 1
      · subst q
        exact run_pair_of_first r hn hv hb hc hline hqc hp hpc ha.reverse
      · refine ⟨p, ?_, q, ?_, hpc, hqc, e, ha⟩
        · rw [hb, Finset.mem_insert, Finset.mem_erase]
          exact Or.inr ⟨hpf, hp⟩
        · rw [hb, Finset.mem_insert, Finset.mem_erase]
          exact Or.inr ⟨hqf, hq⟩

/-- An adjacent pair persists along every potential-preserving path on a straight SCC. -/
theorem AdjacentPair.reachable {B : Board w h} {cap : Option ℕ}
    {s t : State w h} {c : Component B} (hp : AdjacentPair c s)
    (hline : ComponentLinear c) (hr : Reachable B cap s t)
    (he : potential B s = potential B t) : AdjacentPair c t := by
  have hquiet := hr.preserving_potential he
  clear hr he
  induction hquiet with
  | refl => exact hp
  | tail _ hm ih => exact ih.move hline hm.1.choose_spec hm.2

end PushPuzzle.PushFS
