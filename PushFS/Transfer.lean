/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AdjacentPairs

/-!
# SCC transfer from unlimited pushing to single-box pushing

C1 balances initial and target occupancy in each static SCC. C2 requires only
initially occupied SCCs to be straight. C3 forbids adjacent targets within one
SCC. Every successful unlimited-push trajectory on such an instance uses only
single-box pushes, preserving its exact intermediate states and player positions.

## Main results

* `Certificate.push_length_eq_one`: every push on a successful trajectory is single.
* `Certificate.reachable_one_of_solved`: transfer the entire successful trajectory.
* `Certificate.solvable_iff_one`: all positive push limits have the same solvability.

-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

/-- C1–C3 for a complete storage instance. -/
structure Certificate (I : Instance) : Prop where
  /-- Initial and goal occupancy agree on every static component. -/
  balanced : ComponentBalanced I.board I.initial
  /-- Every component initially containing a box is on a single row or column. -/
  linear : ∀ p ∈ I.initial.boxes, ComponentLinear (component I.board p)
  /-- Adjacent goals never lie in the same static component. -/
  separated : ∀ p ∈ I.board.goals, ∀ q ∈ I.board.goals,
    component I.board p = component I.board q → ∀ d, ¬Adjacent d p q

private theorem move_box_ancestor {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : State w h} (hm : Move B cap d s t) (he : potential B s = potential B t)
    {p : Cell w h} (hp : p ∈ t.boxes) :
    ∃ q ∈ s.boxes, component B q = component B p := by
  cases hm with
  | walk _ _ _ _ hb => exact ⟨p, hb ▸ hp, rfl⟩
  | push _ hn _ r _ hb =>
    rw [hb, Finset.mem_insert, Finset.mem_erase] at hp
    rcases hp with rfl | ⟨_, hp⟩
    · exact ⟨r.cell 1, r.first_occupied hn, r.component_eq_of_potential_eq hn hb he⟩
    · exact ⟨p, hp, rfl⟩

/-- On a potential-preserving path every box comes from the same initial SCC. -/
private theorem Reachable.box_ancestor {B : Board w h} {cap : Option ℕ} {s t : State w h}
    (hr : Reachable B cap s t) (he : potential B s = potential B t)
    {p : Cell w h} (hp : p ∈ t.boxes) :
    ∃ q ∈ s.boxes, component B q = component B p := by
  have hquiet := hr.preserving_potential he
  clear hr he
  induction hquiet generalizing p with
  | refl => exact ⟨p, hp, rfl⟩
  | tail _ hm ih =>
    obtain ⟨q, hq, hqc⟩ := move_box_ancestor hm.1.choose_spec hm.2 hp
    obtain ⟨r, hr, hrc⟩ := ih hq
    exact ⟨r, hr, hrc.trans hqc⟩

/-- A successful trajectory has no adjacent pair in a single static SCC. -/
theorem Certificate.no_adjacentPair {I : Instance} (cert : Certificate I)
    {s final : State I.width I.height} {c : Component I.board}
    (hbefore : Reachable I.board none I.initial s)
    (hafter : Reachable I.board none s final) (hsol : final.boxes = I.board.goals) :
    ¬AdjacentPair c s := by
  intro hp
  have hs := potential_eq_on_successful_path cert.balanced hbefore hafter hsol
  have hpair := hp
  obtain ⟨p, hps, _, _, hpc, _⟩ := hpair
  obtain ⟨q, hqi, hqc⟩ := hbefore.box_ancestor hs.symm hps
  have hline := cert.linear q hqi
  rw [hqc, hpc] at hline
  have hfinal := potential_eq_on_successful_path cert.balanced (hbefore.trans hafter) .refl hsol
  have he : potential I.board s = potential I.board final := hs.trans hfinal.symm
  obtain ⟨p, hp, q, hq, hpc, hqc, d, ha⟩ := hp.reachable hline hafter he
  rw [hsol] at hp hq
  exact cert.separated p hp q hq (hpc.trans hqc.symm) d ha

/-- Every push occurring on a successful unlimited-push trajectory moves exactly one box. -/
theorem Certificate.push_length_eq_one {I : Instance} (cert : Certificate I)
    {s t final : State I.width I.height} {d : Direction} {n : ℕ}
    (hbefore : Reachable I.board none I.initial s) (hv : s.Valid I.board)
    (hn : 0 < n) (r : Run I.board d s n) (hp : t.player = r.cell 1)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (hafter : Reachable I.board none t final) (hsol : final.boxes = I.board.goals) : n = 1 := by
  have hm : Step I.board none s t := ⟨d, .push hv hn trivial r hp hb⟩
  have hall := hafter.head hm
  have hs := potential_eq_on_successful_path cert.balanced hbefore hall hsol
  have ht := potential_eq_on_successful_path cert.balanced (hbefore.tail hm) hafter hsol
  have hc := r.component_eq_of_potential_eq hn hb (hs.trans ht.symm)
  by_contra hne
  have hn2 : 2 ≤ n := by omega
  let second : Fin (n + 2) := ⟨2, by omega⟩
  have hadj : Adjacent d (r.cell 1) (r.cell second) := r.adjacent ⟨1, by omega⟩
  apply cert.no_adjacentPair hbefore hall hsol
  exact ⟨r.cell 1, r.first_occupied hn, r.cell second,
    r.occupied_at second (by change 0 < 2; omega) hn2, rfl,
    r.component_eq_first hc second (by change 0 < 2; omega), d, hadj⟩

private theorem successful_move_one {I : Instance} (cert : Certificate I)
    {s t final : State I.width I.height} {d : Direction}
    (hbefore : Reachable I.board none I.initial s) (hm : Move I.board none d s t)
    (hafter : Reachable I.board none t final) (hsol : final.boxes = I.board.goals) :
    Move I.board (some 1) d s t := by
  cases hm with
  | walk hv ha hf he hb => exact .walk hv ha hf he hb
  | push hv hn _ r hp hb =>
    have he := cert.push_length_eq_one hbefore hv hn r hp hb hafter hsol
    exact .push hv hn (by change _ ≤ 1; omega) r hp hb

/-- Transfer a successful unlimited trajectory, keeping all states and player positions. -/
theorem Certificate.reachable_one_of_solved {I : Instance} (cert : Certificate I)
    {final : State I.width I.height} (hr : Reachable I.board none I.initial final)
    (hsol : final.boxes = I.board.goals) : Reachable I.board (some 1) I.initial final := by
  have hconvert : ∀ {s t}, Reachable I.board none s t →
      Reachable I.board none I.initial s → Reachable I.board none t final →
        Reachable I.board (some 1) s t := by
    intro s t hp
    induction hp with
    | refl => intros; exact .refl
    | @tail u v hp hm ih =>
      intro hbefore hafter
      have hstep := successful_move_one cert (hbefore.trans hp) hm.choose_spec hafter hsol
      exact (ih hbefore (hafter.head hm)).tail ⟨hm.choose, hstep⟩
  exact hconvert hr .refl .refl

/-- Unlimited pushing and single-box pushing have the same solvability under C1–C3. -/
theorem Certificate.solvable_unlimited_iff_one {I : Instance} (cert : Certificate I) :
    I.Solvable none ↔ I.Solvable (some 1) := by
  constructor
  · rintro ⟨t, hr, hsol⟩
    exact ⟨t, cert.reachable_one_of_solved hr hsol, hsol⟩
  · exact Instance.solvable_unlimited

/-- Every fixed positive push limit has the same solvability as single-box pushing under C1–C3. -/
theorem Certificate.solvable_iff_one {I : Instance} (cert : Certificate I)
    {k : ℕ} (hk : 1 ≤ k) : I.Solvable (some k) ↔ I.Solvable (some 1) :=
  ⟨fun h => cert.solvable_unlimited_iff_one.mp (Instance.solvable_unlimited h),
    Instance.solvable_of_one hk⟩

end PushPuzzle.PushFS
