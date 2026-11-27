/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Holes
public import Mathlib.Data.Nat.Dist

/-! Excursions from a permanently empty region have a global hole budget. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS

variable {w h : ℕ}

/-- Manhattan distance inside the rectangle. -/
def distance (p q : Cell w h) : ℕ := Nat.dist p.1.val q.1.val + Nat.dist p.2.val q.2.val

@[simp] theorem distance_self (p : Cell w h) : distance p p = 0 := by
  simp [distance]

theorem distance_eq_zero {p q : Cell w h} : distance p q = 0 ↔ p = q := by
  constructor
  · intro hd
    simp only [distance, Nat.dist] at hd
    apply Prod.ext <;> apply Fin.ext <;> omega
  · rintro rfl
    exact distance_self _

private theorem distance_adjacent {d : Direction} {p q : Cell w h} (ha : Adjacent d p q)
    (a : Cell w h) : distance a q ≤ distance a p + 1 := by
  cases d <;> simp only [Adjacent] at ha <;> simp only [distance, Nat.dist] <;> omega

/-- Every intermediate cell of a run is in any Manhattan ball containing its ends. -/
theorem run_distance_le {B : Board w h} {d : Direction} {s : State w h} {n r : ℕ}
    (run : Run B d s n) (a : Cell w h) (hs : distance a s.player ≤ r)
    (hz : distance a (run.cell ⟨n + 1, by omega⟩) ≤ r) (i : Fin (n + 2)) :
    distance a (run.cell i) ≤ r := by
  have hi := run.position i
  have he := run.position ⟨n + 1, by omega⟩
  have hli := run.lane i
  have hle := run.lane ⟨n + 1, by omega⟩
  have hib := i.isLt
  cases d <;>
    simp only [Direction.position, Direction.lane] at hi he hli hle <;>
    simp only [distance, Nat.dist] at hs hz ⊢ <;> omega

namespace Radius

/-- Holes outside the permanent region and the current distance ball. -/
def outside (P : Finset (Cell w h)) (a : Cell w h) (r : ℕ) (s : State w h) :
    Finset (Cell w h) :=
  (holes s \ P).filter (fun p => r < distance a p)

@[simp] theorem mem_outside {P : Finset (Cell w h)} {a p : Cell w h} {r : ℕ}
    {s : State w h} : p ∈ outside P a r s ↔ p ∈ holes s ∧ p ∉ P ∧ r < distance a p := by
  simp only [outside, Finset.mem_filter, Finset.mem_sdiff, and_assoc]

private theorem outside_zero (P : Finset (Cell w h)) (a : Cell w h) (s : State w h) :
    outside P a 0 s = (holes s \ P).erase a := by
  ext p
  simp only [mem_outside, Finset.mem_erase, Finset.mem_sdiff,
    Nat.pos_iff_ne_zero, ne_eq, distance_eq_zero]
  constructor
  · rintro ⟨he, hP, hne⟩
    exact ⟨Ne.symm hne, he, hP⟩
  · rintro ⟨hne, he, hP⟩
    exact ⟨he, hP, Ne.symm hne⟩

private theorem card_advance {α : Type} [DecidableEq α] {U V : Finset α} {p : α}
    (hp : p ∈ U) (hv : V ⊆ U.erase p) : V.card + 1 ≤ U.card := by
  have := Finset.card_le_card hv
  have := Finset.card_erase_add_one hp
  omega

/-- One step either stays in the ball or pays for radius growth with a fresh hole. -/
private theorem move_budget {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : State w h} {P : Finset (Cell w h)} {a : Cell w h} {r : ℕ}
    (hm : Move B cap d s t) (ht : P ⊆ holes t) (hp : t.player ∉ P)
    (hs : distance a s.player ≤ r) :
    ∃ r', distance a t.player ≤ r' ∧
      r' + (outside P a r' t).card ≤ r + (outside P a r s).card := by
  have hnext := (distance_adjacent (players_adjacent hm) a).trans (Nat.add_le_add_right hs 1)
  by_cases hstay : distance a t.player ≤ r
  · refine ⟨r, hstay, Nat.add_le_add_left (Finset.card_le_card ?_) r⟩
    intro p hpm
    obtain ⟨he, hP, hd⟩ := mem_outside.mp hpm
    refine mem_outside.mpr ⟨?_, hP, hd⟩
    cases hm with
    | walk _ _ _ _ hb => simpa [mem_holes, hb] using he
    | push _ hn _ run hplayer hb =>
      have hh := holes_push run hn hb
      rw [hh, Finset.mem_insert] at he
      rcases he with hq | he
      · subst p
        rw [hplayer] at hstay
        omega
      · exact Finset.mem_of_mem_erase he
  · refine ⟨r + 1, hnext, ?_⟩
    suffices (outside P a (r + 1) t).card + 1 ≤ (outside P a r s).card by omega
    cases hm with
    | walk hv _ _ he hb =>
      apply card_advance (p := t.player)
      · exact mem_outside.mpr ⟨(mem_holes _).mpr he, hp, by omega⟩
      · intro p hpm
        obtain ⟨he, hP, hd⟩ := mem_outside.mp hpm
        refine Finset.mem_erase.mpr ⟨?_, mem_outside.mpr ⟨?_, hP, by omega⟩⟩
        · intro heq
          subst p
          omega
        · simpa [mem_holes, hb] using he
    | @push n hv hn _ run hplayer hb =>
      let z := run.cell ⟨n + 1, by omega⟩
      have hz : r < distance a z := by
        by_contra h
        have hq := run_distance_le run a hs (by simpa [z] using Nat.le_of_not_gt h) 1
        rw [← hplayer] at hq
        omega
      have hzt : z ∉ holes t := by simp [mem_holes, hb, z]
      have hzP : z ∉ P := fun h => hzt (ht h)
      apply card_advance (p := z)
      · exact mem_outside.mpr ⟨(mem_holes _).mpr run.empty, hzP, hz⟩
      · intro p hpm
        obtain ⟨he, hP, hd⟩ := mem_outside.mp hpm
        refine Finset.mem_erase.mpr ⟨?_, mem_outside.mpr ⟨?_, hP, by omega⟩⟩
        · intro heq
          subst p
          exact hzt he
        · rw [holes_push run hn hb, Finset.mem_insert] at he
          rcases he with hq | he
          · subst p
            rw [hplayer] at hnext
            omega
          · exact Finset.mem_of_mem_erase he

/-- A segment that stays outside `P` after its starting point and preserves its holes. -/
def ExcursionStep (B : Board w h) (cap : Option ℕ) (P : Finset (Cell w h))
    (s t : State w h) : Prop :=
  Step B cap s t ∧ P ⊆ holes t ∧ t.player ∉ P

/-- The budget counts all holes outside `P`, with the starting hole removed. -/
theorem excursion_distance {B : Board w h} {cap : Option ℕ} {P : Finset (Cell w h)}
    {s t : State w h} (hr : Relation.ReflTransGen (ExcursionStep B cap P) s t) :
    distance s.player t.player ≤ ((holes s \ P).erase s.player).card := by
  suffices ∃ r, distance s.player t.player ≤ r ∧
      r + (outside P s.player r t).card ≤ ((holes s \ P).erase s.player).card by
    obtain ⟨r, hd, hc⟩ := this
    omega
  induction hr with
  | refl => exact ⟨0, by simp, by simp [outside_zero]⟩
  | tail _ hm ih =>
    obtain ⟨r, hd, hc⟩ := ih
    obtain ⟨d, hm'⟩ := hm.1
    obtain ⟨r', hd', hc'⟩ := move_budget hm' hm.2.1 hm.2.2 hd
    exact ⟨r', hd', hc'.trans hc⟩

/-- Legal steps retaining every hole of the specified region. -/
def PreservingStep (B : Board w h) (cap : Option ℕ) (P : Finset (Cell w h))
    (s t : State w h) : Prop := Step B cap s t ∧ P ⊆ holes t

private theorem preserving_reachable {B : Board w h} {cap : Option ℕ}
    {P : Finset (Cell w h)} {s t : State w h}
    (hr : Relation.ReflTransGen (PreservingStep B cap P) s t) : Reachable B cap s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail hm.1

/-- At any time the player is within the global outside-hole budget of the region. -/
theorem reachable_distance {B : Board w h} {cap : Option ℕ} {P : Finset (Cell w h)}
    {s t : State w h} (hr : Relation.ReflTransGen (PreservingStep B cap P) s t)
    (hP : P ⊆ holes s) (hp : s.player ∈ P) :
    ∃ a ∈ P, distance a t.player ≤ (holes s \ P).card := by
  suffices P ⊆ holes t ∧ ∃ a ∈ P, ∃ r, distance a t.player ≤ r ∧
      r + (outside P a r t).card ≤ (holes s \ P).card by
    obtain ⟨_, a, ha, r, hd, hc⟩ := this
    exact ⟨a, ha, by omega⟩
  induction hr with
  | refl =>
    refine ⟨hP, s.player, hp, 0, by simp, ?_⟩
    rw [outside_zero, Finset.erase_eq_of_notMem]
    · omega
    · simp [hp]
  | @tail u v hru hm ih =>
    obtain ⟨hu, a, ha, r, hd, hc⟩ := ih
    refine ⟨hm.2, ?_⟩
    by_cases hv : v.player ∈ P
    · refine ⟨v.player, hv, 0, by simp, ?_⟩
      have hcard : (holes v \ P).card = (holes s \ P).card := by
        rw [Finset.card_sdiff_of_subset hm.2, Finset.card_sdiff_of_subset hP]
        have hre : Reachable B cap s v := preserving_reachable (hru.tail hm)
        rw [card_holes_reachable hre]
      rw [outside_zero, Finset.erase_eq_of_notMem]
      · simpa using hcard.le
      · simp [hv]
    · obtain ⟨d, hmove⟩ := hm.1
      obtain ⟨r', hd', hc'⟩ := move_budget hmove hm.2 hv hd
      exact ⟨a, ha, r', hd', hc'.trans hc⟩

section Exits
variable {B : Board w h} {cap : Option ℕ} {P : Finset (Cell w h)} {E : Set (Cell w h)}
  {s u t : State w h} {R : State w h → State w h → Prop}
  (hstep : ∀ ⦃u v⦄, R u v → PreservingStep B cap P u v)
  (hexit : ∀ ⦃u v⦄, R u v → u.player ∈ P → v.player ∉ P → u.player ∈ E)

include hstep hexit

/-- Outside the permanent region, the radius budget starts at an actual departure cell.
The relation may carry additional geometric support facts identifying those departures. -/
theorem reachable_distance_from_exits
    (hr : Relation.ReflTransGen R s t) (hP : P ⊆ holes s) (hp : s.player ∈ P) :
    t.player ∈ P ∨ ∃ a ∈ E, distance a t.player ≤ (holes s \ P).card := by
  suffices P ⊆ holes t ∧ (t.player ∈ P ∨ ∃ a ∈ E, ∃ r,
      distance a t.player ≤ r ∧ r + (outside P a r t).card ≤ (holes s \ P).card) by
    rcases this with ⟨_, ht | ⟨a, ha, r, hd, hc⟩⟩
    · exact Or.inl ht
    · exact Or.inr ⟨a, ha, by omega⟩
  induction hr with
  | refl => exact ⟨hP, Or.inl hp⟩
  | @tail u v hru hm ih =>
    obtain ⟨hu, hu'⟩ := ih
    have hm' := hstep hm
    refine ⟨hm'.2, ?_⟩
    by_cases hv : v.player ∈ P
    · exact Or.inl hv
    · apply Or.inr
      obtain ⟨d, hmove⟩ := hm'.1
      rcases hu' with hinside | ⟨a, ha, r, hd, hc⟩
      · have ha := hexit hm hinside hv
        have hcard : (holes u \ P).card = (holes s \ P).card := by
          rw [Finset.card_sdiff_of_subset hu, Finset.card_sdiff_of_subset hP]
          exact congrArg (fun n => n - P.card) (card_holes_reachable (preserving_reachable
            (Relation.ReflTransGen.mono (fun _ _ h => hstep h) _ _ hru)))
        obtain ⟨r, hd, hc⟩ := move_budget (a := u.player) (r := 0) hmove hm'.2 hv
          (by simp)
        refine ⟨u.player, ha, r, hd, ?_⟩
        rw [outside_zero, Finset.erase_eq_of_notMem
          (show u.player ∉ holes u \ P by simp [hinside])] at hc
        simpa only [Nat.zero_add, hcard] using hc
      · obtain ⟨r', hd', hc'⟩ := move_budget hmove hm'.2 hv hd
        exact ⟨a, ha, r', hd', hc'.trans hc⟩

/-- A cell outside the permanent region and beyond every departure budget is unvisited. -/
theorem player_ne_distant_from_exits (hr : Relation.ReflTransGen R s t)
    (hP : P ⊆ holes s) (hp : s.player ∈ P) {g : Cell w h} (hgP : g ∉ P)
    (hg : ∀ a ∈ E, (holes s \ P).card < distance a g) : t.player ≠ g := by
  rcases reachable_distance_from_exits hstep hexit hr hP hp with ht | ⟨a, ha, hd⟩
  · exact fun he => hgP (he ▸ ht)
  · intro he
    rw [he] at hd
    have := hg a ha
    omega

/-- Distant required holes persist along a play whose departures use the specified exits. -/
theorem distant_hole_at_from_exits (hsu : Relation.ReflTransGen R s u)
    (hut : Relation.ReflTransGen R u t) (hP : P ⊆ holes s) (hp : s.player ∈ P)
    {g : Cell w h} (hgP : g ∉ P)
    (hg : ∀ a ∈ E, (holes s \ P).card < distance a g) (ht : g ∈ holes t) : g ∈ holes u := by
  induction hut with
  | refl => exact ht
  | tail huv hm ih =>
    have hne := player_ne_distant_from_exits hstep hexit (hsu.trans (huv.tail hm)) hP hp hgP hg
    exact ih (hole_source_of_ne_player (hstep hm).1.choose_spec (Ne.symm hne) ht)

/-- An initially occupied distant cell remains occupied throughout such a play. -/
theorem distant_box_from_exits (hr : Relation.ReflTransGen R s t)
    (hP : P ⊆ holes s) (hp : s.player ∈ P) {g : Cell w h}
    (hg : ∀ a ∈ E, (holes s \ P).card < distance a g) (hs : g ∈ s.boxes) : g ∈ t.boxes := by
  by_contra ht
  have hgP : g ∉ P := fun h => (mem_holes _).mp (hP h) hs
  have hh := distant_hole_at_from_exits hstep hexit .refl hr hP hp hgP hg ((mem_holes _).mpr ht)
  exact (mem_holes _).mp hh hs

end Exits

/-- A cell farther than the budget from every region cell is never visited. -/
theorem player_ne_distant {B : Board w h} {cap : Option ℕ}
    {P : Finset (Cell w h)} {s t : State w h} {g : Cell w h}
    (hr : Relation.ReflTransGen (PreservingStep B cap P) s t)
    (hP : P ⊆ holes s) (hp : s.player ∈ P)
    (hg : ∀ a ∈ P, (holes s \ P).card < distance a g) : t.player ≠ g := by
  obtain ⟨a, ha, hd⟩ := reachable_distance hr hP hp
  intro he
  rw [he] at hd
  have := hg a ha
  omega

/-- A far hole present at the endpoint was present before every preceding step. -/
theorem distant_hole_source {B : Board w h} {cap : Option ℕ}
    {P : Finset (Cell w h)} {s t : State w h} {g : Cell w h}
    (hr : Relation.ReflTransGen (PreservingStep B cap P) s t)
    (hP : P ⊆ holes s) (hp : s.player ∈ P)
    (hg : ∀ a ∈ P, (holes s \ P).card < distance a g)
    (ht : g ∈ holes t) : g ∈ holes s := by
  induction hr with
  | refl => exact ht
  | tail hru hm ih =>
    have hne := player_ne_distant (hru.tail hm) hP hp hg
    exact ih (hole_source_of_ne_player hm.1.choose_spec (Ne.symm hne) ht)

/-- Each intermediate state retains a distant endpoint hole. -/
theorem distant_hole_at {B : Board w h} {cap : Option ℕ}
    {P : Finset (Cell w h)} {s u t : State w h} {g : Cell w h}
    (hsu : Relation.ReflTransGen (PreservingStep B cap P) s u)
    (hut : Relation.ReflTransGen (PreservingStep B cap P) u t)
    (hP : P ⊆ holes s) (hp : s.player ∈ P)
    (hg : ∀ a ∈ P, (holes s \ P).card < distance a g)
    (ht : g ∈ holes t) : g ∈ holes u := by
  induction hut with
  | refl => exact ht
  | tail huv hm ih =>
    have hne := player_ne_distant (hsu.trans (huv.tail hm)) hP hp hg
    exact ih (hole_source_of_ne_player hm.1.choose_spec (Ne.symm hne) ht)

end Radius
end PushPuzzle.PushS
