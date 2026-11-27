/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Single
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Replay of concrete single-box movement certificates

A constant-size wall predicate gives executable lookup without enumerating the
whole rectangle. Soundness connects every checked direction to the actual
single-box semantics and retains exact player positions.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

/-- The neighboring cell, with failure at the boundary and no modular wraparound. -/
def neighbor (d : Direction) (p : Cell w h) : Option (Cell w h) :=
  match d with
  | .north => if hy : 0 < p.2.val then some (p.1, ⟨p.2.val - 1, by omega⟩) else none
  | .east => if hx : p.1.val + 1 < w then some (⟨p.1.val + 1, hx⟩, p.2) else none
  | .south => if hy : p.2.val + 1 < h then some (p.1, ⟨p.2.val + 1, hy⟩) else none
  | .west => if hx : 0 < p.1.val then some (⟨p.1.val - 1, by omega⟩, p.2) else none

theorem neighbor_sound {d : Direction} {p q : Cell w h}
    (hn : neighbor d p = some q) : Adjacent d p q := by
  cases d <;> simp only [neighbor] at hn <;> split_ifs at hn
  all_goals obtain rfl := Option.some.inj hn
  all_goals simp [Adjacent]
  all_goals omega

theorem neighbor_complete {d : Direction} {p q : Cell w h}
    (ha : Adjacent d p q) : neighbor d p = some q := by
  have hex : ∃ r, neighbor d p = some r := by
    cases d <;> simp only [Adjacent] at ha <;>
      simp only [neighbor] <;> split_ifs <;> simp_all <;> omega
  obtain ⟨r, hr⟩ := hex
  have heq := ha.functional (neighbor_sound hr)
  simpa [heq] using hr

namespace Execution

/-- Legality with respect to an executable wall predicate. -/
def valid (wall : Cell w h → Bool) (s : State w h) : Bool :=
  !wall s.player && @decide (∀ p ∈ s.boxes, wall p = false) Finset.decidableDforallFinset &&
    decide (s.player ∉ s.boxes)

/-- Perform one direction, with an empty neighboring cell or a single box. -/
def perform (wall : Cell w h → Bool) (d : Direction) (s : State w h) : Option (State w h) := do
  let p ← neighbor d s.player
  if wall p then none
  else if p ∈ s.boxes then do
    let q ← neighbor d p
    if wall q || decide (q ∈ s.boxes) then none
    else some ⟨p, insert q (s.boxes.erase p)⟩
  else some ⟨p, s.boxes⟩

/-- Replay a finite direction list, failing at the first blocked step. -/
def execute (wall : Cell w h → Bool) (s : State w h) : List Direction → Option (State w h)
  | [] => some s
  | d :: ds => (perform wall d s).bind fun t => execute wall t ds

/-- Check exact final player position and equality of the complete box sets. -/
def check (wall : Cell w h → Bool) (s t : State w h) (ds : List Direction) : Bool :=
  match execute wall s ds with
  | none => false
  | some u => decide (u.player = t.player ∧ u.boxes ⊆ t.boxes ∧ t.boxes ⊆ u.boxes)

theorem valid_correct {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (s : State w h) :
    valid wall s = true ↔ s.Valid B := by
  simp only [valid, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, State.Valid]
  have he : ∀ p, wall p = false ↔ p ∉ B.walls := by
    intro p
    rw [← hw p]
    exact Bool.eq_false_iff
  simp only [he]
  rw [Finset.disjoint_left]
  tauto

/-- Every accepted executable step is a real single-box move. -/
theorem perform_sound {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) {d : Direction} {s t : State w h}
    (hs : s.Valid B) (hm : perform wall d s = some t) : Move B (some 1) d s t := by
  apply Move.single_iff.mpr
  cases hp : neighbor d s.player with
  | none => simp [perform, hp] at hm
  | some p =>
    by_cases hwp : wall p = true
    · simp [perform, hp, hwp] at hm
    · have hpw : p ∉ B.walls := fun h => hwp ((hw p).mpr h)
      by_cases hb : p ∈ s.boxes
      · cases hq : neighbor d p with
        | none => simp [perform, hp, hwp, hb, hq] at hm
        | some q =>
          by_cases he : wall q = true ∨ q ∈ s.boxes
          · simp [perform, hp, hwp, hb, hq, Bool.or_eq_true, he] at hm
          · have hqw : wall q = false := Bool.eq_false_iff.mpr (fun h => he (Or.inl h))
            have hqe : q ∉ s.boxes := fun h => he (Or.inr h)
            simp only [perform, hp, hwp, hb, hq, hqw, hqe, decide_false, Bool.false_or,
              bind, Option.bind, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hm
            subst t
            exact SingleMoveView.push hs (neighbor_sound hp) hb (neighbor_sound hq)
              (fun h => he (Or.inl ((hw q).mpr h))) hqe
      · simp only [perform, hp, hwp, hb, bind, Option.bind, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hm
        subst t
        exact SingleMoveView.walk hs (neighbor_sound hp) hpw hb

/-- Successful replay yields the full semantic trajectory, including walking. -/
private theorem execute_sound {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) {s t : State w h} {ds : List Direction}
    (hs : s.Valid B) (he : execute wall s ds = some t) : Reachable B (some 1) s t := by
  induction ds generalizing s with
  | nil =>
    simp only [execute, Option.some.injEq] at he
    subst t
    exact .refl
  | cons d ds ih =>
    simp only [execute] at he
    cases hm : perform wall d s with
    | none => simp [hm] at he
    | some u =>
      simp only [hm, Option.bind_some] at he
      have hmove := perform_sound hw hs hm
      exact (Relation.ReflTransGen.single ⟨d, hmove⟩).trans (ih hmove.valid_target he)

theorem check_correct (wall : Cell w h → Bool) (s t : State w h) (ds : List Direction) :
    check wall s t ds = true ↔ execute wall s ds = some t := by
  cases he : execute wall s ds with
  | none => simp [check, he]
  | some u =>
    simp only [check, he, decide_eq_true_eq, Option.some.injEq]
    constructor
    · rintro ⟨hp, hst, hts⟩
      exact State.ext hp (Finset.Subset.antisymm hst hts)
    · rintro rfl
      exact ⟨rfl, Finset.Subset.refl _, Finset.Subset.refl _⟩

/-- A checked finite certificate is a genuine trajectory on the specified board. -/
theorem sound {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) {s t : State w h} {ds : List Direction}
    (hs : valid wall s = true) (hc : check wall s t ds = true) : Reachable B (some 1) s t :=
  execute_sound hw ((valid_correct hw s).mp hs) ((check_correct wall s t ds).mp hc)

end Execution
end PushPuzzle.PushFS
