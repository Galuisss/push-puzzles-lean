/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Closure
public import PushS.Labels

/-! Physical box identities fixed by finite iterated first-motion certificates. -/

@[expose] public section
namespace PushPuzzle.PushS.Labels

open PushFS

variable {w h : ℕ} {ι : Type} [Fintype ι] {B : Board w h} {cap : Option ℕ}
  {G : Finset (Cell w h)} {S T : LabelledState ι w h}

/-- A labelled move carrying the established blocker avoidance certificate. -/
def GuardedStep (B : Board w h) (cap : Option ℕ) (G : Finset (Cell w h))
    (S T : LabelledState ι w h) : Prop :=
  MultiStep B cap S T ∧ Freeze.AvoidingStep B cap G S.state T.state

/-- A full physical trajectory retaining its blockers at every push. -/
abbrev GuardedReachable (B : Board w h) (cap : Option ℕ) (G : Finset (Cell w h)) :=
  Relation.ReflTransGen (GuardedStep (ι := ι) B cap G)

/-- Every initially present physical box in the blocker region keeps its exact position. -/
theorem GuardedReachable.position (hr : GuardedReachable B cap G S T)
    (i : ι) (hi : S.position i ∈ G) : T.position i = S.position i := by
  induction hr with
  | refl => rfl
  | @tail U V _ hm ih =>
    have hiU : U.position i ∈ G := ih.symm ▸ hi
    have hpos : V.position i = U.position i := by
      obtain ⟨d, hmove⟩ := hm.1
      cases hmove with
      | walk _ _ _ _ _ hpositions => exact congrFun hpositions i
      | @push n _ hn _ run hp hb hpositions =>
        apply position_eq_of_not_in_run run hpositions i
        intro j he
        exact hm.2.2 d n run hn hp hb j (he ▸ hiU)
    exact hpos.trans ih

/-- Lift a trajectory with blockers without changing its states or its push cap. -/
theorem lift_guarded {t : State w h}
    (hr : Relation.ReflTransGen (Freeze.AvoidingStep B cap G) S.state t) :
    ∃ T : LabelledState ι w h, T.state = t ∧ GuardedReachable B cap G S T := by
  induction hr with
  | refl => exact ⟨S, rfl, .refl⟩
  | tail _ hm ih =>
    obtain ⟨U, hu, hru⟩ := ih
    obtain ⟨V, hv, hstep⟩ := lift_step U (hu ▸ hm.1)
    have hg : Freeze.AvoidingStep B cap G U.state V.state := by
      simpa only [hu, hv] using hm
    exact ⟨V, hv, hru.tail ⟨hstep, hg⟩⟩

end PushPuzzle.PushS.Labels
