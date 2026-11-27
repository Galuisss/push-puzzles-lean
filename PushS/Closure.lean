/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Freeze

/-! Iterated first-motion closure with both unvisited holes and already frozen boxes. -/

@[expose] public section
namespace PushPuzzle.PushS.Freeze

open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ}
  {G C : Finset (Cell w h)} {s t : State w h}

/-- A legal step whose complete push ray avoids every established blocker. -/
def AvoidingStep (B : Board w h) (cap : Option ℕ) (G : Finset (Cell w h))
    (s t : State w h) : Prop :=
  Step B cap s t ∧ ∀ (d : Direction) (n : ℕ) (run : Run B d s n), 0 < n →
    t.player = run.cell 1 →
    t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)) →
    ∀ i, run.cell i ∉ G

/-- Additional excluded holes can join the blockers of the identical actual step. -/
theorem AvoidingStep.union_excluded {H : Finset (Cell w h)}
    (hm : AvoidingStep B cap G s t) (hs : Blocked.Excluded H s) (ht : Blocked.Excluded H t) :
    AvoidingStep B cap (G ∪ H) s t := by
  refine ⟨hm.1, ?_⟩
  intro d n run hn hp hb i hi
  exact (Finset.mem_union.mp hi).elim (hm.2 d n run hn hp hb i)
    (Blocked.run_avoids run hs ht hb i)

private theorem step_enlarge (hanchor : Anchored C G) (hm : AvoidingStep B cap G s t)
    (hfull : C ⊆ s.boxes) : C ⊆ t.boxes ∧ AvoidingStep B cap (G ∪ C) s t := by
  have havoid (d : Direction) (n : ℕ) (run : Run B d s n) (hn : 0 < n)
      (hp : t.player = run.cell 1)
      (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
      (i : Fin (n + 2)) : run.cell i ∉ C :=
    run_avoids hanchor hm.1.choose_spec.valid_source hfull run (hm.2 d n run hn hp hb) i
  constructor
  · obtain ⟨d, hmove⟩ := hm.1
    cases hmove with
    | walk _ _ _ _ hb => simpa only [hb] using hfull
    | @push n _ hn _ run hp hb =>
      intro p hpC
      rw [hb]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨?_, hfull hpC⟩)
      intro he
      exact havoid d n run hn hp hb 1 (he ▸ hpC)
  · refine ⟨hm.1, ?_⟩
    intro d n run hn hp hb i hmem
    exact (Finset.mem_union.mp hmem).elim
      (hm.2 d n run hn hp hb i) (havoid d n run hn hp hb i)

/-- Freezing a full anchored region expands the blockers for the identical trajectory. -/
theorem anchored_closure (hanchor : Anchored C G)
    (hr : Relation.ReflTransGen (AvoidingStep B cap G) s t) (hfull : C ⊆ s.boxes) :
    C ⊆ t.boxes ∧ Relation.ReflTransGen (AvoidingStep B cap (G ∪ C)) s t := by
  induction hr with
  | refl => exact ⟨hfull, .refl⟩
  | tail _ hm ih =>
    obtain ⟨hu, hru⟩ := ih
    obtain ⟨ht, hm'⟩ := step_enlarge hanchor hm hu
    exact ⟨ht, hru.tail hm'⟩

/-- An initially full region can be attached after any previously certified closure. -/
inductive Closure (initial : State w h) : Finset (Cell w h) → Finset (Cell w h) → Prop
  | refl (G : Finset (Cell w h)) : Closure initial G G
  | add {G R C : Finset (Cell w h)} (previous : Closure initial G R) (full : C ⊆ initial.boxes)
      (anchored : Anchored C R) : Closure initial G (R ∪ C)

/-- A finite closure certificate excludes all newly attached boxes from every push. -/
theorem Closure.reachable {R : Finset (Cell w h)} (hc : Closure s G R)
    (hr : Relation.ReflTransGen (AvoidingStep B cap G) s t) :
    Relation.ReflTransGen (AvoidingStep B cap R) s t := by
  induction hc with
  | refl => exact hr
  | add _ hf ha ih => exact (anchored_closure ha ih hf).2

/-- A closure established along a prefix also guards its next actual step. -/
theorem Closure.step {R : Finset (Cell w h)} (hc : Closure s G R)
    {u v : State w h} (hr : Relation.ReflTransGen (AvoidingStep B cap G) s u)
    (hm : AvoidingStep B cap G u v) : AvoidingStep B cap R u v := by
  induction hc with
  | refl => exact hm
  | add previous hf ha ih =>
    exact (step_enlarge ha ih (anchored_closure ha (previous.reachable hr) hf).1).2

end PushPuzzle.PushS.Freeze
