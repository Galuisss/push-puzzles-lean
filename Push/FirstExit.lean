/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import CslibFrontier.Init
public import Mathlib.Logic.Relation

/-! First-exit decomposition of finite paths, retaining the entire preceding invariant. -/

public section
namespace PushPuzzle.Push.Path

/-- Enrich each edge using its actual prefix and suffix in the chosen finite path. -/
theorem enrich {α : Type*} {R Q : α → α → Prop} {s t : α}
    (hr : Relation.ReflTransGen R s t)
    (h : ∀ u v, Relation.ReflTransGen R s u → R u v → Relation.ReflTransGen R v t → Q u v) :
    Relation.ReflTransGen Q s t := by
  induction hr with
  | refl => exact .refl
  | @tail u v hsu hm ih =>
    exact (ih fun a b hsa hab hbu => h a b hsa hab (hbu.tail hm)).tail (h u v hsu hm .refl)

/-- Split a finite path at its first state outside a predicate. -/
theorem first_exit {α : Type*} {R : α → α → Prop} {P : α → Prop} {s t : α}
    (hr : Relation.ReflTransGen R s t) (hs : P s) (ht : ¬P t) :
    ∃ u v, Relation.ReflTransGen (fun a b => R a b ∧ P b) s u ∧ P u ∧
      R u v ∧ ¬P v ∧ Relation.ReflTransGen R v t := by
  classical
  have hsplit : (Relation.ReflTransGen (fun a b => R a b ∧ P b) s t ∧ P t) ∨
      ∃ u v, Relation.ReflTransGen (fun a b => R a b ∧ P b) s u ∧ P u ∧
        R u v ∧ ¬P v ∧ Relation.ReflTransGen R v t := by
    clear ht
    induction hr with
    | refl => exact Or.inl ⟨.refl, hs⟩
    | @tail u v _ hm ih =>
      rcases ih with ⟨hp, hu⟩ | ⟨a, b, hp, ha, hab, hb, hbu⟩
      · by_cases hv : P v
        · exact Or.inl ⟨hp.tail ⟨hm, hv⟩, hv⟩
        · exact Or.inr ⟨u, v, hp, hu, hm, hv, .refl⟩
      · exact Or.inr ⟨a, b, hp, ha, hab, hb, hbu.tail hm⟩
  exact hsplit.resolve_left (fun h => ht h.2)

end PushPuzzle.Push.Path
