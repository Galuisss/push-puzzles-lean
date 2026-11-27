/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Basic

/-! A fixed ordinary wall-free reject instance for checked total compilers. -/

public section
namespace PushPuzzle.Push.Fallback

open PushFS

/-- The only box fills the right cell of a two-cell row and cannot be pushed past its boundary. -/
@[expose] def reject : Push.Instance where
  width := 2
  height := 1
  initial := ⟨(0, 0), {(1, 0)}⟩
  target := (1, 0)
  player_empty := by decide

private theorem reject_empty : ∀ q : Cell 2 1,
    q ∉ reject.initial.boxes → q = reject.initial.player := by
  intro q he
  have hy : q.2 = (0 : Fin 1) := Fin.ext (by have := q.2.isLt; omega)
  have hx : q.1.val = 0 := by
    by_contra hn
    have hq : q = (1, 0) := Prod.ext (Fin.ext (by change q.1.val = 1; have := q.1.isLt; omega)) hy
    exact he (Finset.mem_singleton.mpr hq)
  exact Prod.ext (Fin.ext hx) hy

private theorem reject_no_step (t : State 2 1) (hm : Step reject.board none reject.initial t) : False := by
  obtain ⟨d, hm⟩ := hm
  cases hm with
  | walk _ ha _ he _ => exact ha.ne (reject_empty _ he).symm
  | @push n _ _ _ run _ _ =>
    have he : run.cell ⟨n + 1, by omega⟩ = run.cell 0 := (reject_empty _ run.empty).trans run.start.symm
    have hi := congrArg Fin.val (run.injective he)
    change n + 1 = 0 at hi
    omega

private theorem reject_reachable {t : State 2 1} (hr : Reachable reject.board none reject.initial t) :
    t = reject.initial := by
  induction hr with
  | refl => rfl
  | tail _ hm ih => exact False.elim (reject_no_step _ (ih ▸ hm))

/-- No actual walk or complete push can reach the ordinary destination in this fixed instance. -/
theorem reject_not_solvable : ¬ reject.Solvable := by
  rintro ⟨t, hr, hp⟩
  have ht := reject_reachable hr
  have hn : reject.initial.player ≠ reject.target := by decide
  exact hn ((congrArg State.player ht).symm.trans hp)

end PushPuzzle.Push.Fallback
