/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardSource

/-! The actual storage cleanup chain forgets every stable source bit. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

/-- Exact inventory after erasing the first `cleared` original door registers. -/
private def cleanupStock (I : Instance) (bits : List Bool) (cleared : ℕ) : Stock I where
  register := fun i => if i.val < cleared then .erase else Register.stable (bits.getD i.val false)
  signal := atRow true I (if cleared = 0 then targetRow I else doorBase (cleared - 1) + 69)

/-- One concrete cleanup wire and collision erase the next door, independently of its bit. -/
private theorem cleanup_step (I : Instance) (hwire : WireSimulation true I) (bits : List Bool)
    (n : ℕ) (hn : n < I.doors.length) :
    Finite.Reachable 1 ((cleanupStock I bits n).canonical true)
      ((cleanupStock I bits (n + 1)).canonical true) := by
  let i : Fin I.doors.length := ⟨n, hn⟩
  let current := cleanupStock I bits n
  have hcurrent : current.register i = Register.stable (bits.getD n false) := by
    simp [current, cleanupStock, i]
  have hne : current.register i ≠ Register.erase := by
    rw [hcurrent]
    cases bits.getD n false <;> decide
  let entered : Stock I := {current with signal := atRow true I (doorBase n + 70)}
  have hw : Finite.Reachable 1 (current.canonical true) (entered.canonical true) :=
    hwire current ⟨if n = 0 then targetRow I else doorBase (n - 1) + 69,
      decide (n = 0), doorBase n + 70, true⟩ (cleanup_wire_mem I i) rfl
      (current.door_input_ready true i .erase hne)
  have hc := entered.collide true i .erase hne rfl
  have hrow : collisionRow (entered.register i) .erase = 69 := by
    change collisionRow (current.register i) .erase = 69
    rw [hcurrent]
    cases bits.getD n false <;> rfl
  let next : Stock I := {(entered.setRegister i .erase) with signal := atRow true I (doorBase n + 69)}
  have hc' : Finite.Reachable 1 (entered.canonical true) (next.canonical true) := by
    simpa only [hrow, next, i, atRow] using hc
  have heq : next = cleanupStock I bits (n + 1) := by
    apply Stock.eq_of_register_signal
    · funext j
      by_cases hji : j = i
      · subst j
        simp [next, Stock.setRegister, cleanupStock, i]
      · have hval : j.val ≠ n := by intro he; exact hji (Fin.ext he)
        have hlt : j.val < n + 1 ↔ j.val < n := by omega
        simp only [next, Stock.setRegister, Function.update_of_ne hji,
          entered, current, cleanupStock, hlt]
    · simp [next, cleanupStock, atRow]
  rw [← heq]
  exact hw.trans hc'

private theorem storage_stop (I : Instance) :
    (layout true I).stop = if I.doors.length = 0 then targetRow I else doorBase (I.doors.length - 1) + 69 := by
  change (if true && decide (0 < I.doors.length) then _ else _) = _
  by_cases hz : I.doors.length = 0
  · simp [hz]
  · have hp : 0 < I.doors.length := by omega
    simp [hp, hz]

private theorem cleanup_terminal (I : Instance) (bits : List Bool) :
    cleanupStock I bits I.doors.length = Stock.terminal true I := by
  apply Stock.eq_of_register_signal
  · funext i
    simp [cleanupStock, Stock.terminal]
  · change atRow true I (if I.doors.length = 0 then targetRow I else doorBase (I.doors.length - 1) + 69) =
      ((layout true I).rackX - 1, (layout true I).stop + (layout true I).shift)
    rw [storage_stop]
    rfl

/-- After reaching the source target, all stable configurations converge to one exact box goal. -/
private theorem cleanup_run (I : Instance) (hwire : WireSimulation true I) (bits : List Bool) :
    Finite.Reachable 1 ((cleanupStock I bits 0).canonical true) ((Stock.terminal true I).canonical true) := by
  have hr : ∀ n, n ≤ I.doors.length →
      Finite.Reachable 1 ((cleanupStock I bits 0).canonical true) ((cleanupStock I bits n).canonical true) := by
    intro n hn
    induction n with
    | zero => exact .refl
    | succ n ih => exact (ih (by omega)).trans (cleanup_step I hwire bits n (by omega))
  rw [← cleanup_terminal I bits]
  exact hr I.doors.length le_rfl

/-- Park at the real target endpoint and execute the entire exact-storage cleanup. -/
private theorem encodedState_to_goals (I : Instance) (hwire : WireSimulation true I)
    (s : State) (port : ℕ) (htarget : s.location = I.target) (hport : port < slots I) :
    Finite.Reachable 1 ((encodedState true I s port).canonical true) ((Stock.terminal true I).canonical true) := by
  let current := encodedState true I s port
  have hused : upperUsed I (rank I I.target) 0 = true := by simp [upperUsed]
  have hs : current.signal = atRow true I (inputRow I (rank I I.target) 0 port) := by
    simp only [current, encodedState, Stock.ofBits, htarget]
  have hp := current.junction_upper_single true (rank I I.target) 0 port
    (rank_bound I (target_mem I)) (slots_pos I) hport hused hs
  have heq : ({current with signal := atRow true I (upperRow I (rank I I.target) 0)} : Stock I) =
      cleanupStock I s.bits 0 := by
    apply Stock.eq_of_register_signal
    · funext i
      simp [current, encodedState, Stock.ofBits, cleanupStock]
    · rfl
  rw [heq] at hp
  exact hp.trans (cleanup_run I hwire s.bits)

/-- Every source YES instance has a complete maximum-slide exact-storage solution. -/
theorem puzzle_forward (I : Instance) (hwire : WireSimulation true I)
    (hs : I ∈ Cslib.Complexity.SelfClosingDoor.Reachability) :
    ∃ t, Finite.Reachable 1 (puzzle true I).initial t ∧ t.boxes = (puzzle true I).board.goals := by
  obtain ⟨s, port, ht, hp, hr⟩ := encodedState_reaches_target true I hwire hs
  exact ⟨(Stock.terminal true I).canonical true,
    hr.trans (encodedState_to_goals I hwire s port ht hp), Stock.terminal_boxes true I⟩

end PushPuzzle.PushPush.Doors.Source
