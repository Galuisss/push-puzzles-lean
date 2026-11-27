/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicTwoRoundCompleteness
public import Push.CyclicTwoRoundSoundness
public import Push.CyclicNextPolyTime

/-! Complete physical correctness and standard PT of the actual two-round reader. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS Turing.MultiTapeTM

/-- The actual two-stage player target tests the exact two rounds on one reachable source corner state. -/
theorem twoRound_solvable_iff (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles) :
    (nextInput r rows hlen hb).compile.Solvable ↔
      ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
        s.player = r.sourceCorner ∧ Scan.Accepts (twoRoundProgram r rows) (holes s) := by
  constructor
  · exact twoRound_sound r rows hlen hb
  · rintro ⟨s, hr, hp, hprogram⟩
    exact twoRound_complete r rows hlen hb hr hp hprogram

/-- Complete bitmap generation of the two-round physical player-target instance is standard PT. -/
@[fun_prop] theorem twoRound_compile_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {rows : α → List ℕ}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime rows enc (encList encUnary))
    (hlen : ∀ a, (rows a).length = (reader a).height)
    (hb : ∀ a, (rows a).sum ≤ (reader a).sourceHoles) :
    ComputableInPolyTime (fun a => (nextInput (reader a) (rows a) (hlen a) (hb a)).compile)
      enc Push.encoding :=
  ColumnScan.Input.compile_polyTime.comp (nextInput_polyTime hr hq hlen hb)

end PushPuzzle.Push.Cyclic
