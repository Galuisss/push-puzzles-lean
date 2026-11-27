/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.Corners
public import PushFS.Gadgets.Gates.Soundness.Relay.Arithmetic
public import PushFS.Gadgets.Gates.Soundness.Core

/-! Every core inward bit reaches the actual outermost owned boundary box on arbitrary successful paths. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph

open Relay Wires.Soundness
set_option maxHeartbeats 1000000

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {A : AxisTracks I}

/-- Every actual OR core signal propagates through its full guarded boundary rail. -/
private theorem or_core_to_ports (g : GateGlyph M A false)
    {S final : LabelledState L I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) :
    ((g.decode S).left=true → (S.position (g.labels 25)).1.val≤g.dx+2) ∧
    ((g.decode S).upper=true → (S.position (g.labels 65)).2.val≤g.dy+2) ∧
    ((g.decode S).right=false → g.dx+78≤(S.position (g.labels 77)).1.val) := by
  have hh:=or_signals g.dx g.dy (fun l=>(S.position (g.labels l)).1.val) (fun l=>(S.position (g.labels l)).2.val)
    (fun p hp=>g.rail_gap h cert .main p hp) (fun p hp=>g.rail_gap h cert .upper p hp)
    (g.checked_flip_signal h cert ho (westSpec false) (west_checked false))
    (g.checked_flip_signal h cert ho (eastSpec false) (east_checked false))
    (g.checked_flip_signal h cert ho (upperSpec false) (upper_checked false))
  refine ⟨?_,?_,?_⟩
  · intro hb
    exact hh.1 (of_decide_eq_true hb)
  · intro hb
    exact hh.2.1 (of_decide_eq_true hb)
  · intro hb
    have hn : ¬(S.position (g.labels 4)).1.val≤g.dx+44+3 := of_decide_eq_false hb
    apply hh.2.2
    omega

/-- The AND input signal traverses both protected corners, the real V39 flip and every true long rail. -/
private theorem and_core_to_ports (g : GateGlyph M A true)
    {S final : LabelledState L I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) :
    ((g.decode S).left=true → (S.position (g.labels 54)).1.val≤g.dx+1) ∧
    ((g.decode S).upper=true → (S.position (g.labels 94)).2.val≤g.dy+2) ∧
    ((g.decode S).right=false → g.dx+79≤(S.position (g.labels 107)).1.val) := by
  have hh:=and_signals g.dx g.dy (fun l=>(S.position (g.labels l)).1.val) (fun l=>(S.position (g.labels l)).2.val)
    (fun p hp=>g.rail_gap h cert .main p hp) (fun p hp=>g.rail_gap h cert .upper p hp)
    (fun p hp=>g.rail_gap h cert .incoming p hp) (fun p hp=>g.rail_gap h cert .west p hp)
    (g.lower_turn h cert ho) (g.upper_turn h cert ho)
    (g.checked_flip_signal h cert ho fanoutSpec fanout_checked)
    (g.checked_flip_signal h cert ho (westSpec true) (west_checked true))
    (g.checked_flip_signal h cert ho (eastSpec true) (east_checked true))
    (g.checked_flip_signal h cert ho (upperSpec true) (upper_checked true))
  refine ⟨?_,?_,?_⟩
  · intro hb
    exact hh.1 (of_decide_eq_true hb)
  · intro hb
    exact hh.2.1 (of_decide_eq_true hb)
  · intro hb
    have hn : ¬(S.position (g.labels 4)).1.val≤g.dx+43+3 := of_decide_eq_false hb
    apply hh.2.2
    omega

variable {kind : Bool} (g : GateGlyph M A kind)

/-- The actual outermost boxes read inward at west/north and outward at east. -/
def boundarySignal (S : LabelledState L I.width I.height) : Fin 3→Bool :=
  ![decide ((S.position (g.labels (outerLabel kind 0))).1.val≤g.dx+(if kind then 1 else 2)),
    decide ((S.position (g.labels (outerLabel kind 1))).2.val≤g.dy+2),
    decide (g.dx+(if kind then 79 else 78)≤(S.position (g.labels (outerLabel kind 2))).1.val)]

/-- The three true logical inward bits selected from the core trigger identities. -/
def coreInward (S : LabelledState L I.width I.height) : Fin 3→Bool :=
  ![(g.decode S).left,(g.decode S).upper,!(g.decode S).right]

/-- Each actual core inward signal forces the corresponding boundary endpoint threshold on a successful path. -/
theorem core_to_boundary {S final : LabelledState L I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (i : Fin 3) :
    g.coreInward S i=true → g.boundarySignal S i=true := by
  cases kind
  · obtain ⟨ha,hb,hc⟩:=g.or_core_to_ports h cert ho
    fin_cases i
    · exact fun hh=>decide_eq_true (ha hh)
    · exact fun hh=>decide_eq_true (hb hh)
    · intro hh
      change (!(g.decode S).right)=true at hh
      exact decide_eq_true (hc (by simpa only [Bool.not_eq_true'] using hh))
  · obtain ⟨ha,hb,hc⟩:=g.and_core_to_ports h cert ho
    fin_cases i
    · exact fun hh=>decide_eq_true (ha hh)
    · exact fun hh=>decide_eq_true (hb hh)
    · intro hh
      change (!(g.decode S).right)=true at hh
      exact decide_eq_true (hc (by simpa only [Bool.not_eq_true'] using hh))

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph
