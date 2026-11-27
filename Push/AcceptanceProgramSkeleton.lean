/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgram
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The actual multilevel emitter has one fixed read/clear side skeleton at each level allocation. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- A compact round's read/clear tag and physical side; true denotes a read. -/
@[expose] def Round.shape : Round → Bool × Direction
  | .read side _ => (true, side)
  | .clear side _ => (false, side)

/-- The corresponding tag and side of a literal coordinate template. -/
@[expose] def Template.shape : Template → Bool × Direction
  | .read side _ => (true, side)
  | .clear side _ => (false, side)

/-- The actual complete acceptance schedule, retaining only its fixed same-direction blocks. -/
@[expose] def skeleton (levels : ℕ) : List (Bool × Direction) :=
  [(true, .south), (true, .west), (false, .north), (true, .south), (true, .north),
    (false, .west), (true, .north), (true, .south), (false, .west), (true, .south),
    (true, .east), (true, .north), (true, .west),
    (true, .west), (false, .east), (true, .north), (false, .north), (false, .west),
    (true, .north), (true, .south), (false, .north), (true, .south), (true, .east),
    (true, .west), (false, .north)] ++
  [(true, .south), (true, .west), (false, .north)] ++
  (List.range (levels - 1)).flatMap (fun _ => [(true, .west), (true, .south)]) ++
  [(false, .north)] ++
  (List.range (levels - 1)).flatMap (fun _ => [(true, .west), (false, .north)])

/-- Target-dependent quota emission leaves the whole compact round skeleton unchanged. -/
theorem emit_shapes {w h : ℕ} (stages : List Template) (E : Finset (Cell w h)) :
    (emit stages E).rounds.map Round.shape = stages.map Template.shape := by
  induction stages generalizing E with
  | nil => rfl
  | cons stage stages ih =>
    cases stage <;> simp only [emit, List.map_cons, Round.shape, Template.shape, ih]

/-- Every actual marked layout uses exactly the same schedule skeleton at its level allocation. -/
private theorem schedule_shapes (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    (schedule l p k).map Template.shape = skeleton p.levels := by
  simp only [schedule, preparation, frameSchedule, pageChecks, mainTop, mainBottom, trimRound,
    lowerFinish, readRows, readColumns, Template.shape, skeleton, List.map_append, List.map_cons,
    List.map_nil, List.map_flatMap, List.append_assoc, List.cons_append, List.nil_append,
    reduceCtorEq, ite_true, ite_false]

/-- The actual complete program has a target- and layout-independent read/clear side skeleton. -/
theorem program_shapes (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    (program l p target).rounds.map Round.shape = skeleton p.levels := by
  rw [program, emit_shapes, schedule_shapes]

end PushPuzzle.Push.AcceptanceProgram
