/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderSource
public import Push.AcceptanceProgramBoundedPolyTime

/-! Complete standard PT compilation of reference-accepted fixed-round source programs. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicReader

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM

/-- An actual computed source/program family whose reference target pays the complete fixed-shape word. -/
structure ProgramFamily (α : Type) (enc : α ↪ List Bool) (shapes : List (Bool × Direction)) where
  source : α → Push.Instance
  rounds : α → List Round
  source_polyTime : ComputableInPolyTime source enc Push.encoding
  rounds_polyTime : ComputableInPolyTime rounds enc encRounds
  shapes_eq : ∀ a, (rounds a).map Round.shape = (true, .south) :: (true, .west) :: shapes
  reference_accepts : ∀ a, ∃ E : Finset (Cell (source a).width (source a).height),
    Scan.Accepts (instructions (rounds a)) E
  budget : ∀ a, Scan.quota (instructions (w := (source a).width) (h := (source a).height) (rounds a)) ≤
    (holes (source a).initial).card
  first_height : ∀ a, (source a).height ≤
    ((firstRequests (boundedRounds (source a).width (source a).height (rounds a))).map Prod.snd).sum
  target_x : ∀ a, (source a).target.1.val + 1 = (source a).width
  target_y : ∀ a, (source a).target.2.val + 1 = (source a).height

namespace ProgramFamily

variable {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
  (F : ProgramFamily α enc shapes)

/-- The same complete source program restricted to actual finite rectangle lanes. -/
def normalized (a : α) : List Round := boundedRounds (F.source a).width (F.source a).height (F.rounds a)

@[fun_prop] theorem normalized_polyTime : ComputableInPolyTime F.normalized enc encRounds :=
  boundedRounds_polyTime
    (PushFS.Machine.width_polyTime.comp (Push.Machine.toStorage_polyTime.comp F.source_polyTime))
    (PushFS.Machine.height_polyTime.comp (Push.Machine.toStorage_polyTime.comp F.source_polyTime))
    F.rounds_polyTime

private theorem normalized_shapes (a : α) : (F.normalized a).map Round.shape =
    (true, .south) :: (true, .west) :: shapes :=
  (boundedRounds_shapes ..).trans (F.shapes_eq a)

theorem normalized_read (a : α) :
    F.normalized a = .read .south (firstRequests (F.normalized a)) :: (F.normalized a).tail ∧
      (F.normalized a).tail.map Round.shape = (true, .west) :: shapes :=
  read_cons_of_shapes _ _ _ (F.normalized_shapes a)

private theorem normalized_eval (a : α) (E : Finset (Cell (F.source a).width (F.source a).height)) :
    Scan.eval (instructions (F.normalized a)) E = Scan.eval (instructions (F.rounds a)) E := by
  obtain ⟨reference, result, he⟩ := F.reference_accepts a
  exact boundedRounds_eval _ he E

theorem normalized_quota (a : α) :
    Scan.quota (instructions (w := (F.source a).width) (h := (F.source a).height) (F.normalized a)) =
      Scan.quota (instructions (w := (F.source a).width) (h := (F.source a).height) (F.rounds a)) := by
  obtain ⟨reference, result, he⟩ := F.reference_accepts a
  exact boundedRounds_quota _ he

/-- Reference acceptance gives the complete actual-lane source family without extra geometric lane hypotheses. -/
def toSource : SourceFamily α enc shapes where
  source := F.source
  requests a := firstRequests (F.normalized a)
  rounds a := (F.normalized a).tail
  source_polyTime := F.source_polyTime
  requests_polyTime := firstRequests_polyTime.comp F.normalized_polyTime
  rounds_polyTime := by
    have hr := F.normalized_polyTime
    unfold encRounds
    fun_prop
  shapes_eq a := (F.normalized_read a).2
  requests_bounded a request hr := by
    have hb := boundedRounds_bounded (F.source a).width (F.source a).height (F.rounds a)
    apply hb (.read .south request.1 request.2)
    change Scan.Instruction.read .south request.1 request.2 ∈ instructions (F.normalized a)
    rw [(F.normalized_read a).1]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨request, hr, rfl⟩)
  rounds_bounded a i hi := by
    apply boundedRounds_bounded (F.source a).width (F.source a).height (F.rounds a) i
    change i ∈ instructions (F.normalized a)
    rw [(F.normalized_read a).1]
    exact List.mem_append_right _ hi
  budget a := by
    have hq := F.normalized_quota a
    rw [(F.normalized_read a).1] at hq
    change Scan.quota (Scan.lines .south (firstRequests (F.normalized a)) ++
      instructions (w := (F.source a).width) (h := (F.source a).height) (F.normalized a).tail) = _ at hq
    rw [Scan.quota_append, Scan.lines_quota] at hq
    exact hq ▸ F.budget a
  first_height := F.first_height
  target_x := F.target_x
  target_y := F.target_y

/-- Reach the literal source destination with any source bitmap accepted by the original computed program. -/
def Language (a : α) : Prop := ∃ s : State (F.source a).width (F.source a).height,
  Reachable (F.source a).board none (F.source a).initial s ∧ s.player = (F.source a).target ∧
    Scan.Accepts (instructions (F.rounds a)) (holes s)

private theorem toSource_language_iff (a : α) : F.toSource.Language a ↔ F.Language a := by
  have haccept (E : Finset (Cell (F.source a).width (F.source a).height)) :
      Scan.Accepts (Scan.lines .south (firstRequests (F.normalized a)) ++
        instructions (F.normalized a).tail) E ↔ Scan.Accepts (instructions (F.rounds a)) E := by
    have hi := congrArg (instructions (w := (F.source a).width) (h := (F.source a).height))
      (F.normalized_read a).1
    have hi' : instructions (w := (F.source a).width) (h := (F.source a).height) (F.normalized a) =
        Scan.lines .south (firstRequests (F.normalized a)) ++ instructions (F.normalized a).tail := hi
    rw [← hi']
    simp only [Scan.Accepts, F.normalized_eval a]
  constructor
  · rintro ⟨s, hr, hp, ha⟩
    exact ⟨s, hr, hp, (haccept _).mp ha⟩
  · rintro ⟨s, hr, hp, ha⟩
    exact ⟨s, hr, hp, (haccept _).mpr ha⟩

/-- Actual fixed-round source programs compile to one ordinary player-target puzzle in standard polynomial time. -/
theorem compile (F : ProgramFamily α enc shapes) :
    ∃ compile : α → Push.Instance, ComputableInPolyTime compile enc Push.encoding ∧
      ∀ a, (compile a).Solvable ↔ F.Language a := by
  obtain ⟨compile, hpt, hcorrect⟩ := F.toSource.compile
  exact ⟨compile, hpt, fun a => (hcorrect a).trans (F.toSource_language_iff a)⟩

end ProgramFamily
end PushPuzzle.Push.CyclicReader
