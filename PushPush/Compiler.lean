/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReaderCompiler
public import PushPush.SourceAcceptance

/-! Standard polynomial-time compilation of source door reachability to a single player target. -/

public section
namespace PushPuzzle.PushPush

open Cslib.Complexity Turing.MultiTapeTM

theorem exists_door_compile :
    ∃ compile : SelfClosingDoor.Instance → Instance,
      ComputableInPolyTime compile SelfClosingDoor.encInstance encoding ∧
        ∀ I, I ∈ SelfClosingDoor.Reachability ↔ Instance.Solvable (compile I) := by
  obtain ⟨compile, hpt, hcorrect⟩ := CyclicReader.compile_source_family Doors.Source.sourceFamily
    (by simp [Push.CyclicSchedule.Aligned, Doors.Source.readerShapes, Push.CyclicSchedule.nextSide])
    (by simp [Doors.Source.readerShapes])
  refine ⟨compile, hpt, fun I => ?_⟩
  exact ((hcorrect I).trans (Doors.Source.sourceFamily_language_iff_reachability I)).symm

noncomputable def compile : SelfClosingDoor.Instance → Instance := Classical.choose exists_door_compile

theorem compile_polyTime : ComputableInPolyTime compile SelfClosingDoor.encInstance encoding :=
  (Classical.choose_spec exists_door_compile).1

theorem compile_mem_iff (I : SelfClosingDoor.Instance) :
    I ∈ SelfClosingDoor.Reachability ↔ compile I ∈ solvable :=
  (Classical.choose_spec exists_door_compile).2 I

theorem polyTimeReducible_reachability :
    PolyTimeReducible SelfClosingDoor.encInstance encoding SelfClosingDoor.Reachability solvable :=
  ⟨compile, compile_polyTime, compile_mem_iff⟩

end PushPuzzle.PushPush
