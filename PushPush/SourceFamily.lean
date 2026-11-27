/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.CyclicFamily
public import PushPush.BlockLanguage
public import PushPush.Doors.QuotasShapeChecks
public import PushPush.Doors.QuotasWholeForward
public import PushPush.WholeBlockExact

/-! The literal seven-round door work board is a standard polynomial-time source family. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell State Direction)
open Push.AcceptanceProgram Push.CyclicReader
open Cslib.Complexity Turing.MultiTapeTM

def readerShapes : List (Bool × Direction) :=
  [(true, .north), (true, .east), (true, .south), (true, .west), (true, .north)]

theorem reader_decomposition (I : Instance) :
    readerRounds I = .read .south (firstRequests (readerRounds I)) :: (readerRounds I).tail ∧
      (readerRounds I).tail.map Round.shape = (true, .west) :: readerShapes :=
  read_cons_of_shapes _ _ _ (readerRounds_shapes I)

def sourceFamily : SourceFamily Instance SelfClosingDoor.encInstance readerShapes where
  source := readerSource
  requests I := firstRequests (readerRounds I)
  rounds I := (readerRounds I).tail
  source_polyTime := readerSource_polyTime
  requests_polyTime := firstRequests_polyTime.comp readerRounds_polyTime
  rounds_polyTime := by
    have h := readerRounds_polyTime
    unfold encRounds
    fun_prop
  shapes_eq I := (reader_decomposition I).2
  requests_bounded I a ha := by
    apply readerRounds_read_bounded I .south (firstRequests (readerRounds I)) ?_ a ha
    rw [(reader_decomposition I).1]
    exact List.mem_cons_self ..
  rounds_bounded I i hi := by
    apply readerRounds_bounded I i
    rw [(reader_decomposition I).1]
    exact List.mem_append_right _ hi
  budget I := by
    have h := readerRounds_budget I
    rw [(reader_decomposition I).1] at h
    change Push.Scan.quota
      (Push.Scan.lines .south (firstRequests (readerRounds I)) ++ instructions (readerRounds I).tail) = _ at h
    rw [Push.Scan.quota_append, Push.Scan.lines_quota] at h
    exact h.le
  first_height := readerRounds_first_height
  target_x I := by
    change (layout false I).width - 1 + 1 = (layout false I).width
    have := (layout false I).width_pos
    omega
  target_y I := by
    change (layout false I).height - 1 + 1 = (layout false I).height
    have := (layout false I).height_pos
    omega

def BlocksAccepted (I : Instance) : Prop :=
  ∃ t : PushFS.State (readerSource I).width (readerSource I).height,
    Reachable (readerSource I).initial t ∧ t.player = (readerSource I).target ∧
      ∃ F, WholeBlocks.Exec (readerRounds I) t.boxesᶜ F

theorem sourceFamily_language_iff (I : Instance) :
    CyclicReader.SourceLanguage sourceFamily I ↔ BlocksAccepted I := by
  change (∃ t, Reachable (readerSource I).initial t ∧ t.player = (readerSource I).target ∧
    ∃ F, WholeBlocks.Exec (.read .south (firstRequests (readerRounds I)) :: (readerRounds I).tail) _ F) ↔ _
  rw [← (reader_decomposition I).1]
  rfl

theorem blocksAccepted_of_mem (I : Instance) (hs : I ∈ SelfClosingDoor.Reachability) : BlocksAccepted I := by
  obtain ⟨S, hr, hs⟩ := reaches_parked I hs
  exact ⟨S.canonical false, hr, (readerSource_target I).symm, ∅,
    WholeBlocks.Exec.of_exact (readerRounds_bounded I) (S.quotaProgram_whole hs)⟩

/-- Every accepted original round pays its exact sparse quota on the same reachable source state. -/
theorem BlocksAccepted.exact {I : Instance} (H : BlocksAccepted I) :
    ∃ t : PushFS.State (readerSource I).width (readerSource I).height,
      Reachable (readerSource I).initial t ∧ t.player = (readerSource I).target ∧
        WholeScan.Exec (instructions (readerRounds I)) t.boxesᶜ ∅ := by
  obtain ⟨t, hr, hp, F, H⟩ := H
  have hq := (readerRounds_budget I).trans (Reachable.card_holes hr).symm
  obtain ⟨he, hF⟩ := H.exact_of_budget (readerRounds_bounded I) (readerRounds_positive_nodup I) hq
  exact ⟨t, hr, hp, hF ▸ he⟩

end PushPuzzle.PushPush.Doors.Source
