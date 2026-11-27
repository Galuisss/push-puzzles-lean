/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlocks
public import PushPush.ColumnReaderLanguage
public import PushPush.CyclicFamily

/-! Whole-round source languages of the maximum-sliding reader compiler. -/

@[expose] public section
namespace PushPuzzle.PushPush.CyclicReader

open PushFS (Cell State Direction)
open Push.AcceptanceProgram Push.CyclicReader

def Language (r : Push.ColumnScan.Input) (rounds : List Round) : Prop :=
  ∃ s : State r.width r.height, Reachable r.initial.toState s ∧ s.player = r.sourceCorner ∧
    ∃ E F, WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas)) (PushS.holes s) E ∧
      WholeBlocks.Exec rounds E F

theorem compile_nil_iff (r : Push.ColumnScan.Input) :
    PushPush.Instance.Solvable r.compile ↔ Language r [] := by
  rw [ColumnReader.compile_solvable_iff_whole_scan]
  constructor
  · rintro ⟨s, hr, hp, E, H⟩
    exact ⟨s, hr, hp, E, E, H, .nil E⟩
  · rintro ⟨s, hr, hp, E, F, H, hnil⟩
    exact ⟨s, hr, hp, E, H⟩

/-- The literal first sparse south block followed by every original future block. -/
def SourceLanguage {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
    (F : SourceFamily α enc shapes) (a : α) : Prop :=
  ∃ s : State (F.source a).width (F.source a).height,
    Reachable (F.source a).initial s ∧ s.player = (F.source a).target ∧
      ∃ E, WholeBlocks.Exec (.read .south (F.requests a) :: F.rounds a) (PushS.holes s) E

theorem direct_language_iff {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
    (F : SourceFamily α enc shapes) (a : α) :
    Language ((direct F).reader a) ((direct F).rounds a) ↔ SourceLanguage F a := by
  have hi : (F.reader a).initial.toState = (F.source a).initial := Push.ColumnScan.Input.ofInstance_initial ..
  have hc : (F.reader a).sourceCorner = (F.source a).target :=
    Push.ColumnScan.Input.ofInstance_corner _ _ _ _ (F.target_x a) (F.target_y a)
  constructor
  · rintro ⟨s, hr, hp, E, G, hfirst, hrest⟩
    refine ⟨s, ?_, hp.trans hc, G, .cons hfirst hrest⟩
    exact Eq.mp (congrArg (fun u => Reachable u s) hi) hr
  · rintro ⟨s, hr, hp, G, H⟩
    cases H with
    | @cons _ _ _ _ E _ hfirst hrest =>
      refine ⟨s, ?_, hp.trans hc.symm, E, G, hfirst, hrest⟩
      exact Eq.mpr (congrArg (fun u => Reachable u s) hi) hr

end PushPuzzle.PushPush.CyclicReader
