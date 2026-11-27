/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderProgram
public import Push.AcceptanceProgramComplete
public import Push.AcceptanceProgramFirstQuota
public import Push.SourceGame
public import PushS.PortInstance

/-! Actual canonical marked-board families satisfy every condition of the ordinary point compiler. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS Turing.MultiTapeTM

/-- Construct the actual source/program compiler family with its fixed physical level allocation. -/
def readerFamily {α : Type} {enc : α ↪ List Bool}
    {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
    {initial target : α → List Bool}
    (hpages : ∀ a, (layout a).pages.Valid)
    (hM : ∀ a, (layout a).pages.highest ≤ (p a).levels)
    (haxes : ∀ a, (layout a).portCount ≤ (p a).axes)
    (hlevels : ∀ a, (p a).levels = M)
    (hsource : ComputableInPolyTime
      (fun a => (layout a).canonicalInstance (p a) (hpages a) (hM a) (haxes a) (initial a) (target a))
      enc PushS.encoding)
    (hprogram : ComputableInPolyTime (fun a => (program (layout a) (p a) (target a)).rounds) enc encRounds) :
    CyclicReader.ProgramFamily α enc ((skeleton M).drop 2) where
  source a := SourceGame.ofStorage
    ((layout a).canonicalInstance (p a) (hpages a) (hM a) (haxes a) (initial a) (target a))
  rounds a := (program (layout a) (p a) (target a)).rounds
  source_polyTime := SourceGame.ofStorage_polyTime.comp hsource
  rounds_polyTime := hprogram
  shapes_eq a := by
    rw [program_shapes, hlevels a]
    rfl
  reference_accepts a := ⟨targetHoles (layout a) (p a) (target a), ∅, program_accepts_target _ _ _⟩
  budget a := by
    have hh : holes ((layout a).canonicalInstance (p a) (hpages a) (hM a) (haxes a)
        (initial a) (target a)).initial = SegmentRecipe.holes ((p a).W + 1) ((p a).H + 1)
          ((layout a).encodedSegments (p a) ((layout a).canonical (initial a))) :=
      (layout a).physicalInstance_initial_holes (p a) (hpages a) (hM a) (haxes a)
        ((layout a).canonical (initial a)) ((layout a).canonical (target a))
    have hq := program_source_quota (layout a) (p a) (hpages a) (hM a) (haxes a) (initial a) (target a)
    change Scan.quota (instructions (w := (p a).W + 1) (h := (p a).H + 1)
      (program (layout a) (p a) (target a)).rounds) ≤
        (holes ((layout a).canonicalInstance (p a) (hpages a) (hM a) (haxes a) (initial a) (target a)).initial).card
    rw [hh]
    exact hq.le
  first_height a := by
    obtain ⟨requests, rest, he, hheight⟩ := bounded_program_first_south (layout a) (p a) (target a)
    change (p a).H + 1 ≤ ((CyclicReader.firstRequests
      (boundedRounds ((p a).W + 1) ((p a).H + 1) (program (layout a) (p a) (target a)).rounds)).map Prod.snd).sum
    rw [he]
    exact hheight
  target_x a := (SourceGame.ofStorage_target
    ((layout a).canonicalInstance (p a) (hpages a) (hM a) (haxes a) (initial a) (target a))).1
  target_y a := (SourceGame.ofStorage_target
    ((layout a).canonicalInstance (p a) (hpages a) (hM a) (haxes a) (initial a) (target a))).2

end PushPuzzle.Push.AcceptanceProgram
