/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSourceMoves

/-! Every committed-reader source prefix is a real source computation, with its original hole inventory. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

/-- Cropping a successful pre-needle trajectory deletes only excursions from the source corner. -/
theorem before_south_source_reachable
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    Reachable r.sourceBoard none r.initial.toState (r.cropState s) := by
  revert hsf
  induction hr with
  | refl =>
    intro _
    rw [r.cropState_initial]
  | @tail u v hpre hm ih =>
    intro hvf
    have huf := (Relation.ReflTransGen.single hm.1).trans hvf
    have hsource := ih huf
    have hvsource := hsource.valid (r.initial.valid r.sourceBoard rfl)
    rcases r.before_south_step_crop hpre hm hvf hfx hfy hvsource with he | hs
    · simpa only [he] using hsource
    · exact hsource.tail hs

/-- The source-row hole inventory is unchanged up to the committed landing. -/
theorem before_south_source_count
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    (ReflectedFrontier.source r.width r.height s).card = r.sourceHoles := by
  have hsource := r.before_south_source_reachable hr hsf hfx hfy
  calc
    _ = (holes (r.cropState s)).card := by
      rw [← r.cropState_holes_image, Finset.card_image_of_injective _ r.embed_injective]
    _ = (holes r.initial.toState).card := card_holes_reachable hsource
    _ = r.sourceHoles := by rw [r.initial.holes_toState]; rfl

/-- The exact source bitmap present at commitment is reachable in the original source, at its corner. -/
theorem landing_source_prefix
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : s.player = r.landing) :
    Reachable r.sourceBoard none r.initial.toState (r.cropState s) ∧
      (r.cropState s).player = r.sourceCorner ∧
      (holes (r.cropState s)).image r.embed = ReflectedFrontier.source r.width r.height s ∧
      (ReflectedFrontier.source r.width r.height s).card = r.sourceHoles := by
  have hout : ¬r.SourceInside s := by
    intro hh
    have hx := hh.1
    rw [hs] at hx
    change r.width < r.width at hx
    omega
  exact ⟨r.before_south_source_reachable hr hsf hfx hfy, r.cropPlayer_outside hout,
    r.cropState_holes_image s, r.before_south_source_count hr hsf hfx hfy⟩

end PushPuzzle.Push.ColumnScan.Input
