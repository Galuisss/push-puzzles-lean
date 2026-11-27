/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSourceBoundary
public import Push.ColumnScanForward
public import Push.ReflectedFrontier

/-! Cropping the actual pre-needle trajectory retains the source player, using its corner outside. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

/-- The original source board has no fixed walls. -/
def sourceBoard : Board r.width r.height := ⟨∅, ∅⟩

instance (s : State r.outputWidth r.outputHeight) : Decidable (r.SourceInside s) :=
  inferInstanceAs (Decidable (s.player.1.val < r.width ∧ s.player.2.val < r.height))

/-- The physical player in the source, or the source corner while the physical player is outside. -/
def cropPlayer (s : State r.outputWidth r.outputHeight) : Cell r.width r.height :=
  if hi : r.SourceInside s then (⟨s.player.1.val, hi.1⟩, ⟨s.player.2.val, hi.2⟩)
  else r.sourceCorner

/-- The exact source bitmap and its retained player position. -/
def cropState (s : State r.outputWidth r.outputHeight) : State r.width r.height :=
  ⟨r.cropPlayer s, Finset.univ.filter fun p => r.embed p ∈ s.boxes⟩

@[simp] theorem cropState_mem_boxes (s : State r.outputWidth r.outputHeight) (p : Cell r.width r.height) :
    p ∈ (r.cropState s).boxes ↔ r.embed p ∈ s.boxes := by
  simp only [cropState, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem cropState_mem_holes (s : State r.outputWidth r.outputHeight) (p : Cell r.width r.height) :
    p ∈ holes (r.cropState s) ↔ r.embed p ∈ holes s := by
  simp only [mem_holes, cropState_mem_boxes]

theorem cropPlayer_inside {s : State r.outputWidth r.outputHeight} (hs : r.SourceInside s) :
    r.embed (r.cropState s).player = s.player := by
  simp only [cropState, cropPlayer, dite_eq_left hs]
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem cropPlayer_outside {s : State r.outputWidth r.outputHeight} (hs : ¬r.SourceInside s) :
    (r.cropState s).player = r.sourceCorner := by simp only [cropState, cropPlayer, dite_eq_right hs]

/-- Cropping the emitted initial bitmap gives the exact original source state. -/
theorem cropState_initial : r.cropState r.initialState.toState = r.initial.toState := by
  have hi : r.SourceInside r.initialState.toState := ⟨r.initial.player.1.isLt, r.initial.player.2.isLt⟩
  apply State.ext
  · apply r.embed_injective
    exact r.cropPlayer_inside hi
  · ext p
    rw [r.cropState_mem_boxes]
    change (r.embed p ∈ r.emptyᶜ) ↔ p ∈ r.initial.emptyᶜ
    simpa only [Finset.mem_compl] using not_congr (r.embed_mem_empty p)

/-- The cropped hole set embeds to precisely the source-row holes of the real board. -/
theorem cropState_holes_image (s : State r.outputWidth r.outputHeight) :
    (holes (r.cropState s)).image r.embed = ReflectedFrontier.source r.width r.height s := by
  ext q
  simp only [Finset.mem_image, ReflectedFrontier.source, Finset.mem_filter]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(r.cropState_mem_holes s p).mp hp, p.1.isLt, p.2.isLt⟩
  · rintro ⟨hq, hx, hy⟩
    let p : Cell r.width r.height := (⟨q.1.val, hx⟩, ⟨q.2.val, hy⟩)
    have he : r.embed p = q := by apply Prod.ext <;> apply Fin.ext <;> rfl
    exact ⟨p, (r.cropState_mem_holes s p).mpr (he.symm ▸ hq), he⟩

/-- A successful pre-needle player outside the source is always east of all source columns. -/
theorem before_south_player_east
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hv : s.Valid r.compile.board) (hs : ¬r.SourceInside s) : r.width ≤ s.player.1.val := by
  by_contra hx
  have hy : r.height ≤ s.player.2.val := by
    by_contra hy
    exact hs ⟨by omega, by omega⟩
  obtain ⟨i, hi⟩ := (r.before_south_exact hr hsf hfx hfy (by omega) hy).mp (player_mem_holes hv)
  have hN := reachable_north hr (r.initial_north r.width)
  have hn := hN (by omega)
  have hi' := congrArg (fun q => q.2.val) hi
  have ht := r.targetLevel_le_needleLevel i
  change r.needleLevel i = s.player.2.val at hi'
  omega

/-- An outside player on an original source row occupies the unique side door. -/
theorem before_south_outside_on_source_row
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hv : s.Valid r.compile.board) (hs : ¬r.SourceInside s) (hy : s.player.2.val < r.height) :
    s.player = r.door := by
  have hx := r.before_south_player_east hr hsf hfx hfy hv hs
  have hreach : Reachable r.compile.board none r.compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hr
  have hxeq : s.player.1.val = r.width := by
    by_contra hn
    exact hv.2.2 (r.east_full hreach s.player (by omega) hy)
  have hyeq : s.player.2.val = r.height - 1 := by
    by_contra hn
    exact hv.2.2 (r.northeast_full hreach s.player hx (by omega))
  apply Prod.ext <;> apply Fin.ext
  · exact hxeq
  · exact hyeq

end PushPuzzle.Push.ColumnScan.Input
