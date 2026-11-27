/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteAtomFrames
public import PushS.FiniteParallelFrames

/-! Exact full-stock updates for the narrow single-push replay interfaces. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS

variable {w h n m W H : ℕ}

namespace FiniteWireFrame.Frame

/-- Restrict the cells exposed by a frame while retaining its actual stationary inventory. -/
theorem mono_active {active smaller : Finset (Cell w h)} {e : GridEmbedding w h W H}
    {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame active e B fixed) (hsub : smaller ⊆ active) :
    FiniteWireFrame.Frame smaller e B fixed where
  floor p hp := F.floor p (hsub hp)
  fixed_avoids p hp := F.fixed_avoids p (hsub hp)
  fixed_floor := F.fixed_floor

end FiniteWireFrame.Frame

namespace FiniteAtomFrames

/-- Update one actual label and retain the entire represented inventory. -/
theorem update_ambient (support src dst : Cell w h) (d : Direction)
    (hax : Adjacent d support src) (hxd : Adjacent d src dst)
    (stock : Finset (Cell w h)) (hsrc : src ∈ stock)
    (e : GridEmbedding w h W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (pushActive support src dst) e B
      ((stock.erase src).map e.cells ∪ extra)) :
    Reachable B (some 1) (e.extend extra ⟨support,stock⟩)
      (e.extend extra ⟨src,insert dst (stock.erase src)⟩) := by
  have hr := push_ambient support src dst d hax hxd e F
  simpa only [FiniteWireFrame.extend_insert, Finset.insert_erase hsrc] using hr

/-- Fill a prepared missing normal slot and restore the entire target inventory. -/
theorem restore_ambient (support src dst : Cell w h) (d : Direction)
    (hax : Adjacent d support src) (hxd : Adjacent d src dst)
    (target : Finset (Cell w h)) (hdst : dst ∈ target)
    (e : GridEmbedding w h W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (pushActive support src dst) e B
      ((target.erase dst).map e.cells ∪ extra)) :
    Reachable B (some 1) (e.extend extra ⟨support,insert src (target.erase dst)⟩)
      (e.extend extra ⟨src,target⟩) := by
  have hr := push_ambient support src dst d hax hxd e F
  simpa only [FiniteWireFrame.extend_insert, Finset.insert_erase hdst] using hr

end FiniteAtomFrames

namespace FiniteParallelFrames

/-- Use a rotated or reflected local lane to update one physical label in the full stock. -/
theorem update_mapped_ambient (hub support src dst : Fin w) (lane row : Fin h) (entry d : Direction)
    (hentry : Adjacent entry (support,lane) (support,row))
    (hexit : Adjacent entry.opposite (src,row) (src,lane))
    (hax : Adjacent d (support,row) (src,row)) (hxd : Adjacent d (src,row) (dst,row))
    (a : GridEmbedding w h n m) (stock : Finset (Cell n m)) (hsrc : a.cells (src,row) ∈ stock)
    (e : GridEmbedding n m W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (active hub support src dst lane row) (a.trans e) B
      ((stock.erase (a.cells (src,row))).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨a.cells (hub,lane),stock⟩)
      (e.extend extra ⟨a.cells (hub,lane),insert (a.cells (dst,row)) (stock.erase (a.cells (src,row)))⟩) := by
  have he (p v : Cell w h) :
      (a.trans e).extend ((stock.erase (a.cells (src,row))).map e.cells ∪ extra) ⟨p,{v}⟩ =
      e.extend extra ⟨a.cells p,insert (a.cells v) (stock.erase (a.cells (src,row)))⟩ := by
    apply State.ext
    · rfl
    · simp only [GridEmbedding.extend, Finset.map_singleton, Finset.map_insert,
        GridEmbedding.trans, Finset.singleton_union, Finset.insert_union]
      rfl
  have hr := push_ambient hub support src dst lane row entry d hentry hexit hax hxd (a.trans e) F
  simpa only [he, Finset.insert_erase hsrc] using hr

end FiniteParallelFrames
end PushPuzzle.PushS
