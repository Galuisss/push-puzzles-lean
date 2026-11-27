/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteInventoryAtoms

/-! Construct global narrow frames from local noncollision and literal global floor facts. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteWireFrame.Frame

open PushFS

variable {w h n m W H : ℕ}

/-- Actual free active cells and the actual stationary stock form a narrow ambient frame. -/
theorem of_free {active : Finset (Cell w h)} {e : GridEmbedding w h W H}
    {B : Board W H} {fixed : Finset (Cell W H)} (hd : Disjoint fixed B.walls)
    (hf : ∀ p ∈ active, Free B fixed (e.cells p)) :
    FiniteWireFrame.Frame active e B fixed where
  floor p hp := (hf p hp).1
  fixed_avoids p hp := (hf p hp).2
  fixed_floor := hd

/-- Place an existing local footprint while retaining precisely its local and global stationary stock. -/
theorem place {active : Finset (Cell w h)} {a : GridEmbedding w h n m}
    {A : Board n m} {localFixed : Finset (Cell n m)}
    (F : FiniteWireFrame.Frame active a A localFixed)
    (e : GridEmbedding n m W H) {B : Board W H} {extra : Finset (Cell W H)}
    (hfloor : ∀ p ∈ active, (a.trans e).cells p ∉ B.walls)
    (hlocal : ∀ p ∈ localFixed, e.cells p ∉ B.walls)
    (hextra : Disjoint extra B.walls)
    (havoid : ∀ p ∈ active, (a.trans e).cells p ∉ extra) :
    FiniteWireFrame.Frame active (a.trans e) B (localFixed.map e.cells ∪ extra) where
  floor := hfloor
  fixed_avoids p hp := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hm
      exact F.fixed_avoids p hp (e.cells.injective he ▸ hq)
    · exact havoid p hp hm
  fixed_floor := by
    apply Finset.disjoint_union_left.mpr
    refine ⟨?_,hextra⟩
    apply Finset.disjoint_left.mpr
    intro p hp hm
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    exact hlocal q hq hm

/-- Join two explicit footprints without changing either the board or the stationary inventory. -/
theorem union {active other : Finset (Cell w h)} {e : GridEmbedding w h W H}
    {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame active e B fixed) (G : FiniteWireFrame.Frame other e B fixed) :
    FiniteWireFrame.Frame (active ∪ other) e B fixed where
  floor p hp := (Finset.mem_union.mp hp).elim (F.floor p) (G.floor p)
  fixed_avoids p hp := (Finset.mem_union.mp hp).elim (F.fixed_avoids p) (G.fixed_avoids p)
  fixed_floor := F.fixed_floor

end PushPuzzle.PushS.FiniteWireFrame.Frame
