/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFrameComposition

/-! Narrow active-frame replay of one push reached from an adjacent parallel lane. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteParallelFrames

open PushFS

variable {w h W H : ℕ}

/-- The three push cells and the exact adjacent lane interval used before and after the push. -/
def active (hub support src dst : Fin w) (lane row : Fin h) : Finset (Cell w h) :=
  {(support,row), (src,row), (dst,row)} ∪ Finset.univ.filter fun p =>
    p.2 = lane ∧ min hub.val (min support.val src.val) ≤ p.1.val ∧
      p.1.val ≤ max hub.val (max support.val src.val)

/-- Walk to one actual support, push one box, and return along the same exposed lane. -/
theorem push_ambient (hub support src dst : Fin w) (lane row : Fin h) (entry d : Direction)
    (hentry : Adjacent entry (support,lane) (support,row))
    (hexit : Adjacent entry.opposite (src,row) (src,lane))
    (hax : Adjacent d (support,row) (src,row)) (hxd : Adjacent d (src,row) (dst,row))
    (e : GridEmbedding w h W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (active hub support src dst lane row) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨(hub,lane), {(src,row)}⟩)
      (e.extend fixed ⟨(hub,lane), {(dst,row)}⟩) := by
  let A := FiniteWireFrame.board (active hub support src dst lane row) ∅
  have hfloor (x : Fin w) (hx : x = support ∨ x = src ∨ x = dst) : (x,row) ∉ A.walls := by
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    apply Finset.mem_union_left
    rcases hx with rfl | rfl | rfl <;> simp
  have hrowne : lane ≠ row := by
    intro he
    exact hentry.ne (by rw [he])
  have hlane (z : Fin w)
      (hz : min hub.val (min support.val src.val) ≤ z.val)
      (hz' : z.val ≤ max hub.val (max support.val src.val)) : Free A {(src,row)} (z,lane) := by
    constructor
    · apply (FiniteWireFrame.floor_iff _ _ _).mpr
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hz, hz'⟩
    · intro hm
      have he := Finset.mem_singleton.mp hm
      exact hrowne (congrArg Prod.snd he)
  have hsrc : (src,row) ∉ A.walls := hfloor src (Or.inr (Or.inl rfl))
  have hlocal := push_via_parallel_row (Finset.disjoint_singleton_left.mpr hsrc)
    hub support src dst lane row entry d hentry hexit hax hxd
    ⟨hfloor support (Or.inl rfl), by simpa only [Finset.mem_singleton] using hax.ne⟩
    (Finset.mem_singleton_self _)
    ⟨hfloor dst (Or.inr (Or.inr rfl)), by simpa only [Finset.mem_singleton] using hxd.ne.symm⟩
    (by intro z hz hz'; apply hlane z <;> omega)
    (by intro z hz hz'; apply hlane z <;> omega)
  have hr : Reachable A (some 1) ⟨(hub,lane), {(src,row)}⟩ ⟨(hub,lane), {(dst,row)}⟩ := by
    simpa only [Finset.erase_singleton, Finset.insert_empty] using hlocal
  exact F.replay hr

/-- Isolate the chosen physical source label and update the complete local-plus-global inventory. -/
theorem update_ambient (hub support src dst : Fin w) (lane row : Fin h) (entry d : Direction)
    (hentry : Adjacent entry (support,lane) (support,row))
    (hexit : Adjacent entry.opposite (src,row) (src,lane))
    (hax : Adjacent d (support,row) (src,row)) (hxd : Adjacent d (src,row) (dst,row))
    (stock : Finset (Cell w h)) (hsource : (src,row) ∈ stock)
    (e : GridEmbedding w h W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (active hub support src dst lane row) e B
      ((stock.erase (src,row)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(hub,lane), stock⟩)
      (e.extend extra ⟨(hub,lane), insert (dst,row) (stock.erase (src,row))⟩) := by
  have hr := push_ambient hub support src dst lane row entry d hentry hexit hax hxd e F
  simpa only [FiniteWireFrame.extend_insert, Finset.insert_erase hsource] using hr

end PushPuzzle.PushS.FiniteParallelFrames
