/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCompilerBounds

/-! Literal narrow footprints of the emitted line marks and turn windows. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

def coordinates {W H : ℕ} (p : Cell W H) : ℕ × ℕ := (p.1.val,p.2.val)

theorem advance_contains (d : Direction) (p q : ℕ × ℕ) (length t : ℕ)
    (h : Travels d p q length) (ht : t ≤ length) : (⟨p,q⟩ : Segment).Contains (advance d p t) := by
  cases d <;> dsimp [Travels, advance, Segment.Contains] at * <;> omega

namespace Line

attribute [local irreducible] width height

/-- Project a physical strip cell onto the exact closed centerline interval. -/
def railProjection (w : ℕ) (atoms : List Atom) (p : Cell (width w atoms) (height w)) :
    Cell (width w atoms) (height w) :=
  (⟨min p.1.val (FiniteTools.radius w+span w atoms), by have hp := p.1.isLt; omega⟩,
   ⟨FiniteTools.radius w, by unfold height FiniteTools.side; omega⟩)

private theorem railProjection_bounds (w : ℕ) (atoms : List Atom) (p : Cell (width w atoms)
    (height w))
    (hx : FiniteTools.radius w ≤ p.1.val) :
    FiniteTools.radius w ≤ (railProjection w atoms p).1.val ∧
      (railProjection w atoms p).1.val ≤ FiniteTools.radius w+span w atoms := by
  dsimp [railProjection]
  omega

private theorem railProjection_nearby (w : ℕ) (atoms : List Atom) (m : ℕ)
    (p : Cell (width w atoms) (height w))
    (hx' : p.1.val ≤ FiniteTools.radius w+span w atoms+1)
    (hy : FiniteTools.radius w-m ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+m) :
    Nearby (m+1) (coordinates p) (coordinates (railProjection w atoms p)) := by
  dsimp [Nearby, coordinates, railProjection]
  omega

/-- Proper rectangle rotations and placement translations preserve the exact grid distance bound. -/
private theorem placement_nearby (w : ℕ) (atoms : List Atom) (d : Direction) (p q : ℕ × ℕ)
    (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w)
    (m : ℕ) (a b : Cell (width w atoms) (height w))
    (h : Nearby m (coordinates a) (coordinates b)) :
    Nearby m (coordinates ((placement w atoms d p q htravel hp hq).cells a))
      (coordinates ((placement w atoms d p q htravel hp hq).cells b)) := by
  have ha := rotation_coordinates w atoms d a
  have hb := rotation_coordinates w atoms d b
  have hax := congrArg Prod.fst ha
  have hay := congrArg Prod.snd ha
  have hbx := congrArg Prod.fst hb
  have hby := congrArg Prod.snd hb
  dsimp only at hax hay hbx hby
  dsimp [coordinates, placement, GridEmbedding.trans, GridEmbedding.translate, GridIsometry.embedding]
  rw [hax,hay,hbx,hby]
  have haX := a.1.isLt
  have haY := a.2.isLt
  have hbX := b.1.isLt
  have hbY := b.2.isLt
  cases d <;> dsimp [rotatedCoordinates, Nearby, coordinates] at * <;> omega

theorem placement_row (w : ℕ) (atoms : List Atom) (d : Direction) (p q : ℕ × ℕ)
    (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w)
    (a : Cell (width w atoms) (height w))
    (hx : FiniteTools.radius w ≤ a.1.val) (hx' : a.1.val ≤ FiniteTools.radius w+span w atoms)
    (hy : a.2.val = FiniteTools.radius w) :
    coordinates ((placement w atoms d p q htravel hp hq).cells a) =
      along w d p (a.1.val-FiniteTools.radius w) := by
  have hr := rotation_coordinates w atoms d a
  have hax := congrArg Prod.fst hr
  have hay := congrArg Prod.snd hr
  dsimp only at hax hay
  apply Prod.ext
  all_goals dsimp [coordinates, placement, GridEmbedding.trans, GridEmbedding.translate, GridIsometry.embedding]
  · rw [hax]
    cases d <;> dsimp [rotatedCoordinates, along, Travels, offsetX, anchor] at * <;>
      unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega
  · rw [hay]
    cases d <;> dsimp [rotatedCoordinates, along, Travels, offsetY, anchor] at * <;>
      unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega

private theorem along_advance (w : ℕ) (d : Direction) (p q : ℕ × ℕ) (length t : ℕ)
    (h : Travels d p q length) (ht : t ≤ length) :
    along w d p t = (padding w+(advance d p t).1,padding w+(advance d p t).2) := by
  cases d <;> dsimp [along, advance, Travels] at * <;> apply Prod.ext <;> omega

theorem placed_box_footprint (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom)
    (d : Direction) (p q : ℕ × ℕ) (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w) (phase : Bool) (l : Label w atoms) :
    ∃ u, (⟨p,q⟩ : Segment).Contains u ∧
      Nearby 1 (coordinates ((placement w atoms d p q htravel hp hq).cells (cell w hw atoms phase l)))
        (padding w+u.1,padding w+u.2) := by
  let a := cell w hw atoms phase l
  have hb := positions_bounds w hw phase atoms (position_mem w atoms phase l)
  have hphase := Bool.toNat_le phase
  have ha : FiniteTools.radius w ≤ a.1.val := by dsimp [a,cell]; omega
  have hproj := railProjection_bounds w atoms a ha
  let t := (railProjection w atoms a).1.val-FiniteTools.radius w
  have ht : t ≤ span w atoms := by dsimp [t]; omega
  refine ⟨advance d p t,advance_contains d p q _ t htravel ht,?_⟩
  have hn := railProjection_nearby w atoms 0 a (by dsimp [a,cell]; omega)
    (by dsimp [a,cell]; omega) (by dsimp [a,cell]; omega)
  have himg := placement_nearby w atoms d p q htravel hp hq 1 a (railProjection w atoms a) hn
  have he := placement_row w atoms d p q htravel hp hq (railProjection w atoms a) hproj.1 hproj.2 rfl
  rw [he,along_advance w d p q _ t htravel ht] at himg
  exact himg

end Line

end PushPuzzle.PushS.FiniteRouting
