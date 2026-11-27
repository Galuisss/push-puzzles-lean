/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingStockMacros
public import PushS.FiniteFlipMacros
public import PushS.FiniteParityOwned
import Mathlib.Tactic.NormNum

/-! Concrete buffered placements of full flip and parity macros inside a routing line. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Tool

open PushFS FiniteTools
open FiniteGeometry (Rectangle)

def mirrorDirection : Direction → Direction
  | .north => .south
  | .south => .north
  | .east => .east
  | .west => .west

def embedding (w : ℕ) (atoms : List Atom) (dx : ℕ) (above : Bool)
    (hx : dx+side w ≤ width w atoms) : GridEmbedding (side w) (side w) (width w atoms) (height w) where
  cells := {
    toFun p := (⟨dx+p.1.val, by have := p.1.isLt; omega⟩,
      ⟨if above then 2*radius w-p.2.val else p.2.val, by
        have := p.2.isLt
        unfold height side at *
        split <;> omega⟩)
    inj' := by
      intro p q he
      have hp := p.2.isLt
      have hq := q.2.isLt
      have hxe := congrArg (fun p : Cell (width w atoms) (height w) => p.1.val) he
      have hye := congrArg (fun p : Cell (width w atoms) (height w) => p.2.val) he
      apply Prod.ext <;> apply Fin.ext
      · dsimp at hxe; omega
      · cases above <;> dsimp at hye <;> unfold side at hp hq <;> omega }
  direction := if above then mirrorDirection else id
  adjacent := by
    intro d p q ha
    have hp := p.2.isLt
    have hq := q.2.isLt
    cases above <;> cases d <;> simp [Adjacent, mirrorDirection] at ha ⊢ <;>
      unfold side at hp hq <;> omega

def flipPlace (w : ℕ) (before after : List Atom) (n m : ℕ) (above : Bool) :
    GridEmbedding (side w) (side w) (width w (before++ .line n:: .flip:: .line m::after)) (height w) :=
  embedding w _ (span w before+2*n+w) (exitSide above before) (by
    unfold width side
    simp only [span_append, span_cons, Atom.span]
    omega)

def parityPlace (w : ℕ) (before after : List Atom) (n m : ℕ) (above : Bool) :
    GridEmbedding (side w) (side w) (width w (before++ .line n:: .parity:: .line m::after)) (height w) :=
  embedding w _ (span w before+2*n) (exitSide above before) (by
    unfold width side
    simp only [span_append, span_cons, Atom.span]
    omega)

attribute [local irreducible] width height

private theorem in_flip_wall (w : ℕ) (p : Cell (side w) (side w)) (i : Fin 4)
    (h : p ∈ (flipRectangle w i).cells (side w) (side w)) : p ∈ flipWalls w :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩

/-- The two complete stock collars and every other atom introduce no wall on the actual flip floor. -/
theorem flip_floor (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (p : Cell (side w) (side w)) (hp : p ∈ flipActive w) :
    (flipPlace w before after n m above).cells p ∈
      active w (before++ .line n:: .flip:: .line m::after) above := by
  unfold buffer at hn hm
  have hpa := (Finset.mem_filter.mp hp).2
  have hpy := p.2.isLt
  have hpx := p.1.isLt
  have hxy : ((flipPlace w before after n m above).cells p).1.val =
      span w before+2*n+w+p.1.val := by rfl
  have hyy : ((flipPlace w before after n m above).cells p).2.val =
      if exitSide above before then 2*radius w-p.2.val else p.2.val := by rfl
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hxy]; unfold radius at *; omega
  · rw [hxy]; simp only [span_append, span_cons, Atom.span]
    unfold radius at *; omega
  · rw [hyy]; cases hb : exitSide above before <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> unfold radius at * <;> omega
  · rw [hyy]; cases hb : exitSide above before <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> unfold radius at * <;> omega
  · intro hwall
    obtain ⟨r, hr, hrp⟩ := Finset.mem_biUnion.mp hwall
    have hr' := List.mem_toFinset.mp hr
    rw [rectangles_split] at hr'
    have hrp' := (Rectangle.mem_cells _ _ _ _).mp hrp
    rcases List.mem_append.mp hr' with hbefore | hrest
    · have hb := rectangles_bounds w 0 above before hbefore
      rw [hxy] at hrp'
      unfold radius at *; omega
    · simp only [rectangles, Atom.nextSide, Atom.span, Nat.zero_add] at hrest
      rcases List.mem_append.mp hrest with hleft | hrest
      · have he : r = ⟨radius w+span w before,
          if exitSide above before then radius w-w else radius w+1, 2*n+2,w⟩ := by
          simpa only [Atom.rectangles, List.mem_singleton] using hleft
        subst r
        apply hpa.2.2.2.2
        apply in_flip_wall w p 0
        apply (Rectangle.mem_cells _ _ _ _).mpr
        rw [hxy, hyy] at hrp'
        cases hb : exitSide above before <;> simp [hb] at hrp' <;>
          norm_num [flipRectangle] <;> unfold side radius at * <;> omega
      · rcases List.mem_append.mp hrest with hflip | hrest
        · apply hpa.2.2.2.2
          cases hb : exitSide above before <;> simp [Atom.rectangles, hb] at hflip <;>
            rcases hflip with rfl | rfl | rfl | rfl
          all_goals rw [hxy, hyy] at hrp'; simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hrp'
          all_goals first
            | exact in_flip_wall w p 0 (by apply (Rectangle.mem_cells _ _ _ _).mpr; norm_num [flipRectangle]; unfold side radius at *; omega)
            | exact in_flip_wall w p 1 (by apply (Rectangle.mem_cells _ _ _ _).mpr; norm_num [flipRectangle]; unfold side radius at *; omega)
            | exact in_flip_wall w p 2 (by apply (Rectangle.mem_cells _ _ _ _).mpr; norm_num [flipRectangle]; unfold side radius at *; omega)
            | exact in_flip_wall w p 3 (by apply (Rectangle.mem_cells _ _ _ _).mpr; norm_num [flipRectangle]; unfold side radius at *; omega)
        · rcases List.mem_append.mp hrest with hright | hafter
          · have he : r = ⟨radius w+(span w before+2*n+(2*w+2)),
              if !(exitSide above before) then radius w-w else radius w+1, 2*m+2,w⟩ := by
              simpa only [Atom.rectangles, List.mem_singleton] using hright
            subst r
            apply hpa.2.2.2.2
            apply in_flip_wall w p 3
            apply (Rectangle.mem_cells _ _ _ _).mpr
            rw [hxy, hyy] at hrp'
            cases hb : exitSide above before <;> simp [hb] at hrp' <;>
              norm_num [flipRectangle] <;> unfold side radius at * <;> omega
          · have hb := rectangles_bounds w (span w before+2*n+(2*w+2)+2*m)
              (!(exitSide above before)) after hafter
            rw [hxy] at hrp'
            unfold radius at *; omega

private theorem in_parity_wall (w : ℕ) (p : Cell (side w) (side w)) (i : Fin 2)
    (h : p ∈ (parityRectangle w i).cells (side w) (side w)) : p ∈ parityWalls w :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩

/-- A full parity adapter uses only its explicitly represented roof corridor. -/
theorem parity_floor (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (p : Cell (side w) (side w)) (hp : p ∈ parityActive w) :
    (parityPlace w before after n m above).cells p ∈
      active w (before++ .line n:: .parity:: .line m::after) above := by
  unfold buffer at hn hm
  have hpa := (Finset.mem_filter.mp hp).2
  have hpy := p.2.isLt
  have hpx := p.1.isLt
  have hspan := paritySpan_bounds w
  have hxy : ((parityPlace w before after n m above).cells p).1.val =
      span w before+2*n+p.1.val := by rfl
  have hyy : ((parityPlace w before after n m above).cells p).2.val =
      if exitSide above before then 2*radius w-p.2.val else p.2.val := by rfl
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hxy]; unfold radius at *; omega
  · rw [hxy]; simp only [span_append, span_cons, Atom.span]
    unfold radius at *; omega
  · rw [hyy]; cases hb : exitSide above before <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> unfold radius at * <;> omega
  · rw [hyy]; cases hb : exitSide above before <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> unfold radius at * <;> omega
  · intro hwall
    obtain ⟨r, hr, hrp⟩ := Finset.mem_biUnion.mp hwall
    have hr' := List.mem_toFinset.mp hr
    rw [rectangles_split] at hr'
    have hrp' := (Rectangle.mem_cells _ _ _ _).mp hrp
    rcases List.mem_append.mp hr' with hbefore | hrest
    · have hb := rectangles_bounds w 0 above before hbefore
      rw [hxy] at hrp'
      unfold radius at *; omega
    · simp only [rectangles, Atom.nextSide, Atom.span, Nat.zero_add] at hrest
      rcases List.mem_append.mp hrest with hleft | hrest
      · have he : r = ⟨radius w+span w before,
          if exitSide above before then radius w-w else radius w+1, 2*n+2,w⟩ := by
          simpa only [Atom.rectangles, List.mem_singleton] using hleft
        subst r
        apply hpa.2.2.2.2
        apply in_parity_wall w p 0
        apply (Rectangle.mem_cells _ _ _ _).mpr
        rw [hxy, hyy] at hrp'
        cases hb : exitSide above before <;> simp [hb] at hrp' <;>
          norm_num [parityRectangle] <;> unfold side radius at * <;> omega
      · rcases List.mem_append.mp hrest with hparity | hrest
        · apply hpa.2.2.2.2
          cases hb : exitSide above before <;> simp [Atom.rectangles, hb] at hparity <;>
            rcases hparity with rfl | rfl
          all_goals rw [hxy, hyy] at hrp'; simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hrp'
          all_goals first
            | exact in_parity_wall w p 0 (by apply (Rectangle.mem_cells _ _ _ _).mpr; norm_num [parityRectangle]; unfold side radius at *; omega)
            | exact in_parity_wall w p 1 (by apply (Rectangle.mem_cells _ _ _ _).mpr; norm_num [parityRectangle]; unfold side radius at *; omega)
        · rcases List.mem_append.mp hrest with hright | hafter
          · have he : r = ⟨radius w+(span w before+2*n+(paritySpan w+2)),
              if exitSide above before then radius w-w else radius w+1, 2*m+2,w⟩ := by
              simpa only [Atom.rectangles, List.mem_singleton] using hright
            subst r
            apply hpa.2.2.2.2
            apply in_parity_wall w p 0
            apply (Rectangle.mem_cells _ _ _ _).mpr
            rw [hxy, hyy] at hrp'
            cases hb : exitSide above before <;> simp [hb] at hrp' <;>
              norm_num [parityRectangle] <;> unfold side radius at * <;> omega
          · have hb := rectangles_bounds w (span w before+2*n+(paritySpan w+2)+2*m)
              (exitSide above before) after hafter
            rw [hxy] at hrp'
            unfold radius at *; omega

end PushPuzzle.PushS.FiniteRouting.Line.Tool
