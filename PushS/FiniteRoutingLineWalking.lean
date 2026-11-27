/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineCut
public import PushFS.Walking
import Mathlib.Tactic.FinCases

/-! Outer walking lanes and true flip-mouth crossings of emitted routing programs. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

/-- Prefix-owned points omit the interface physically owned by the following atom. -/
def ownedPositions (w : ℕ) (q : Bool) : List Atom → List ℕ
  | [] => []
  | a::atoms => a.positions w q ++ (ownedPositions w q atoms).map (a.span w + ·)

theorem positions_split (w : ℕ) (q : Bool) (pre post : List Atom) :
    positions w q (pre++post) = ownedPositions w q pre ++ (positions w q post).map (span w pre + ·) := by
  induction pre with
  | nil => simp [ownedPositions]
  | cons a pre ih =>
    simp only [List.cons_append, positions, ownedPositions, ih, List.map_append,
      List.append_assoc, List.map_map, span_cons]
    simp [Function.comp_def, Nat.add_assoc]

theorem ownedPositions_bounds (w : ℕ) (hw : 2 ≤ w) (q : Bool) (atoms : List Atom)
    {x : ℕ} (hx : x ∈ ownedPositions w q atoms) : q.toNat ≤ x ∧ x+2 ≤ span w atoms+q.toNat := by
  induction atoms generalizing x with
  | nil => simp [ownedPositions] at hx
  | cons a atoms ih =>
    rcases List.mem_append.mp hx with hx | hx
    · have hh := a.positions_bounds w hw q hx
      simp only [span_cons]
      omega
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hh := ih hy
      simp only [span_cons]
      omega

theorem rectangles_split (w offset : ℕ) (above : Bool) (pre post : List Atom) :
    rectangles w offset above (pre++post) = rectangles w offset above pre ++
      rectangles w (offset+span w pre) (exitSide above pre) post := by
  induction pre generalizing offset above with
  | nil => simp [rectangles, exitSide]
  | cons a pre ih =>
    simp only [List.cons_append, rectangles, ih, List.append_assoc, span_cons, exitSide]
    simp [Nat.add_assoc]

def laneY (w : ℕ) (north : Bool) : Fin (height w) :=
  ⟨if north then FiniteTools.radius w-w-1 else FiniteTools.radius w+w+1, by
    unfold height FiniteTools.side FiniteTools.radius
    split <;> omega⟩

def outerCell (w : ℕ) (atoms : List Atom) (north : Bool) (x : Fin (width w atoms)) :
    Cell (width w atoms) (height w) := (x, laneY w north)

attribute [local irreducible] width height

/-- The two outer rows lie strictly beyond every actual thick wall strip. -/
theorem outer_floor (w : ℕ) (atoms : List Atom) (above north : Bool) (x : Fin (width w atoms)) :
    outerCell w atoms north x ∉ walls w atoms above := by
  intro hp
  have hb := walls_bounds w atoms above hp
  cases north <;> dsimp [outerCell, laneY, FiniteTools.radius] at hb <;> omega

theorem outer_free (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above north : Bool)
    (x : Fin (width w atoms)) :
    Free (⟨walls w atoms above, ∅⟩ : Board (width w atoms) (height w))
      (cutBoxes w hw cut atoms) (outerCell w atoms north x) := by
  refine ⟨outer_floor w atoms above north x, ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hy := congrArg (fun p : Cell (width w atoms) (height w) => p.2.val) he
  have hc := (cutCell_coordinates w hw cut atoms l).2
  cases north <;> dsimp [outerCell, laneY, FiniteTools.radius] at hy hc <;> omega

/-- A cut box retains a genuine normal coordinate from one of its two source slots. -/
theorem cutCell_normal (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (l : Label w atoms) :
    ∃ q : Bool, cutCell w hw cut atoms l = cell w hw atoms q l := by
  by_cases hl : l.val < cut
  · exact ⟨false, ite_eq_left hl⟩
  · exact ⟨true, ite_eq_right hl⟩

def flipMouthX (w : ℕ) (pre post : List Atom) (j : Fin 2) :
    Fin (width w (pre++ .flip::post)) :=
  ⟨FiniteTools.radius w+span w pre+w+1+j.val, by
    have hj := j.isLt
    unfold width
    simp only [span_append, span_cons, Atom.span]
    unfold FiniteTools.radius
    omega⟩

/-- Neither mouth is a possible working-box slot, at any physical-label cut. -/
theorem flipMouth_no_box (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (pre post : List Atom) (j : Fin 2)
    (p : Cell (width w (pre++ .flip::post)) (height w)) (hx : p.1 = flipMouthX w pre post j) :
    p ∉ cutBoxes w hw cut (pre++ .flip::post) := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  obtain ⟨q, hq⟩ := cutCell_normal w hw cut _ l
  have heX := congrArg (fun p : Cell (width w (pre++ .flip::post)) (height w) => p.1.val)
    (hq.symm.trans he)
  have hh := position_mem w (pre++ .flip::post) q l
  have hj := j.isLt
  have hb := Bool.toNat_le q
  have hpx := congrArg Fin.val hx
  change p.1.val = FiniteTools.radius w+span w pre+w+1+j.val at hpx
  change FiniteTools.radius w+position w (pre++ .flip::post) q l = p.1.val at heX
  rw [positions_split] at hh
  rcases List.mem_append.mp hh with hh | hh
  · have hg := ownedPositions_bounds w hw q pre hh
    omega
  · obtain ⟨x, hx, he⟩ := List.mem_map.mp hh
    simp only [positions, Atom.positions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (h | h) | h
    · omega
    · cases q <;> simp at h <;> omega
    · obtain ⟨z, hz, hez⟩ := List.mem_map.mp h
      have hbound := positions_bounds w hw q post hz
      dsimp [Atom.span] at hez
      omega

def flipMouthNorth (above : Bool) (pre : List Atom) (j : Fin 2) : Bool :=
  if j.val = 0 then exitSide above pre else !(exitSide above pre)

theorem flipMouthNorth_rev (above : Bool) (pre : List Atom) (j : Fin 2) :
    flipMouthNorth above pre j.rev = !(flipMouthNorth above pre j) := by
  fin_cases j <;> simp [flipMouthNorth, Fin.rev]

/-- Each mouth's vertical ray opens onto the corresponding actual outer face. -/
theorem flipMouth_floor (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (above : Bool) (j : Fin 2)
    (p : Cell (width w (pre++ .flip::post)) (height w)) (hx : p.1 = flipMouthX w pre post j)
    (hside : if flipMouthNorth above pre j then p.2.val ≤ FiniteTools.radius w
      else FiniteTools.radius w ≤ p.2.val) : p ∉ walls w (pre++ .flip::post) above := by
  intro hp
  obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
  have hr' := List.mem_toFinset.mp hr
  have hwall := (Rectangle.mem_cells _ _ _ _).mp hp
  have hpx := congrArg Fin.val hx
  change p.1.val = FiniteTools.radius w+span w pre+w+1+j.val at hpx
  have hj := j.isLt
  rw [rectangles_split] at hr'
  rcases List.mem_append.mp hr' with hpre | hrest
  · have hb := rectangles_bounds w 0 above pre hpre
    omega
  · simp only [rectangles, Atom.span, Atom.nextSide, Nat.zero_add] at hrest
    rcases List.mem_append.mp hrest with hflip | hpost
    · cases hs : exitSide above pre <;> fin_cases j <;>
        simp [Atom.rectangles, hs] at hflip <;>
        rcases hflip with rfl | rfl | rfl | rfl <;>
        simp [flipMouthNorth, hs, FiniteTools.radius] at hside hwall hpx <;> omega
    · have hb := rectangles_bounds w (span w pre+(2*w+2)) (!(exitSide above pre)) post hpost
      omega

def workY (w : ℕ) : Fin (height w) :=
  ⟨FiniteTools.radius w, by unfold height FiniteTools.side; omega⟩

theorem program_contains_flip (w length : ℕ) (switch : Bool) :
    ∃ post, program w length switch = [.line (buffer w)]++ .flip::post := by
  unfold program initialAtoms
  exact ⟨_, rfl⟩

end PushPuzzle.PushS.FiniteRouting.Line
