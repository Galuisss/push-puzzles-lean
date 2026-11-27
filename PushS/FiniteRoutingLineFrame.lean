/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineStock
import Mathlib.Tactic.FinCases

/-! Explicit narrow active floor for complete routing-line execution and ambient replay. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

def active (w : ℕ) (atoms : List Atom) (above : Bool) : Finset (Cell (width w atoms) (height w)) :=
  Finset.univ.filter fun p =>
    FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+span w atoms+2 ∧
      FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ p ∉ walls w atoms above

def macroBoard (w : ℕ) (atoms : List Atom) (above : Bool) : Board (width w atoms) (height w) :=
  FiniteWireFrame.board (active w atoms above) ∅

attribute [local irreducible] width height

theorem cutCell_active (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above : Bool) (l : Label w atoms) :
    cutCell w hw cut atoms l ∈ active w atoms above := by
  obtain ⟨q, hq⟩ := cutCell_normal w hw cut atoms l
  rw [hq]
  have hb := positions_bounds w hw q atoms (position_mem w atoms q l)
  have hq := Bool.toNat_le q
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, row_floor w atoms above _ rfl⟩
  all_goals dsimp [cell]; unfold FiniteTools.radius at *; omega

theorem cutBoxes_macro_floor (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above : Bool) :
    Disjoint (cutBoxes w hw cut atoms) (macroBoard w atoms above).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact (FiniteWireFrame.floor_iff _ _ _).mpr (cutCell_active w hw cut atoms above l)

theorem outer_macro_free (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above north : Bool)
    (x : Fin (width w atoms)) (hx : FiniteTools.radius w-1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+span w atoms+2) :
    Free (macroBoard w atoms above) (cutBoxes w hw cut atoms) (outerCell w atoms north x) := by
  refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, (outer_free w hw cut atoms above north x).2⟩
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hx, hx', ?_, ?_, outer_floor w atoms above north x⟩
  all_goals cases north <;> dsimp [outerCell, laneY, FiniteTools.radius] <;> omega

private theorem outer_macro_walk (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (above north : Bool)
    (x y : Fin (width w atoms)) (hx : FiniteTools.radius w-1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+span w atoms+2)
    (hy : FiniteTools.radius w-1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w atoms+2) :
    Reachable (macroBoard w atoms above) (some 1)
      ⟨outerCell w atoms north x, cutBoxes w hw cut atoms⟩
      ⟨outerCell w atoms north y, cutBoxes w hw cut atoms⟩ := by
  apply walk_horizontal (cutBoxes_macro_floor w hw cut atoms above)
  intro z hz hz'
  exact outer_macro_free w hw cut atoms above north z (by omega) (by omega)

private theorem flipMouthX_bounds (w : ℕ) (pre post : List Atom) (j : Fin 2) :
    FiniteTools.radius w-1 ≤ (flipMouthX w pre post j).val ∧
      (flipMouthX w pre post j).val ≤ FiniteTools.radius w+span w (pre++ .flip::post)+2 := by
  have hj := j.isLt
  dsimp [flipMouthX]
  simp only [span_append, span_cons, Atom.span]
  omega

theorem flipMouth_macro_free (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (pre post : List Atom) (above : Bool) (j : Fin 2)
    (p : Cell (width w (pre++ .flip::post)) (height w)) (hx : p.1 = flipMouthX w pre post j)
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1)
    (hside : if flipMouthNorth above pre j then p.2.val ≤ FiniteTools.radius w
      else FiniteTools.radius w ≤ p.2.val) :
    Free (macroBoard w (pre++ .flip::post) above) (cutBoxes w hw cut (pre++ .flip::post)) p := by
  refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, flipMouth_no_box w hw cut pre post j p hx⟩
  have hb := flipMouthX_bounds w pre post j
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hx ▸ hb.1, hx ▸ hb.2, hy, hy', flipMouth_floor w hw pre post above j p hx hside⟩

private theorem flipMouth_macro_crossing (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (pre post : List Atom)
    (above : Bool) (j : Fin 2) :
    Reachable (macroBoard w (pre++ .flip::post) above) (some 1)
      ⟨outerCell w _ (flipMouthNorth above pre j) (flipMouthX w pre post j),
        cutBoxes w hw cut (pre++ .flip::post)⟩
      ⟨outerCell w _ (flipMouthNorth above pre j.rev) (flipMouthX w pre post j.rev),
        cutBoxes w hw cut (pre++ .flip::post)⟩ := by
  let atoms := pre++ .flip::post
  have hd := cutBoxes_macro_floor w hw cut atoms above
  have h1 : Reachable (macroBoard w atoms above) (some 1)
      ⟨outerCell w atoms (flipMouthNorth above pre j) (flipMouthX w pre post j), cutBoxes w hw cut atoms⟩
      ⟨(flipMouthX w pre post j, workY w), cutBoxes w hw cut atoms⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply flipMouth_macro_free w hw cut pre post above j _ rfl
    all_goals cases hs : flipMouthNorth above pre j <;>
      simp [laneY, workY, hs] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  have h2 : Reachable (macroBoard w atoms above) (some 1)
      ⟨(flipMouthX w pre post j, workY w), cutBoxes w hw cut atoms⟩
      ⟨(flipMouthX w pre post j.rev, workY w), cutBoxes w hw cut atoms⟩ := by
    apply walk_horizontal hd
    intro x hx hx'
    have hchoice : x = flipMouthX w pre post 0 ∨ x = flipMouthX w pre post 1 := by
      by_cases h0 : x.val = FiniteTools.radius w+span w pre+w+1
      · exact Or.inl (Fin.ext h0)
      · apply Or.inr
        apply Fin.ext
        fin_cases j <;> simp [flipMouthX, Fin.rev] at hx hx' ⊢ <;> omega
    rcases hchoice with rfl | rfl
    all_goals apply flipMouth_macro_free w hw cut pre post above _ _ rfl
    all_goals first | (change _ ≤ FiniteTools.radius w; unfold FiniteTools.radius; omega) |
      (change FiniteTools.radius w ≤ _; omega) | (split <;> exact le_refl _)
  have h3 : Reachable (macroBoard w atoms above) (some 1)
      ⟨(flipMouthX w pre post j.rev, workY w), cutBoxes w hw cut atoms⟩
      ⟨outerCell w atoms (flipMouthNorth above pre j.rev) (flipMouthX w pre post j.rev), cutBoxes w hw cut atoms⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply flipMouth_macro_free w hw cut pre post above j.rev _ rfl
    all_goals cases hs : flipMouthNorth above pre j.rev <;>
      simp [laneY, workY, hs] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  exact h1.trans (h2.trans h3)

private theorem outer_macro_connected (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (pre post : List Atom)
    (above north north' : Bool) (x y : Fin (width w (pre++ .flip::post)))
    (hx : FiniteTools.radius w-1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+span w (pre++ .flip::post)+2)
    (hy : FiniteTools.radius w-1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w (pre++ .flip::post)+2) :
    Reachable (macroBoard w (pre++ .flip::post) above) (some 1)
      ⟨outerCell w _ north x, cutBoxes w hw cut (pre++ .flip::post)⟩
      ⟨outerCell w _ north' y, cutBoxes w hw cut (pre++ .flip::post)⟩ := by
  by_cases hn : north = north'
  · subst north'
    exact outer_macro_walk w hw cut _ above north x y hx hx' hy hy'
  · let j : Fin 2 := if north = exitSide above pre then 0 else 1
    have hj : flipMouthNorth above pre j = north := by
      cases hnorth : north <;> cases hs : exitSide above pre <;>
        simp [j, flipMouthNorth, hnorth, hs]
    have hj' : flipMouthNorth above pre j.rev = north' := by
      rw [flipMouthNorth_rev, hj]
      cases north <;> cases north' <;> simp_all
    have hc := flipMouth_macro_crossing w hw cut pre post above j
    rw [hj, hj'] at hc
    have hb := flipMouthX_bounds w pre post j
    have hb' := flipMouthX_bounds w pre post j.rev
    exact (outer_macro_walk w hw cut _ above north x _ hx hx' hb.1 hb.2).trans
      (hc.trans (outer_macro_walk w hw cut _ above north' _ y hb'.1 hb'.2 hy hy'))

theorem outer_macro_connected_of_flip (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (hflip : ∃ pre post, atoms = pre++ .flip::post) (above north north' : Bool)
    (x y : Fin (width w atoms)) (hx : FiniteTools.radius w-1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+span w atoms+2)
    (hy : FiniteTools.radius w-1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w atoms+2) :
    Reachable (macroBoard w atoms above) (some 1)
      ⟨outerCell w atoms north x, cutBoxes w hw cut atoms⟩
      ⟨outerCell w atoms north' y, cutBoxes w hw cut atoms⟩ := by
  obtain ⟨pre, post, rfl⟩ := hflip
  exact outer_macro_connected w hw cut pre post above north north' x y hx hx' hy hy'

def outerHubX (w : ℕ) (atoms : List Atom) : Fin (width w atoms) :=
  ⟨FiniteTools.radius w+1, by unfold width FiniteTools.radius; omega⟩

def outerHub (w : ℕ) (atoms : List Atom) : Cell (width w atoms) (height w) :=
  outerCell w atoms true (outerHubX w atoms)

end PushPuzzle.PushS.FiniteRouting.Line
