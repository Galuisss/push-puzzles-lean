/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineContract
import Mathlib.Tactic.FinCases

/-! The actual action footprint excludes the unused guarded end caps of routed line programs. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Action

open PushFS

def UsedPoint (w : ℕ) (atoms : List Atom) (above last : Bool)
    (p : Cell (width w atoms) (height w)) : Prop :=
  (p.2.val = FiniteTools.radius w ∧ FiniteTools.radius w ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+span w atoms+1) ∨
    (FiniteTools.radius w+1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+span w atoms) ∨
    (last = true ∧ FiniteTools.radius w+span w atoms < p.1.val ∧ Exposed w (exitSide above atoms) p.2.val)


instance (w : ℕ) (atoms : List Atom) (above last : Bool) (p : Cell (width w atoms) (height w)) :
    Decidable (UsedPoint w atoms above last p) := by unfold UsedPoint Exposed; infer_instance

def active (w : ℕ) (atoms : List Atom) (above last : Bool) : Finset (Cell (width w atoms) (height w)) :=
  (Line.active w atoms above).filter (UsedPoint w atoms above last)

variable {last : Bool}

def macroBoard (w : ℕ) (atoms : List Atom) (above : Bool) : Board (width w atoms) (height w) :=
  FiniteWireFrame.board (active w atoms above last) ∅

attribute [local irreducible] width height

theorem cutCell_active (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above : Bool) (l : Label w atoms) :
    cutCell w hw cut atoms l ∈ active w atoms above last := by
  refine Finset.mem_filter.mpr ⟨Line.cutCell_active w hw cut atoms above l, ?_⟩
  apply Or.inl
  refine ⟨(cutCell_coordinates w hw cut atoms l).2,?_⟩
  obtain ⟨q,hq⟩ := cutCell_normal w hw cut atoms l
  have hb := positions_bounds w hw q atoms (position_mem w atoms q l)
  have hqb := Bool.toNat_le q
  rw [hq]
  dsimp [cell]
  omega

theorem cutBoxes_macro_floor (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above : Bool) :
    Disjoint (cutBoxes w hw cut atoms) (macroBoard (last:=last) w atoms above).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact (FiniteWireFrame.floor_iff _ _ _).mpr (cutCell_active w hw cut atoms above l)

theorem lift_free (w : ℕ) (atoms : List Atom) (above : Bool) (boxes : Finset (Cell (width w atoms) (height w)))
    (p : Cell (width w atoms) (height w)) (hp : Free (Line.macroBoard w atoms above) boxes p)
    (hu : UsedPoint w atoms above last p) : Free (macroBoard (last:=last) w atoms above) boxes p :=
  ⟨(FiniteWireFrame.floor_iff _ _ _).mpr (Finset.mem_filter.mpr
    ⟨(FiniteWireFrame.floor_iff _ _ _).mp hp.1,hu⟩),hp.2⟩

theorem outer_macro_free (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above north : Bool)
    (x : Fin (width w atoms)) (hx : FiniteTools.radius w+1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+span w atoms) :
    Free (macroBoard (last:=last) w atoms above) (cutBoxes w hw cut atoms) (outerCell w atoms north x) := by
  apply lift_free w atoms above _ _ (Line.outer_macro_free w hw cut atoms above north x (by omega) (by omega))
  exact Or.inr (Or.inl ⟨hx,hx'⟩)

private theorem outer_macro_walk (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (above north : Bool)
    (x y : Fin (width w atoms)) (hx : FiniteTools.radius w+1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+span w atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w atoms) :
    Reachable (macroBoard (last:=last) w atoms above) (some 1)
      ⟨outerCell w atoms north x, cutBoxes w hw cut atoms⟩
      ⟨outerCell w atoms north y, cutBoxes w hw cut atoms⟩ := by
  apply walk_horizontal (cutBoxes_macro_floor w hw cut atoms above)
  intro z hz hz'
  exact outer_macro_free w hw cut atoms above north z (by omega) (by omega)

private theorem flipMouthX_bounds (w : ℕ) (pre post : List Atom) (j : Fin 2) :
    FiniteTools.radius w+1 ≤ (flipMouthX w pre post j).val ∧
      (flipMouthX w pre post j).val ≤ FiniteTools.radius w+span w (pre++ .flip::post) := by
  have hj := j.isLt
  dsimp [flipMouthX]
  simp only [span_append,span_cons,Atom.span]
  omega

theorem flipMouth_macro_free (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (pre post : List Atom) (above : Bool) (j : Fin 2)
    (p : Cell (width w (pre++ .flip::post)) (height w)) (hx : p.1 = flipMouthX w pre post j)
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1)
    (hside : if flipMouthNorth above pre j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) :
    Free (macroBoard (last:=last) w (pre++ .flip::post) above) (cutBoxes w hw cut (pre++ .flip::post)) p := by
  apply lift_free w _ above _ _ (Line.flipMouth_macro_free w hw cut pre post above j p hx hy hy' hside)
  apply Or.inr; apply Or.inl
  have hj := j.isLt
  rw [hx]
  dsimp [flipMouthX]
  simp only [span_append,span_cons,Atom.span]
  omega

private theorem flipMouth_macro_crossing (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (pre post : List Atom)
    (above : Bool) (j : Fin 2) :
    Reachable (macroBoard (last:=last) w (pre++ .flip::post) above) (some 1)
      ⟨outerCell w _ (flipMouthNorth above pre j) (flipMouthX w pre post j),
        cutBoxes w hw cut (pre++ .flip::post)⟩
      ⟨outerCell w _ (flipMouthNorth above pre j.rev) (flipMouthX w pre post j.rev),
        cutBoxes w hw cut (pre++ .flip::post)⟩ := by
  let atoms := pre++ .flip::post
  have hd := cutBoxes_macro_floor (last:=last) w hw cut atoms above
  have h1 : Reachable (macroBoard (last:=last) w atoms above) (some 1)
      ⟨outerCell w atoms (flipMouthNorth above pre j) (flipMouthX w pre post j), cutBoxes w hw cut atoms⟩
      ⟨(flipMouthX w pre post j, workY w), cutBoxes w hw cut atoms⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply flipMouth_macro_free w hw cut pre post above j _ rfl
    all_goals cases hs : flipMouthNorth above pre j <;>
      simp [laneY, workY, hs] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  have h2 : Reachable (macroBoard (last:=last) w atoms above) (some 1)
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
  have h3 : Reachable (macroBoard (last:=last) w atoms above) (some 1)
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
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+span w (pre++ .flip::post))
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w (pre++ .flip::post)) :
    Reachable (macroBoard (last:=last) w (pre++ .flip::post) above) (some 1)
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
    have hc := flipMouth_macro_crossing (last:=last) w hw cut pre post above j
    rw [hj, hj'] at hc
    have hb := flipMouthX_bounds w pre post j
    have hb' := flipMouthX_bounds w pre post j.rev
    exact (outer_macro_walk w hw cut _ above north x _ hx hx' hb.1 hb.2).trans
      (hc.trans (outer_macro_walk w hw cut _ above north' _ y hb'.1 hb'.2 hy hy'))

theorem outer_macro_connected_of_flip (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (hflip : ∃ pre post, atoms = pre++ .flip::post) (above north north' : Bool)
    (x y : Fin (width w atoms)) (hx : FiniteTools.radius w+1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+span w atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w atoms) :
    Reachable (macroBoard (last:=last) w atoms above) (some 1)
      ⟨outerCell w atoms north x, cutBoxes w hw cut atoms⟩
      ⟨outerCell w atoms north' y, cutBoxes w hw cut atoms⟩ := by
  obtain ⟨pre, post, rfl⟩ := hflip
  exact outer_macro_connected w hw cut pre post above north north' x y hx hx' hy hy'


theorem outer_reachable (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above : Bool)
    (hflip : ∃ pre post, atoms = pre++ .flip::post) (north : Bool)
    (p : Cell (width w atoms) (height w)) (hx : FiniteTools.radius w+1 ≤ p.1.val)
    (hx' : p.1.val ≤ FiniteTools.radius w+span w atoms) (hy : p.2.val = (laneY w north).val) :
    Reachable (macroBoard (last:=last) w atoms above) (some 1)
      ⟨outerHub w atoms,cutBoxes w hw cut atoms⟩ ⟨p,cutBoxes w hw cut atoms⟩ := by
  have he : p = outerCell w atoms north p.1 := Prod.ext rfl (Fin.ext hy)
  rw [he]
  exact outer_macro_connected_of_flip w hw cut atoms hflip above true north (outerHubX w atoms) p.1
    (by dsimp [outerHubX]; omega) (by dsimp [outerHubX]; omega) hx hx'

theorem outer_return (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (above : Bool)
    (hflip : ∃ pre post, atoms = pre++ .flip::post) (north : Bool)
    (p : Cell (width w atoms) (height w)) (hx : FiniteTools.radius w+1 ≤ p.1.val)
    (hx' : p.1.val ≤ FiniteTools.radius w+span w atoms) (hy : p.2.val = (laneY w north).val) :
    Reachable (macroBoard (last:=last) w atoms above) (some 1)
      ⟨p,cutBoxes w hw cut atoms⟩ ⟨outerHub w atoms,cutBoxes w hw cut atoms⟩ := by
  have he : p = outerCell w atoms north p.1 := Prod.ext rfl (Fin.ext hy)
  rw [he]
  exact outer_macro_connected_of_flip w hw cut atoms hflip above north true p.1 (outerHubX w atoms)
    hx hx' (by dsimp [outerHubX]; omega) (by dsimp [outerHubX]; omega)

end PushPuzzle.PushS.FiniteRouting.Line.Action
