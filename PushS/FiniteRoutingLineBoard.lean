/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLine
public import PushS.FiniteWalls

/-! Actual finite thick-wall straight-line storage pieces emitted from routing programs. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

def width (w : ℕ) (atoms : List Atom) : ℕ := 2*FiniteTools.radius w+span w atoms+2

def height (w : ℕ) : ℕ := FiniteTools.side w

/-- Complete owned physical box indices, with the last endpoint included once. -/
abbrev Label (w : ℕ) (atoms : List Atom) := Fin (positions w false atoms).length

def position (w : ℕ) (atoms : List Atom) (q : Bool) (l : Label w atoms) : ℕ :=
  (positions w q atoms).get ⟨l.val, by simpa only [positions_length] using l.isLt⟩

theorem position_mem (w : ℕ) (atoms : List Atom) (q : Bool) (l : Label w atoms) :
    position w atoms q l ∈ positions w q atoms := List.get_mem _ _

def cell (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (l : Label w atoms) :
    Cell (width w atoms) (height w) :=
  (⟨FiniteTools.radius w+position w atoms q l, by
      have hh := positions_bounds w hw q atoms (position_mem w atoms q l)
      have hq := Bool.toNat_le q
      unfold width FiniteTools.radius
      omega⟩,
   ⟨FiniteTools.radius w, by unfold height FiniteTools.side; omega⟩)

attribute [local irreducible] width height

theorem cell_injective (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) :
    Function.Injective (cell w hw atoms q) := by
  intro a b he
  have hx := congrArg (fun p : Cell (width w atoms) (height w) => p.1.val) he
  have he' : position w atoms q a = position w atoms q b := by
    change FiniteTools.radius w+position w atoms q a = FiniteTools.radius w+position w atoms q b at hx
    omega
  have hi := (List.nodup_iff_injective_get.mp (positions_nodup w hw q atoms)) he'
  apply Fin.ext
  exact congrArg (fun i : Fin (positions w q atoms).length => i.val) hi

def boxes (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) :
    Finset (Cell (width w atoms) (height w)) := Finset.univ.image (cell w hw atoms q)

def walls (w : ℕ) (atoms : List Atom) (above : Bool) :
    Finset (Cell (width w atoms) (height w)) :=
  (rectangles w 0 above atoms).toFinset.biUnion fun r => r.cells (width w atoms) (height w)

private theorem walls_squareCovered (w : ℕ) (hw : 0 < w) (atoms : List Atom) (above : Bool)
    (ha : ∀ a ∈ atoms, a.Valid w) : FiniteFreeze.SquareCovered w (walls w atoms above) := by
  intro p hp
  obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
  have hh := rectangles_thick w 0 above atoms ha (List.mem_toFinset.mp hr)
  obtain ⟨x,y,hx,hx',hy,hy',hfull⟩ := r.squareCovered _ _ w hw hh.1 hh.2 p hp
  refine ⟨x,y,hx,hx',hy,hy',?_⟩
  intro q hqx hqx' hqy hqy'
  exact Finset.mem_biUnion.mpr ⟨r,hr,hfull q hqx hqx' hqy hqy'⟩

/-- The entire working row is literal floor, including all support and destination cells. -/
theorem row_floor (w : ℕ) (atoms : List Atom) (above : Bool)
    (p : Cell (width w atoms) (height w)) (hpy : p.2.val = FiniteTools.radius w) :
    p ∉ walls w atoms above := by
  intro hp
  obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
  have hh := rectangles_off_row w 0 above atoms (List.mem_toFinset.mp hr)
  have hb := (r.mem_cells _ _ p).mp hp
  omega

/-- All actual line and tool wall marks remain in the narrow strip around their physical segment. -/
theorem walls_bounds (w : ℕ) (atoms : List Atom) (above : Bool)
    {p : Cell (width w atoms) (height w)} (hp : p ∈ walls w atoms above) :
    FiniteTools.radius w ≤ p.1.val ∧ p.1.val < FiniteTools.radius w+span w atoms+2 ∧
      FiniteTools.radius w-w ≤ p.2.val ∧ p.2.val < FiniteTools.radius w+w+1 := by
  obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp hp
  have hb := rectangles_bounds w 0 above atoms (List.mem_toFinset.mp hr)
  have hy := rectangles_band w 0 above atoms (List.mem_toFinset.mp hr)
  have hh := (r.mem_cells _ _ _).mp hp
  omega

def northCell (w : ℕ) (atoms : List Atom) (x : Fin (width w atoms)) : Cell (width w atoms) (height w) :=
  (x, ⟨FiniteTools.radius w-1, by unfold height FiniteTools.side FiniteTools.radius; omega⟩)

def southCell (w : ℕ) (atoms : List Atom) (x : Fin (width w atoms)) : Cell (width w atoms) (height w) :=
  (x, ⟨FiniteTools.radius w+1, by unfold height FiniteTools.side FiniteTools.radius; omega⟩)

/-- Every physical rail column has an actual protecting wall immediately above or below it. -/
theorem rail_guard (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (above : Bool) (x : Fin (width w atoms))
    (hx : FiniteTools.radius w ≤ x.val) (hx' : x.val < FiniteTools.radius w+span w atoms+2) :
    northCell w atoms x ∈ walls w atoms above ∨ southCell w atoms x ∈ walls w atoms above := by
  obtain ⟨r, hr, hxr, hxr', hrow⟩ := column_guard w hw 0 above atoms hne (by simpa using hx) (by simpa using hx')
  rcases hrow with hn | hs
  · left
    apply Finset.mem_biUnion.mpr
    refine ⟨r, List.mem_toFinset.mpr hr, ?_⟩
    exact (r.mem_cells _ _ _).mpr ⟨hxr,hxr',hn.1,hn.2⟩
  · right
    apply Finset.mem_biUnion.mpr
    refine ⟨r, List.mem_toFinset.mpr hr, ?_⟩
    exact (r.mem_cells _ _ _).mpr ⟨hxr,hxr',hs.1,hs.2⟩

def hub (w : ℕ) (atoms : List Atom) : Cell (width w atoms) (height w) :=
  (⟨0, by unfold width FiniteTools.radius; omega⟩,
   ⟨0, by unfold height FiniteTools.side FiniteTools.radius; omega⟩)

theorem hub_not_wall (w : ℕ) (atoms : List Atom) (above : Bool) : hub w atoms ∉ walls w atoms above := by
  intro hp
  obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
  have hh := rectangles_bounds w 0 above atoms (List.mem_toFinset.mp hr)
  have hb := (r.mem_cells _ _ _).mp hp
  have hby := hb.2.2.1
  change r.y ≤ 0 at hby
  omega

theorem hub_not_box (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) :
    hub w atoms ∉ boxes w hw atoms q := by
  intro hp
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hp
  have hy := congrArg (fun p : Cell (width w atoms) (height w) => p.2.val) hl
  change FiniteTools.radius w = 0 at hy
  unfold FiniteTools.radius at hy
  omega

/-- The complete exact-length line program has uniformly frozen walls at force `k`. -/
theorem program_walls_thick (k length : ℕ) (switch above : Bool) :
    FiniteFreeze.Thick k (walls (k+1) (program (k+1) length switch) above) :=
  FiniteFreeze.thick_of_squareCovered (by omega)
    (walls_squareCovered (k+1) (by omega) _ above (program_valid (k+1) length switch))

end PushPuzzle.PushS.FiniteRouting.Line
