/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineClassifier
public import PushS.FiniteRoutingPlacement
public import PushS.FiniteRoutingLineEndpoints
public import PushFS.RectOrientation
public import PushFS.IsometryInterior

/-! Actual cropped line classifiers in the four emitted physical orientations. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

attribute [local irreducible] width height walls

def railOrientation : Direction → RectOrientation
  | .east => ⟨false,false,false⟩
  | .south => ⟨true,true,false⟩
  | .west => ⟨false,true,true⟩
  | .north => ⟨true,false,true⟩

def railAxis (w : ℕ) (atoms : List Atom) (d : Direction) :=
  (railOrientation d).axis (span w atoms+2) (height w)

def railOffsetX (w : ℕ) : Direction → ℕ
  | .east | .west => FiniteTools.radius w
  | .north | .south => 0

def railOffsetY (w : ℕ) : Direction → ℕ
  | .east | .west => 0
  | .north | .south => FiniteTools.radius w

theorem rail_fits (w : ℕ) (atoms : List Atom) (d : Direction) :
    railOffsetX w d+(railOrientation d).width (span w atoms+2) (height w) ≤ orientedWidth w atoms d ∧
      railOffsetY w d+(railOrientation d).height (span w atoms+2) (height w) ≤ orientedHeight w atoms d := by
  cases d <;> dsimp [railOffsetX,railOffsetY,railOrientation,RectOrientation.width,RectOrientation.height,
    orientedWidth,orientedHeight] <;> unfold width <;> omega

def orientedRailEmbedding (w : ℕ) (atoms : List Atom) (d : Direction) :=
  GridEmbedding.translate (railOffsetX w d) (railOffsetY w d)
    (rail_fits w atoms d).1 (rail_fits w atoms d).2

/-- The cropped guard strip commutes with the exact rotation of the full emitted line rectangle. -/
theorem rotation_rail (w : ℕ) (atoms : List Atom) (d : Direction)
    (p : Cell (span w atoms+2) (height w)) :
    (rotation w atoms d).cells ((railEmbedding w atoms).cells p) =
      (orientedRailEmbedding w atoms d).cells ((railAxis w atoms d).geometry.cells p) := by
  have hpx := p.1.isLt
  cases d <;> apply Prod.ext <;> apply Fin.ext
  · rfl
  · change width w atoms-(FiniteTools.radius w+p.1.val+1) =
      FiniteTools.radius w+(span w atoms+2-(p.1.val+1))
    unfold width
    omega
  · rfl
  · rfl
  · change height w-(0+p.2.val+1) = 0+(height w-(p.2.val+1))
    omega
  · rfl
  · change width w atoms-(FiniteTools.radius w+p.1.val+1) =
      FiniteTools.radius w+(span w atoms+2-(p.1.val+1))
    unfold width
    omega
  · change height w-(0+p.2.val+1) = 0+(height w-(p.2.val+1))
    omega

theorem rail_strong (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ []) (above : Bool)
    (p q : Cell (span w atoms+2) (height w))
    (hp : (railClassifier w hw atoms hne above).name p ≠ .outside)
    (hd : Displacement (railBoard w atoms above) p q) :
    ((railClassifier w hw atoms hne above).name p).Strong
      ((railClassifier w hw atoms hne above).name q) := by
  rcases (railClassifier w hw atoms hne above).displacement p q hd with he | hl
  · exact Or.inl he
  · by_cases hp' : p.2 = railRow w
    · by_cases hq' : q.2 = railRow w
      all_goals simp only [railClassifier,GuardStencils.horizontalOfGuard,GuardStencils.horizontalName,
        hp',hq',ite_true,ite_false,AxisTrack.level] at hl
      all_goals omega
    · exact False.elim (hp (by simp only [railClassifier,GuardStencils.horizontalOfGuard,
        GuardStencils.horizontalName,hp',ite_false]))

def orientedRailChart (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (above : Bool) (d : Direction) : TranslatedAxisChart (orientedWidth w atoms d) (orientedHeight w atoms d) where
  width := (railOrientation d).width (span w atoms+2) (height w)
  height := (railOrientation d).height (span w atoms+2) (height w)
  board := (railAxis w atoms d).geometry.board (railBoard w atoms above)
  dx := railOffsetX w d
  dy := railOffsetY w d
  fits_x := (rail_fits w atoms d).1
  fits_y := (rail_fits w atoms d).2
  classifier := (railAxis w atoms d).classifier (railClassifier w hw atoms hne above)
    (rail_strong w hw atoms hne above)

/-- Every oriented strip guard is an actual wall of the full rotated physical line piece. -/
theorem orientedRailChart_walls (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (above : Bool) (d : Direction)
    (p : Cell (orientedRailChart w hw atoms hne above d).width
      (orientedRailChart w hw atoms hne above d).height)
    (hp : p ∈ (orientedRailChart w hw atoms hne above d).board.walls) :
    (orientedRailChart w hw atoms hne above d).embedding.cells p ∈
      ((rotation w atoms d).board ⟨walls w atoms above,∅⟩).walls := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  have hwall := (railChart_walls w hw atoms hne above q).mpr hq
  change (orientedRailEmbedding w atoms d).cells ((railAxis w atoms d).geometry.cells q) ∈ _
  rw [← rotation_rail]
  exact Finset.mem_map.mpr ⟨(railEmbedding w atoms).cells q,hwall,rfl⟩

def orientedRailName (w : ℕ) : Direction → AxisTrack
  | .east | .west => .horizontal (FiniteTools.radius w)
  | .north | .south => .vertical (FiniteTools.radius w)

/-- The represented coordinate name is the literal physical row or column in every direction. -/
theorem orientedRailChart_row_tag (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (above : Bool) (d : Direction) (p : Cell (span w atoms+2) (height w)) (hp : p.2 = railRow w) :
    AxisTrack.shift (railOffsetX w d) (railOffsetY w d)
      ((orientedRailChart w hw atoms hne above d).classifier.name ((railAxis w atoms d).geometry.cells p)) =
        orientedRailName w d := by
  have hn : (orientedRailChart w hw atoms hne above d).classifier.name
      ((railAxis w atoms d).geometry.cells p) = (railAxis w atoms d).name (.horizontal (FiniteTools.radius w)) := by
    change (railAxis w atoms d).name ((railClassifier w hw atoms hne above).name
      ((railAxis w atoms d).geometry.cells.symm ((railAxis w atoms d).geometry.cells p))) = _
    rw [Equiv.symm_apply_apply]
    congr 1
    simp only [railClassifier,GuardStencils.horizontalOfGuard,GuardStencils.horizontalName,hp,ite_true,railRow]
  rw [hn]
  cases d
  · change AxisTrack.vertical (0+FiniteTools.radius w) = .vertical (FiniteTools.radius w)
    congr 1
    omega
  · change AxisTrack.horizontal (0+FiniteTools.radius w) = .horizontal (FiniteTools.radius w)
    congr 1
    omega
  · change AxisTrack.vertical (0+(height w-1-FiniteTools.radius w)) = .vertical (FiniteTools.radius w)
    congr 1
    unfold height FiniteTools.side
    omega
  · change AxisTrack.horizontal (0+(height w-1-FiniteTools.radius w)) = .horizontal (FiniteTools.radius w)
    congr 1
    unfold height FiniteTools.side
    omega

def railSlot (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (phase : Bool) (l : Label w atoms) :
    Cell (span w atoms+2) (height w) :=
  (⟨position w atoms phase l,by
    have hh := positions_bounds w hw phase atoms (position_mem w atoms phase l)
    have hq := Bool.toNat_le phase
    omega⟩,railRow w)

private theorem railSlot_cell (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (phase : Bool)
    (l : Label w atoms) :
    (railEmbedding w atoms).cells (railSlot w hw atoms phase l) = cell w hw atoms phase l := by
  apply Prod.ext <;> apply Fin.ext
  · rfl
  · change 0+FiniteTools.radius w = FiniteTools.radius w
    omega

/-- All owned line and tool labels are represented at both normal phases in the actual oriented rail. -/
theorem orientedRailChart_normal (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (above : Bool) (d : Direction) (phase : Bool) (l : Label w atoms) :
    ∃ q, (orientedRailChart w hw atoms hne above d).embedding.cells q =
        (rotation w atoms d).cells (cell w hw atoms phase l) ∧
      AxisTrack.shift (railOffsetX w d) (railOffsetY w d)
        ((orientedRailChart w hw atoms hne above d).classifier.name q) = orientedRailName w d := by
  refine ⟨(railAxis w atoms d).geometry.cells (railSlot w hw atoms phase l),?_,?_⟩
  · change (orientedRailEmbedding w atoms d).cells
      ((railAxis w atoms d).geometry.cells (railSlot w hw atoms phase l)) = _
    rw [← rotation_rail,railSlot_cell]
  · exact orientedRailChart_row_tag w hw atoms hne above d _ rfl

/-- The only unsafe chart cells are the literal low first slot and high final slot. -/
theorem orientedRailChart_interior_or_ends (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ [])
    (above : Bool) (d : Direction)
    (p : Cell (orientedRailChart w hw atoms hne above d).width
      (orientedRailChart w hw atoms hne above d).height)
    (hp : (orientedRailChart w hw atoms hne above d).classifier.name p ≠ .outside) :
    Interior p ∨
      (orientedRailChart w hw atoms hne above d).embedding.cells p = (rotation w atoms d).cells (startCell w atoms) ∨
      (orientedRailChart w hw atoms hne above d).embedding.cells p =
        (rotation w atoms d).cells (cell w hw atoms true (lastLabel w atoms)) := by
  obtain ⟨q,rfl⟩ := (railAxis w atoms d).geometry.cells.surjective p
  change (railAxis w atoms d).name ((railClassifier w hw atoms hne above).name
    ((railAxis w atoms d).geometry.cells.symm ((railAxis w atoms d).geometry.cells q))) ≠ .outside at hp
  rw [Equiv.symm_apply_apply] at hp
  have hrow : q.2 = railRow w := by
    by_contra hn
    apply hp
    apply ((railAxis w atoms d).outside _).mpr
    exact ite_eq_right hn
  have hy : q.2.val = FiniteTools.radius w := congrArg Fin.val hrow
  have hx := q.1.isLt
  have hplace : (orientedRailChart w hw atoms hne above d).embedding.cells
      ((railAxis w atoms d).geometry.cells q) = (rotation w atoms d).cells ((railEmbedding w atoms).cells q) :=
    (rotation_rail w atoms d q).symm
  by_cases h0 : q.1.val = 0
  · right
    left
    apply hplace.trans
    apply congrArg (rotation w atoms d).cells
    apply Prod.ext <;> apply Fin.ext
    · change FiniteTools.radius w+q.1.val = FiniteTools.radius w
      omega
    · change 0+q.2.val = FiniteTools.radius w
      omega
  · by_cases hlast : q.1.val+1 = span w atoms+2
    · right
      right
      apply hplace.trans
      apply congrArg (rotation w atoms d).cells
      apply Prod.ext <;> apply Fin.ext
      · change FiniteTools.radius w+q.1.val = FiniteTools.radius w+position w atoms true (lastLabel w atoms)
        rw [position_last]
        simp only [Bool.toNat_true]
        omega
      · change 0+q.2.val = FiniteTools.radius w
        omega
    · left
      apply (railAxis w atoms d).geometry.interior
      refine ⟨by omega,by omega,?_,?_⟩
      · unfold FiniteTools.radius at hy
        omega
      · unfold height FiniteTools.side
        unfold FiniteTools.radius at *
        omega

end PushPuzzle.PushS.FiniteRouting.Line
