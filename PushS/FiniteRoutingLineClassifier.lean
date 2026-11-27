/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineBoard
public import PushFS.GuardRails

/-! A complete static chart on the actually guarded portion of each emitted straight line. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

attribute [local irreducible] width height

def railEmbedding (w : ℕ) (atoms : List Atom) :
    GridEmbedding (span w atoms+2) (height w) (width w atoms) (height w) :=
  GridEmbedding.translate (FiniteTools.radius w) 0
    (by unfold width; omega) (by omega)

/-- The full actual wall restriction along every working column. -/
def railBoard (w : ℕ) (atoms : List Atom) (above : Bool) : Board (span w atoms+2) (height w) :=
  (railEmbedding w atoms).pullback ⟨walls w atoms above,∅⟩

def railRow (w : ℕ) : Fin (height w) :=
  ⟨FiniteTools.radius w, by unfold height FiniteTools.side; omega⟩

/-- Side-changing tool walls guard every column of the cropped physical rail. -/
theorem rail_horizontalGuard (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ []) (above : Bool) :
    GuardStencils.HorizontalGuard (railBoard w atoms above) (railRow w) := by
  intro x u v hu hv
  let gx : Fin (width w atoms) :=
    ⟨FiniteTools.radius w+x.val, by unfold width; have hx := x.isLt; omega⟩
  have hg := rail_guard w hw atoms hne above gx
    (by dsimp [gx]; omega) (by dsimp [gx]; have hx := x.isLt; omega)
  rcases hg with hg | hg
  · left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he : (railEmbedding w atoms).cells (x,u) = northCell w atoms gx := by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · change 0+u.val = FiniteTools.radius w-1
        change u.val+1 = FiniteTools.radius w at hu
        omega
    change (railEmbedding w atoms).cells (x,u) ∈ walls w atoms above
    rw [he]
    exact hg
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he : (railEmbedding w atoms).cells (x,v) = southCell w atoms gx := by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · change 0+v.val = FiniteTools.radius w+1
        change FiniteTools.radius w+1 = v.val at hv
        omega
    change (railEmbedding w atoms).cells (x,v) ∈ walls w atoms above
    rw [he]
    exact hg

def railClassifier (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ []) (above : Bool) :
    AxisClassifier (railBoard w atoms above) :=
  GuardStencils.horizontalOfGuard (railRow w) (rail_horizontalGuard w hw atoms hne above)

/-- The literal row chart, with exact ambient walls and both shared endpoint columns. -/
def railChart (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ []) (above : Bool) :
    TranslatedAxisChart (width w atoms) (height w) where
  width := span w atoms+2
  height := height w
  board := railBoard w atoms above
  dx := FiniteTools.radius w
  dy := 0
  fits_x := by unfold width; omega
  fits_y := by omega
  classifier := railClassifier w hw atoms hne above

theorem railChart_walls (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hne : atoms ≠ []) (above : Bool) :
    (railChart w hw atoms hne above).embedding.WallsAgree (railChart w hw atoms hne above).board
      (⟨walls w atoms above,∅⟩ : Board (width w atoms) (height w)) :=
  (railEmbedding w atoms).pullback_walls _

end PushPuzzle.PushS.FiniteRouting.Line
