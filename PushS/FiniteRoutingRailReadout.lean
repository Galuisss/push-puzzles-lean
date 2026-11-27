/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionContract
public import PushS.FiniteRoutingLineReadout
public import PushS.FiniteRoutingLineCompletion

/-! Source components and literal finite rail floor determine the horizontal readout tags. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Readout

open PushFS

/-- Every pair of concrete normal slots shares a component using only the literal finite rail. -/
theorem rail_connected (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool)
    {W H : ℕ} (e : GridEmbedding (width w atoms) (height w) W H) (B : Board W H)
    (floor : ∀ k, e.cells (rail w atoms k) ∉ B.walls) (i j : Label w atoms) :
    SameComponent B (e.cells (cell w hw atoms q i)) (e.cells (cell w hw atoms q j)) := by
  have hh := sameComponent_line (n:=span w atoms+1) (d:=e.direction .east) (B:=B)
    (fun k => e.cells (rail w atoms k)) floor
    (by intro k; apply e.adjacent .east; dsimp [Adjacent,rail]; exact ⟨by omega,rfl⟩)
    (railIndex w hw atoms q i) (railIndex w hw atoms q j)
    (by
      have hp := positions_bounds w hw q atoms (position_mem w atoms q i)
      have hq := Bool.toNat_le q
      dsimp [railIndex]; omega)
    (by
      have hp := positions_bounds w hw q atoms (position_mem w atoms q j)
      have hq := Bool.toNat_le q
      dsimp [railIndex]; omega)
  simpa only [rail_slot] using hh

variable {I : PushFS.Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {A : ComponentTracks I}

/-- Two actual source identities with different x coordinates fix the horizontal kind of their common source component. -/
theorem horizontal_source (i j : L)
    (hc : component I.board (M.source i) = component I.board (M.source j))
    (hx : (M.source i).1.val ≠ (M.source j).1.val) (y : ℕ) (hy : (M.source i).2.val = y) :
    A.name (M.source i) = .horizontal y := by
  have hmem : M.source i ∈ I.initial.boxes := by
    rw [←M.source_image]
    exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have ha := A.active _ hmem
  have hn := A.name_eq_of_component_eq hc
  change A.name (M.source i) = A.name (M.source j) at hn
  have hi := A.supported (M.source i)
  have hj := A.supported (M.source j)
  rw [←hn] at hj
  cases hname : A.name (M.source i) with
  | outside => exact False.elim (ha hname)
  | horizontal row =>
    simp only [hname,AxisTrack.Supports] at hi
    exact congrArg AxisTrack.horizontal (by omega)
  | vertical col =>
    simp only [hname,AxisTrack.Supports] at hi hj
    exact False.elim (hx (by omega))
  | sink x y =>
    simp only [hname,AxisTrack.Supports] at hi hj
    exact False.elim (hx (by omega))

/-- Construct a line glyph and its track names from the complete slot table. -/
def LineGlyph.of_rail_slots (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hspan : 0 < span w atoms) (above : Bool)
    (dx dy : ℕ) (fit_x : dx+width w atoms ≤ I.width) (fit_y : dy+height w ≤ I.height)
    (initial target : Bool) (labels : Label w atoms → L)
    (sources : ∀ l, M.source (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (cell w hw atoms initial l))
    (targets : ∀ l, M.target (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (cell w hw atoms target l))
    (walls : ∀ p ∈ Line.walls w atoms above, (GridEmbedding.translate dx dy fit_x fit_y).cells p ∈ I.board.walls)
    (floor : ∀ i, (GridEmbedding.translate dx dy fit_x fit_y).cells (rail w atoms i) ∉ I.board.walls) :
    LineGlyph M A w atoms above := by
  have component_eq (i j : Label w atoms) : component I.board (M.source (labels i)) = component I.board (M.source (labels j)) := by
    rw [sources,sources]
    exact component_eq_iff.mpr (rail_connected w hw atoms initial _ I.board floor i j)
  have hfirst : A.name (M.source (labels (cutFirstLabel w atoms))) = .horizontal (dy+FiniteTools.radius w) := by
    apply horizontal_source (labels (cutFirstLabel w atoms)) (labels (cutLastLabel w atoms)) (component_eq _ _)
    · rw [sources,sources]
      change dx+(FiniteTools.radius w+position w atoms initial (cutFirstLabel w atoms)) ≠
        dx+(FiniteTools.radius w+position w atoms initial (cutLastLabel w atoms))
      rw [position_first,Terminal.last_position]
      omega
    · rw [sources]
      rfl
  apply LineGlyph.of_slots w hw atoms above dx dy fit_x fit_y initial target labels sources targets
  · intro l
    have hn := A.name_eq_of_component_eq (component_eq l (cutFirstLabel w atoms))
    exact hn.trans hfirst
  · exact walls
  · exact floor

end PushPuzzle.PushS.FiniteRouting.Line.Readout
