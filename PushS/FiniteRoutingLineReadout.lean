/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Gadgets.Wires.Soundness.ComponentTracks
public import PushS.FiniteRoutingLineContract
public import PushS.FiniteToolSoundness
public import PushFS.Gadgets.Wires.Soundness.Pair

/-! Actual physical labels, rail gaps and thick tool strips on arbitrary successful route trajectories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Readout

open PushFS PushFS.Gadgets.Wires.Soundness
open FiniteTools (radius)

/-- A finite row with one support cell beyond each extreme normal slot. -/
def rail (w : ℕ) (atoms : List Atom) (i : Fin (span w atoms+4)) : Cell (width w atoms) (height w) :=
  (⟨radius w-1+i.val, by have := i.isLt; unfold width radius; omega⟩, workY w)

def railIndex (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (l : Label w atoms) :
    Fin (span w atoms+4) :=
  ⟨position w atoms q l+1, by
    have hp := positions_bounds w hw q atoms (position_mem w atoms q l)
    have hq := Bool.toNat_le q
    omega⟩

theorem rail_slot (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (l : Label w atoms) :
    rail w atoms (railIndex w hw atoms q l) = cell w hw atoms q l := by
  apply Prod.ext <;> apply Fin.ext
  · dsimp [rail, railIndex, cell]; unfold radius; omega
  · rfl

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]

/-- Static whole-board data for a concrete complete straight program. -/
structure LineGlyph (M : SlotMatching I GlobalLabel) (A : ComponentTracks I) (w : ℕ) (atoms : List Atom) (above : Bool) where
  hw : 2 ≤ w
  dx : ℕ
  dy : ℕ
  fit_x : dx+width w atoms ≤ I.width
  fit_y : dy+height w ≤ I.height
  initialPhase : Bool
  targetPhase : Bool
  labels : Label w atoms ↪ GlobalLabel
  sources : ∀ l, M.source (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (cell w hw atoms initialPhase l)
  targets : ∀ l, M.target (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (cell w hw atoms targetPhase l)
  tracks : ∀ l, A.name (M.source (labels l)) = .horizontal (dy+radius w)
  walls : ∀ p ∈ Line.walls w atoms above, (GridEmbedding.translate dx dy fit_x fit_y).cells p ∈ I.board.walls
  railFloor : ∀ i, (GridEmbedding.translate dx dy fit_x fit_y).cells (rail w atoms i) ∉ I.board.walls

attribute [local irreducible] width height

namespace LineGlyph

variable {M : SlotMatching I GlobalLabel} {A : ComponentTracks I} {w : ℕ} {atoms : List Atom} {above : Bool}
    (g : LineGlyph M A w atoms above) {S final : LabelledState GlobalLabel I.width I.height}

def embedding : GridEmbedding (width w atoms) (height w) I.width I.height :=
  GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y

theorem source_order (i j : Label w atoms) (hij : i.val < j.val) :
    (M.source (g.labels i)).1.val < (M.source (g.labels j)).1.val := by
  rw [g.sources, g.sources]
  have hg := position_gap w g.hw atoms g.initialPhase i j hij
  change g.dx+(radius w+position w atoms g.initialPhase i) < g.dx+(radius w+position w atoms g.initialPhase j)
  omega

private theorem source_component (i j : Label w atoms) :
    SameComponent I.board (M.source (g.labels i)) (M.source (g.labels j)) := by
  have hh := sameComponent_line (n := span w atoms+1) (d := .east) (B := I.board)
    (fun k => g.embedding.cells (rail w atoms k)) g.railFloor
    (by intro k; apply g.embedding.adjacent .east; dsimp [Adjacent, rail]; exact ⟨by omega,rfl⟩)
    (railIndex w g.hw atoms g.initialPhase i) (railIndex w g.hw atoms g.initialPhase j)
    (by
      have hh := positions_bounds w g.hw g.initialPhase atoms (position_mem w atoms g.initialPhase i)
      have hq := Bool.toNat_le g.initialPhase
      dsimp [railIndex]; omega)
    (by
      have hh := positions_bounds w g.hw g.initialPhase atoms (position_mem w atoms g.initialPhase j)
      have hq := Bool.toNat_le g.initialPhase
      dsimp [railIndex]; omega)
  rw [g.sources, g.sources]
  simpa only [rail_slot, embedding] using hh

private theorem gap (h : Successful M S final) (cert : Certificate I) (i j : Label w atoms)
    (hij : i.val < j.val) :
    (S.position (g.labels i)).1.val+2 ≤ (S.position (g.labels j)).1.val :=
  h.gap_component cert A true (g.dy+radius w) (g.labels i) (g.labels j) (g.tracks i) (g.tracks j)
    (component_eq_iff.mpr (g.source_component i j)) (g.source_order i j hij)

/-- The spacing bound accumulates along every physical identity on the actual rail. -/
theorem gap_span (h : Successful M S final) (cert : Certificate I) (i j : Label w atoms) (hij : i.val ≤ j.val) :
    (S.position (g.labels i)).1.val+2*(j.val-i.val) ≤ (S.position (g.labels j)).1.val := by
  have aux (n : ℕ) (hn : i.val+n < (positions w false atoms).length) :
      (S.position (g.labels i)).1.val+2*n ≤ (S.position (g.labels ⟨i.val+n,hn⟩)).1.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hprev := ih (by omega)
      have hgap := g.gap h cert ⟨i.val+n,by omega⟩ ⟨i.val+(n+1),hn⟩ (by simp)
      omega
  have he := aux (j.val-i.val) (by have := j.isLt; omega)
  have hj : (⟨i.val+(j.val-i.val), by have := j.isLt; omega⟩ : Label w atoms) = j := by
    apply Fin.ext
    change i.val+(j.val-i.val) = j.val
    omega
  rw [hj] at he
  exact he

/-- A local strip is placed by wall inclusion alone. -/
theorem strip_walls {lo hi : ℕ} (_hl : lo ≤ hi) (hhi : hi < width w atoms)
    (hs : StripWalls (⟨Line.walls w atoms above,∅⟩ : Board (width w atoms) (height w)) lo hi (radius w)) :
    StripWalls I.board (g.dx+lo) (g.dx+hi) (g.dy+radius w) := by
  have hy0 : 0 < radius w := by unfold radius; omega
  have hyfit : radius w+1 < height w := by unfold height FiniteTools.side radius; omega
  have wall (p : Cell I.width I.height) (hx : g.dx+lo ≤ p.1.val) (hx' : p.1.val ≤ g.dx+hi)
      (hy : p.2.val = g.dy+radius w+1 ∨ p.2.val+1 = g.dy+radius w) : p ∈ I.board.walls := by
    let q : Cell (width w atoms) (height w) := (⟨p.1.val-g.dx,by omega⟩,⟨p.2.val-g.dy,by omega⟩)
    have hq : g.embedding.cells q = p := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [embedding, GridEmbedding.translate, q] <;> omega
    have hm : q ∈ Line.walls w atoms above := by
      rcases hy with hy | hy
      · exact hs.below q (by dsimp [q]; omega) (by dsimp [q]; omega) (by dsimp [q]; omega)
      · exact hs.above q (by dsimp [q]; omega) (by dsimp [q]; omega) (by dsimp [q]; omega)
    exact hq ▸ g.walls q hm
  exact ⟨fun p hp hx hx' => wall p hx hx' (Or.inl hp), fun p hp hx hx' => wall p hx hx' (Or.inr hp)⟩

/-- Every threshold reads a concrete physical label's actual global coordinate. -/
def High (S : LabelledState GlobalLabel I.width I.height) (l : Label w atoms) : Prop :=
  g.dx+radius w+position w atoms true l ≤ (S.position (g.labels l)).1.val

end LineGlyph
end PushPuzzle.PushS.FiniteRouting.Line.Readout
