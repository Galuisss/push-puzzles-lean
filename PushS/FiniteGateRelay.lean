/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateReadout
public import PushFS.Gadgets.Gates.Soundness.Relay.AxisStrip
public import PushFS.Gadgets.Gates.Soundness.Relay.Corners

/-! Successful-path transmission from thick-gate triggers to their actual outer ports. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateReadout

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateCore FiniteGateTracks FiniteCoreRails
open PushFS.Gadgets.Wires.Soundness

variable {I : PushFS.Instance} {Label : Type} [Fintype Label]

/-- The two actual straight OR rails are available for source-label SCC paths. -/
structure OrGlyph (M : SlotMatching I Label) (A : AxisTracks I) (w : ℕ)
    extends ThickGateGlyph M A w false where
  railFloor : ∀ r : OrRail, ∀ i,
    (GridEmbedding.translate dx dy fit_x fit_y).cells (r.cell w i) ∉ I.board.walls

def key {W H : ℕ} (axis : Bool) (p : Cell W H) : ℕ := if axis then p.1.val else p.2.val

private theorem forward_chain {n : ℕ} (f : Fin (n+1) → ℕ)
    (hgap : ∀ i : Fin n, f i.castSucc+2 ≤ f i.succ) (i : Fin (n+1)) :
    f 0+2*i.val ≤ f i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih => have hg := hgap i; simp only [Fin.val_succ, Fin.val_castSucc] at *; omega

private theorem backward_chain {n : ℕ} (f : Fin (n+1) → ℕ)
    (hgap : ∀ i : Fin n, f i.succ+2 ≤ f i.castSucc) (i : Fin (n+1)) :
    f i+2*i.val ≤ f 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih => have hg := hgap i; simp only [Fin.val_succ, Fin.val_castSucc] at *; omega

attribute [local irreducible] side

namespace ThickGateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ} {kind : Bool}
    (g : ThickGateGlyph M A w kind)

def offset (axis : Bool) : ℕ := if axis then g.dx else g.dy

private theorem source_coord (axis : Bool) (l : GateLabel w kind) :
    key axis (M.source (g.labels l)) = g.offset axis+key axis (gateCell w kind g.initialSignals l) := by
  rw [g.sources]
  cases axis <;> rfl

private theorem track_literal (axis : Bool) (line : ℕ) (l : GateLabel w kind)
    (hl : gateTrack w kind l = lineTag axis line) :
    A.name (M.source (g.labels l)) = lineTag axis (g.offset (!axis)+line) := by
  rw [g.tracks, hl]
  cases axis <;> rfl

end ThickGateGlyph

namespace AndGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}
    (g : AndGlyph M A w) {S final : LabelledState Label I.width I.height}

def mainX : ℕ := g.dx+(origin w-6*w-9)
def mainY : ℕ := g.dy+origin w
def upperY : ℕ := g.dy+(origin w-6*w-21)
def flipY : ℕ := g.dy+(origin w-3*w-9)

/-- Any cell in one of the seven actual placed rectangles is an ambient wall. -/
theorem wall_rectangle (i : Fin 7) (p : Cell I.width I.height)
    (hx : g.dx+(andRectangle w i).x ≤ p.1.val)
    (hx' : p.1.val < g.dx+(andRectangle w i).x+(andRectangle w i).width)
    (hy : g.dy+(andRectangle w i).y ≤ p.2.val)
    (hy' : p.2.val < g.dy+(andRectangle w i).y+(andRectangle w i).height) : p ∈ I.board.walls := by
  have hb := andRectangle_interior w i
  obtain ⟨q, he⟩ := (GridEmbedding.translate_image_iff g.dx g.dy g.fit_x g.fit_y p).mpr
    ⟨by omega, by omega, by omega, by omega⟩
  have hqx := congrArg (fun r : Cell I.width I.height => r.1.val) he
  have hqy := congrArg (fun r : Cell I.width I.height => r.2.val) he
  change g.dx+q.1.val = p.1.val at hqx
  change g.dy+q.2.val = p.2.val at hqy
  rw [← he]
  apply g.walls q
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    (Rectangle.mem_cells _ _ _ _).mpr ⟨by omega, by omega, by omega, by omega⟩⟩

private theorem rail_component (l m : AndLabel w) (hr : andRail l = andRail m) :
    component I.board (M.source (g.labels l)) = component I.board (M.source (g.labels m)) := by
  rw [g.sources, g.sources]
  exact component_eq_iff.mpr (andCells_connected w
    g.initialSignals.left g.initialSignals.upper g.initialSignals.right l m hr
    g.toThickGateGlyph.embedding I.board (g.railFloor _))

theorem rail_gap (h : Successful M S final) (cert : Certificate I)
    (axis : Bool) (line : ℕ) (l m : AndLabel w) (hr : andRail l = andRail m)
    (hl : andTrack w l = lineTag axis line) (hm : andTrack w m = lineTag axis line)
    (horder : key axis (andCell w g.initialSignals.left g.initialSignals.upper g.initialSignals.right l) <
      key axis (andCell w g.initialSignals.left g.initialSignals.upper g.initialSignals.right m)) :
    key axis (S.position (g.labels l))+2 ≤ key axis (S.position (g.labels m)) := by
  apply h.gap cert A axis (g.offset (!axis)+line) (g.labels l) (g.labels m)
    (g.track_literal axis line l hl) (g.track_literal axis line m hm) (g.rail_component l m hr)
  change key axis (M.source (g.labels l)) < key axis (M.source (g.labels m))
  rw [g.source_coord, g.source_coord]
  exact Nat.add_lt_add_left horder _

theorem guard_span (h : Successful M S final) (cert : Certificate I) (i : Fin (3*w+5)) :
    (S.position (g.labels (.guard 0))).1.val+2*i.val ≤ (S.position (g.labels (.guard i))).1.val := by
  apply forward_chain (fun j : Fin (3*w+5) => (S.position (g.labels (.guard j))).1.val)
  intro j
  apply g.rail_gap h cert true (origin w) (.guard j.castSucc) (.guard j.succ) rfl rfl rfl
  have ha := Bool.toNat_le g.initialSignals.left
  have hj := j.isLt
  dsimp [key, andCell, andPoint]
  unfold origin
  omega

theorem lower_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+5)) :
    (S.position (g.labels (.lower 0))).2.val+2*i.val ≤ (S.position (g.labels (.lower i))).2.val := by
  apply forward_chain (fun j : Fin (w+5) => (S.position (g.labels (.lower j))).2.val)
  intro j
  apply g.rail_gap h cert false (origin w-6*w-9) (.lower j.castSucc) (.lower j.succ) rfl rfl rfl
  have ha := Bool.toNat_le g.initialSignals.left
  have hj := j.isLt
  dsimp [key, andCell, andPoint]
  unfold origin
  omega

theorem upper_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+5)) :
    (S.position (g.labels (.upper 0))).2.val+2*i.val ≤ (S.position (g.labels (.upper i))).2.val := by
  apply forward_chain (fun j : Fin (w+5) => (S.position (g.labels (.upper j))).2.val)
  intro j
  apply g.rail_gap h cert false (origin w-6*w-9) (.upper j.castSucc) (.upper j.succ) rfl rfl rfl
  have ha := Bool.toNat_le g.initialSignals.left
  have hj := j.isLt
  dsimp [key, andCell, andPoint]
  unfold origin
  omega

theorem west_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+4)) :
    (S.position (g.labels (.west i))).1.val+2*i.val ≤ (S.position (g.labels (.west 0))).1.val := by
  apply backward_chain (fun j : Fin (w+4) => (S.position (g.labels (.west j))).1.val)
  intro j
  apply g.rail_gap h cert true (origin w-6*w-21) (.west j.succ) (.west j.castSucc) rfl rfl rfl
  have ha := Bool.toNat_le g.initialSignals.left
  have hj := j.isLt
  dsimp [key, andCell, andPoint]
  unfold origin
  omega

theorem branchB_span (h : Successful M S final) (cert : Certificate I) (i : Fin (4*w+16)) :
    (S.position (g.labels (.branchB i))).2.val+2*i.val ≤ (S.position (g.labels (.branchB 0))).2.val := by
  apply backward_chain (fun j : Fin (4*w+16) => (S.position (g.labels (.branchB j))).2.val)
  intro j
  apply g.rail_gap h cert false (origin w+3) (.branchB j.succ) (.branchB j.castSucc) rfl rfl rfl
  have hb := Bool.toNat_le g.initialSignals.upper
  have hj := j.isLt
  dsimp [key, andCell, andPoint]
  unfold origin
  omega

theorem branchC_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+5)) :
    (S.position (g.labels (.branchC 0))).1.val+2*i.val ≤ (S.position (g.labels (.branchC i))).1.val := by
  apply forward_chain (fun j : Fin (w+5) => (S.position (g.labels (.branchC j))).1.val)
  intro j
  apply g.rail_gap h cert true (origin w) (.branchC j.castSucc) (.branchC j.succ) rfl rfl rfl
  have hc := Bool.toNat_le g.initialSignals.right
  have hj := j.isLt
  dsimp [key, andCell, andPoint]
  unfold origin
  omega

end AndGlyph

namespace OrGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}
    (g : OrGlyph M A w) {S final : LabelledState Label I.width I.height}

private theorem rail_component (l m : OrLabel w) (hr : orRail l = orRail m) :
    component I.board (M.source (g.labels l)) = component I.board (M.source (g.labels m)) := by
  rw [g.sources, g.sources]
  exact component_eq_iff.mpr (orCells_connected w
    g.initialSignals.left g.initialSignals.upper g.initialSignals.right l m hr
    g.toThickGateGlyph.embedding I.board (g.railFloor _))

theorem rail_gap (h : Successful M S final) (cert : Certificate I)
    (axis : Bool) (line : ℕ) (l m : OrLabel w) (hr : orRail l = orRail m)
    (hl : orTrack w l = lineTag axis line) (hm : orTrack w m = lineTag axis line)
    (horder : key axis (orCell w g.initialSignals.left g.initialSignals.upper g.initialSignals.right l) <
      key axis (orCell w g.initialSignals.left g.initialSignals.upper g.initialSignals.right m)) :
    key axis (S.position (g.labels l))+2 ≤ key axis (S.position (g.labels m)) := by
  apply h.gap cert A axis (g.offset (!axis)+line) (g.labels l) (g.labels m)
    (g.track_literal axis line l hl) (g.track_literal axis line m hm) (g.rail_component l m hr)
  change key axis (M.source (g.labels l)) < key axis (M.source (g.labels m))
  rw [g.source_coord, g.source_coord]
  exact Nat.add_lt_add_left horder _

theorem left_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+5)) :
    (S.position (g.labels (.left i))).1.val+2*i.val ≤ (S.position (g.labels (.left 0))).1.val := by
  apply backward_chain (fun j : Fin (w+5) => (S.position (g.labels (.left j))).1.val)
  intro j
  apply g.rail_gap h cert true (origin w) (.left j.succ) (.left j.castSucc) rfl rfl rfl
  have ha := Bool.toNat_le g.initialSignals.left
  have hj := j.isLt
  dsimp [key, orCell, orPoint]
  unfold origin
  omega

theorem branchB_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+7)) :
    (S.position (g.labels (.branchB i))).2.val+2*i.val ≤ (S.position (g.labels (.branchB 0))).2.val := by
  apply backward_chain (fun j : Fin (w+7) => (S.position (g.labels (.branchB j))).2.val)
  intro j
  apply g.rail_gap h cert false (origin w+4) (.branchB j.succ) (.branchB j.castSucc) rfl rfl rfl
  have hb := Bool.toNat_le g.initialSignals.upper
  have hj := j.isLt
  dsimp [key, orCell, orPoint]
  unfold origin
  omega

theorem branchC_span (h : Successful M S final) (cert : Certificate I) (i : Fin (w+5)) :
    (S.position (g.labels (.branchC 0))).1.val+2*i.val ≤ (S.position (g.labels (.branchC i))).1.val := by
  apply forward_chain (fun j : Fin (w+5) => (S.position (g.labels (.branchC j))).1.val)
  intro j
  apply g.rail_gap h cert true (origin w) (.branchC j.castSucc) (.branchC j.succ) rfl rfl rfl
  have hc := Bool.toNat_le g.initialSignals.right
  have hj := j.isLt
  dsimp [key, orCell, orPoint]
  unfold origin
  omega

end OrGlyph
end PushPuzzle.PushS.FiniteGateReadout
