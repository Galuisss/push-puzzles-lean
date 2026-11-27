/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RailChain
public import PushFS.Gadgets.Wires.FlippedChain.Order
public import PushFS.Gadgets.Wires.Soundness.Chain

/-! The full terminal-flipped train transmits its signal through true source SCCs and C1–C3 in any reoriented ambient board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness

variable {I : Instance} {L : Type} [Fintype L]

/-- Pure static exact placement of every real owned FlippedChain label and its actual wall bitmap. -/
structure FlippedRailGlyph (M : SlotMatching I L) (n : ℕ) (hn : 2301≤n) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+(n+25)≤I.width
  fit_y : dy+21≤I.height
  initialPhase : Bool
  targetPhase : Bool
  labels : FlippedChain.Label n↪L
  walls : (GridEmbedding.translate dx dy fit_x fit_y).WallsAgree (FlippedChain.board n hn ∅) I.board
  sources : ∀l, M.source (labels l)=(GridEmbedding.translate dx dy fit_x fit_y).cells (FlippedChain.position n hn initialPhase l)
  targets : ∀l, M.target (labels l)=(GridEmbedding.translate dx dy fit_x fit_y).cells (FlippedChain.position n hn targetPhase l)

namespace FlippedRailGlyph

variable {M : SlotMatching I L} {n : ℕ} {hn : 2301≤n} (g : FlippedRailGlyph M n hn)

theorem chain_fit : g.dx+(n+5)≤I.width := by have hh:=g.fit_x; omega
theorem flip_fit : g.dx+n+25≤I.width := by have hh:=g.fit_x; omega

theorem chain_cell (p : Chain.C n) :
    (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells ((FlippedChain.chainPlacement n).cells p)=
      (GridEmbedding.translate g.dx g.dy g.chain_fit g.fit_y).cells p := by
  apply Prod.ext <;> apply Fin.ext
  · change g.dx+(0+p.1.val)=g.dx+p.1.val; omega
  · change g.dy+(0+p.2.val)=g.dy+p.2.val; omega

theorem flip_cell (p : Flip.C) :
    (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells ((FlippedChain.flipPlacement n).cells p)=
      (GridEmbedding.translate (g.dx+n) g.dy g.flip_fit g.fit_y).cells p := by
  apply Prod.ext <;> apply Fin.ext
  · change g.dx+(n+p.1.val)=g.dx+n+p.1.val; omega
  · change g.dy+(0+p.2.val)=g.dy+p.2.val; omega

private def chain : ChainRailGlyph M n hn where
  dx:=g.dx
  dy:=g.dy
  fit_x:=g.chain_fit
  fit_y:=g.fit_y
  initialPhase:=g.initialPhase
  targetPhase:=g.targetPhase
  labels:=(FlippedChain.chainLabels n).trans g.labels
  walls p:=by
    rw [←g.chain_cell p,g.walls]
    exact FlippedChain.chain_walls n hn ∅ p
  sources l:=by
    change M.source (g.labels ⟨0,l⟩)=_
    rw [g.sources,FlippedChain.position0 n hn g.initialPhase l,g.chain_cell]
  targets l:=by
    change M.target (g.labels ⟨0,l⟩)=_
    rw [g.targets,FlippedChain.position0 n hn g.targetPhase l,g.chain_cell]

private def terminal : HorizontalRailGlyph M .flip where
  dx:=g.dx+n
  dy:=g.dy
  fit_x:=g.flip_fit
  fit_y:=g.fit_y
  initialPhase:=g.initialPhase
  targetPhase:=g.targetPhase
  labels:=(FlippedChain.flipLabels n).trans g.labels
  walls p:=by
    rw [←g.flip_cell p,g.walls]
    exact FlippedChain.flip_walls n hn ∅ p
  sources i:=by
    change M.source (g.labels ⟨1,i⟩)=_
    rw [g.sources,FlippedChain.position1 n hn g.initialPhase i,g.flip_cell]
    rfl
  targets i:=by
    change M.target (g.labels ⟨1,i⟩)=_
    rw [g.targets,FlippedChain.position1 n hn g.targetPhase i,g.flip_cell]
    rfl

theorem component (i j : FlippedChain.Label n) : component I.board (M.source (g.labels i))=component I.board (M.source (g.labels j)) := by
  rw [g.sources,g.sources]
  have hc:=FlippedChain.slots_component n hn g.initialPhase i j
  exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hc.1,GridEmbedding.staticReach g.walls hc.2⟩

private def rail : SourceRail M true (g.dy+10) where
  anchor:=g.labels (FlippedChain.firstLabel n hn)
  witness:=M.source (g.labels (FlippedChain.lastLabel n))
  connected:=g.component _ _
  different:=by
    intro he
    rw [g.sources,g.sources] at he
    change g.dx+(FlippedChain.position n hn g.initialPhase (FlippedChain.lastLabel n)).1.val=
      g.dx+(FlippedChain.position n hn g.initialPhase (FlippedChain.firstLabel n hn)).1.val at he
    rw [(FlippedChain.endpoints n hn g.initialPhase).1,(FlippedChain.endpoints n hn g.initialPhase).2] at he
    omega
  anchor_cross:=by
    rw [g.sources]
    change g.dy+(FlippedChain.position n hn g.initialPhase _).2.val=g.dy+10
    rw [FlippedChain.position_row]

/-- The real two-cell gap across the physical train/terminal-flip seam follows from C1–C3. -/
private theorem seam_gap {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I) :
    (S.position (g.labels (FlippedChain.lastChainLabel n hn))).1.val+2≤(S.position (g.labels (FlippedChain.firstFlipLabel n))).1.val := by
  apply g.rail.gap h cert _ _ (g.component _ _) (g.component _ _)
  rw [g.sources,g.sources]
  change g.dx+(FlippedChain.position n hn g.initialPhase ⟨0,Polyline.ChainEnds.last n hn⟩).1.val<
    g.dx+(FlippedChain.position n hn g.initialPhase ⟨1,(0 : Fin 9)⟩).1.val
  rw [FlippedChain.position0 n hn g.initialPhase _,FlippedChain.position1 n hn g.initialPhase _,FlippedChain.chain_x,FlippedChain.flip_x,
    Polyline.ChainEnds.last_x,(Flip.endpoint_slots g.initialPhase).1]
  omega

/-- Every actual intermediate state of a successful path transmits the near threshold to the true far endpoint. -/
theorem signal {S final : LabelledState L I.width I.height} (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dx+3≤(S.position (g.labels (FlippedChain.firstLabel n hn))).1.val) :
    g.dx+n+21≤(S.position (g.labels (FlippedChain.lastLabel n))).1.val := by
  have hc:=g.chain.signal h cert ho hin
  have hg:=g.seam_gap h cert
  have hflip : g.dx+n+3≤(S.position (g.terminal.labels HorizontalKind.flip.first)).1.val := by
    change g.dx+n+1≤(S.position (g.labels (FlippedChain.lastChainLabel n hn))).1.val at hc
    change g.dx+n+3≤(S.position (g.labels (FlippedChain.firstFlipLabel n))).1.val
    omega
  exact g.terminal.signal h cert ho hflip

end FlippedRailGlyph
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
