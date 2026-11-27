/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.StorageImage
public import PushFS.Gadgets.Wires.Catalog.RailFlipped
public import PushFS.Gadgets.Wires.Catalog.RailTurn

/-! Every actual atlas piece yields an exact ambient storage chart and its C1–C3 endpoint lemma. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

variable {n W H : ℕ} {Family : Fin n→Type} [∀i,Fintype (Family i)]

/-- All physical identities and true walls of one owned piece are preserved inside the real atlas. -/
def pieceImage (a : Reduction.StorageAtlas n W H Family) (i : Fin n) :
    StorageImage a.slotMatching (a.matching i) where
  dx:=a.dx i
  dy:=a.dy i
  fit_x:=a.fitsX i
  fit_y:=a.fitsY i
  labels:=⟨fun l=>⟨i,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
  walls:=a.walls_agree i
  sources _:=rfl
  targets _:=rfl

namespace StorageImage

open Soundness
variable {I J : Instance} {L A : Type} [Fintype L] [Fintype A]
    {M : SlotMatching I L} {N : SlotMatching J A}

theorem source_component (g : StorageImage M N) (i j : A)
    (hc : SameComponent J.board (N.source i) (N.source j)) :
    component I.board (M.source (g.labels i))=component I.board (M.source (g.labels j)) := by
  rw [g.sources,g.sources]
  exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hc.1,GridEmbedding.staticReach g.walls hc.2⟩

variable {n : ℕ} {hn : 2301≤n} {a b : Bool}

def chainGlyph (g : StorageImage M (Chain.slotMatching n hn a b)) : ChainRailGlyph M n hn where
  dx:=g.dx
  dy:=g.dy
  fit_x:=g.fit_x
  fit_y:=g.fit_y
  initialPhase:=a
  targetPhase:=b
  labels:=g.labels
  walls:=g.walls
  sources:=g.sources
  targets:=g.targets

def flippedGlyph (g : StorageImage M (FlippedChain.slotMatching n hn a b)) : FlippedRailGlyph M n hn where
  dx:=g.dx
  dy:=g.dy
  fit_x:=g.fit_x
  fit_y:=g.fit_y
  initialPhase:=a
  targetPhase:=b
  labels:=g.labels
  walls p:=by
    have hh:=g.walls p
    change _↔p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls at hh
    rw [FlippedChain.atlas_walls] at hh
    exact hh
  sources l:=by
    rw [g.sources,FlippedChain.source_position]
    rfl
  targets l:=by
    rw [g.targets,FlippedChain.target_position]
    rfl

def turnGlyph (g : StorageImage M (Turn.checked.slotMatching a b)) : TurnRailGlyph M where
  dx:=g.dx
  dy:=g.dy
  fit_x:=g.fit_x
  fit_y:=g.fit_y
  initialPhase:=a
  targetPhase:=b
  labels:=g.labels
  walls p:=by
    change _↔p∈Turn.template.walls
    exact g.walls p
  sources:=g.sources
  targets:=g.targets

end StorageImage
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
