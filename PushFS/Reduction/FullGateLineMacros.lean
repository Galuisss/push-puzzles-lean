/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateFrontierWalking
public import PushFS.Reduction.FullGateSeamGeometry
public import PushFS.Reduction.FullGateLineWalking
public import PushFS.Reduction.FullGateCornerWalking
public import PushFS.Reduction.FullGateLineSlots
public import PushFS.Reduction.FullGateUpdates

/-! Complete actual long-line propagation preserves every other primitive and returns the one actual player. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def lineNeighbors (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Finset (Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height) :=
  match flip with
  | false=>Chain.neighbors n
  | true=>FlippedChain.neighbors n

private theorem chainNeighbors_iff (n : ℕ) (p : Chain.C n) :
    p∈Chain.neighbors n ↔p.2.val=10 ∧(p.1.val=0 ∨p.1.val=n+3) := by
  rcases p with ⟨x,y⟩
  simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega

private theorem flippedNeighbors_iff (n : ℕ) (p : FlippedChain.C n) :
    p∈FlippedChain.neighbors n ↔p.2.val=10 ∧(p.1.val=0 ∨p.1.val=n+23) := by
  rcases p with ⟨x,y⟩
  simp only [FlippedChain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega

theorem lineNeighbors_iff (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height) :
    p∈lineNeighbors flip n hn a b ↔p.2.val=10 ∧(p.1.val=0 ∨p.1.val=n+(if flip then 20 else 0)+3) := by
  cases flip
  · exact chainNeighbors_iff n p
  · exact flippedNeighbors_iff n p

theorem raw_line_transition (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    {W H : ℕ} (e : GridEmbedding (lineBase flip n hn a b).width (lineBase flip n hn a b).height W H)
    {B : Board W H} {outside : Finset (Cell W H)}
    (hw : e.WallsAgree (lineBase flip n hn a b).board B) (hf : Disjoint outside B.walls)
    (hc : Polyline.Frame.fixed e outside⊆lineNeighbors flip n hn a b) :
    Reachable B (some 1) (e.extend outside ⟨lineBaseHub flip n hn a b,(lineBase flip n hn a b).initial.boxes⟩)
      (e.extend outside ⟨lineBaseHub flip n hn a b,(lineBase flip n hn a b).board.goals⟩) := by
  cases flip
  · exact Chain.transition_placed n hn a b (Polyline.Frame.fixed e outside) hc e hw
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf
  · have hw' : e.WallsAgree (FlippedChain.board n hn ∅) B := by
      intro p
      have hm:=hw p
      change e.cells p∈B.walls ↔p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls at hm
      rw [FlippedChain.atlas_walls] at hm
      exact hm
    change Reachable B (some 1)
      (e.extend outside ⟨FlippedChain.player n,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).initial.boxes⟩)
      (e.extend outside ⟨FlippedChain.player n,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals⟩)
    rw [FlippedChain.initial_boxes,FlippedChain.goals_eq]
    exact FlippedChain.transition_placed n hn a b (Polyline.Frame.fixed e outside) hc e hw'
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf

attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profile profileOutside selectedMarks cornerKind cornerOrientation

structure LinePrepared (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) : Prop where
  buffer : j.val=0 →armPhase g f r (.inl (frontierBufferIndex r))=false
  previous : ∀k : Fin ((curve (key g r)).length-1),j.val=k.val+1 →armPhase g f r (cornerIndex g r k)=false
  next : ∀k : Fin ((curve (key g r)).length-1),j.val=k.val →armPhase g f r (cornerIndex g r k)=true

theorem line_macro_collar (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) (prepared : LinePrepared g f r j) :
    Polyline.Frame.fixed (lineEmbedding g r j) (profileOutside g f (lineIndex g r j))⊆
      lineNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) := by
  intro p hp
  obtain ⟨hy,hs⟩:=line_profile_slots g f r j p ((Polyline.Frame.mem_fixed _ _ p).mp hp)
  apply (lineNeighbors_iff _ _ _ _ _ p).mpr
  refine ⟨hy,?_⟩
  cases hs with
  | buffer hj hx =>
    rw [prepared.buffer hj] at hx
    exact Or.inl hx
  | previous k hj hx =>
    rw [prepared.previous k hj] at hx
    exact Or.inl hx
  | next k hj hx =>
    rw [prepared.next k hj] at hx
    rcases hx with hx|⟨hf,_⟩
    · exact Or.inr hx
    · cases hf

end PushPuzzle.PushFS.Reduction.GateTileRouting
