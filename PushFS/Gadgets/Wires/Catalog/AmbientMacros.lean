/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.InThinFrame
public import PushFS.Gadgets.Wires.Catalog.OutThinFrame
public import PushFS.Gadgets.Wires.Catalog.OutMovement
public import PushFS.Gadgets.Wires.Catalog.InMovement
public import PushFS.Gadgets.Wires.Catalog.PlacedSemantics

/-! One actual thin-frame interface for all seven rotated and padded ordinary-cell macros. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Reduction
set_option maxRecDepth 65536

def native (k : Kind) (a b : Bool) : Instance :=
  match k with
  | .east | .west=>Chain.puzzle 200000 (by decide) a b
  | .south=>Chain.puzzle 198061 (by decide) a b
  | .westSouth=>(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle
  | .eastSouth=>(Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).puzzle
  | .southEast=>(In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).puzzle
  | .southWest=>(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle

def nativeIsometry (k : Kind) (a b : Bool) :
    GridIsometry (native k a b).width (native k a b).height (base k a b).width (base k a b).height :=
  match k with
  | .east=>GridIsometry.refl _ _
  | .west=>GridIsometry.reflectX _ _
  | .south=>(GridIsometry.transpose _ _).trans (GridIsometry.reflectX _ _)
  | .westSouth=>GridIsometry.refl _ _
  | .eastSouth=>GridIsometry.reflectX _ _
  | .southEast=>(GridIsometry.reflectX _ _).trans (GridIsometry.transpose _ _)
  | .southWest=>((GridIsometry.reflectX _ _).trans (GridIsometry.transpose _ _)).trans (GridIsometry.reflectX _ _)

private theorem state_refl {w h : ℕ} (s : State w h) : (GridIsometry.refl w h).state s=s := by
  apply State.ext
  · rfl
  · exact Finset.map_refl

private theorem board_refl {w h : ℕ} (B : Board w h) : (GridIsometry.refl w h).board B=B := by
  apply Board.ext <;> exact Finset.map_refl

private theorem native_initial (k : Kind) (a b : Bool) :
    (nativeIsometry k a b).state (native k a b).initial=(base k a b).initial := by
  cases k
  · exact state_refl _
  · rfl
  · exact (GridIsometry.state_trans (GridIsometry.transpose 198066 21) (GridIsometry.reflectX 21 198066) _).symm
  · exact state_refl _
  · rfl
  · exact (GridIsometry.state_trans (GridIsometry.reflectX 99044 100013) (GridIsometry.transpose 99044 100013) _).symm
  · let s : State 99044 100013 := (native .southWest a b).initial
    exact (GridIsometry.state_trans ((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013))
      (GridIsometry.reflectX 100013 99044) s).symm.trans
      (congrArg (GridIsometry.reflectX 100013 99044).state
        (GridIsometry.state_trans (GridIsometry.reflectX 99044 100013) (GridIsometry.transpose 99044 100013) s).symm)

theorem native_board (k : Kind) (a b : Bool) :
    (nativeIsometry k a b).board (native k a b).board=(base k a b).board := by
  cases k
  · exact board_refl _
  · rfl
  · exact (GridIsometry.board_trans (GridIsometry.transpose 198066 21) (GridIsometry.reflectX 21 198066) _).symm
  · exact board_refl _
  · rfl
  · exact (GridIsometry.board_trans (GridIsometry.reflectX 99044 100013) (GridIsometry.transpose 99044 100013) _).symm
  · let B : Board 99044 100013 := (native .southWest a b).board
    exact (GridIsometry.board_trans ((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013))
      (GridIsometry.reflectX 100013 99044) B).symm.trans
      (congrArg (GridIsometry.reflectX 100013 99044).board
        (GridIsometry.board_trans (GridIsometry.reflectX 99044 100013) (GridIsometry.transpose 99044 100013) B).symm)

private theorem native_goals (k : Kind) (a b : Bool) :
    (native k a b).board.goals.map (nativeIsometry k a b).cells.toEmbedding=(base k a b).board.goals :=
  congrArg Board.goals (native_board k a b)

variable {W H : ℕ}

/-- The true unrotated thin primitive chart placed through its actual catalog padding. -/
def nativeEmbedding (k : Kind) (a b : Bool) (e : GridEmbedding width height W H) :
    GridEmbedding (native k a b).width (native k a b).height W H :=
  (nativeIsometry k a b).embedding.trans
    (GridEmbedding.translate (dx k) (dy k) (fitsX k a b) (fitsY k a b)) |>.trans e

structure ChainFrame (n : ℕ) (hn : 2301≤n) (e : GridEmbedding (n+5) 21 W H) (B : Board W H)
    (outside : Finset (PushFS.Cell W H)) : Prop where
  walls : e.WallsAgree (Chain.board n hn ∅) B
  outside_floor : Disjoint outside B.walls
  collar : Polyline.Frame.fixed e outside ⊆ Chain.neighbors n

/-- Every requirement refers to the actual thin lines, protected corner and physical collar boxes. -/
def AmbientFrame (k : Kind) (a b : Bool) (e : GridEmbedding width height W H) (B : Board W H)
    (outside : Finset (PushFS.Cell W H)) : Prop :=
  match k with
  | .east=>ChainFrame 200000 (by decide) (nativeEmbedding .east a b e) B outside
  | .west=>ChainFrame 200000 (by decide) (nativeEmbedding .west a b e) B outside
  | .south=>ChainFrame 198061 (by decide) (nativeEmbedding .south a b e) B outside
  | .westSouth=>Polyline.L.ThinFrame 99970 98999 (by decide) (by decide) (nativeEmbedding .westSouth a b e) B outside
  | .eastSouth=>Out.ThinFrame 99970 98979 (by decide) (by decide) (nativeEmbedding .eastSouth a b e) B outside
  | .southEast=>In.ThinFrame 98981 99969 (by decide) (by decide) (nativeEmbedding .southEast a b e) B outside
  | .southWest=>Polyline.L.ThinFrame 99001 99969 (by decide) (by decide) (nativeEmbedding .southWest a b e) B outside

private theorem chain_frame_transition {n : ℕ} {hn : 2301≤n} {e : GridEmbedding (n+5) 21 W H}
    {B : Board W H} {outside : Finset (PushFS.Cell W H)} (f : ChainFrame n hn e B outside) (a b : Bool) :
    Reachable B (some 1) (e.extend outside (Chain.puzzle n hn a b).initial)
      (e.extend outside ⟨(Chain.puzzle n hn a b).initial.player,(Chain.puzzle n hn a b).board.goals⟩) :=
  Chain.transition_placed n hn a b (Polyline.Frame.fixed e outside) f.collar e f.walls
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor

private theorem native_frame_transition (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    {B : Board W H} {outside : Finset (PushFS.Cell W H)} (f : AmbientFrame k a b e B outside) :
    Reachable B (some 1) ((nativeEmbedding k a b e).extend outside (native k a b).initial)
      ((nativeEmbedding k a b e).extend outside ⟨(native k a b).initial.player,(native k a b).board.goals⟩) := by
  cases k
  · exact chain_frame_transition f a b
  · exact chain_frame_transition f a b
  · exact chain_frame_transition f a b
  · change Reachable B (some 1) ((nativeEmbedding .westSouth a b e).extend outside
      (Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).initial)
      ((nativeEmbedding .westSouth a b e).extend outside
      ⟨Polyline.L.player 99970 98999,(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board.goals⟩)
    rw [Polyline.L.initial_state,Polyline.L.goals_eq]
    exact f.transition a b
  · change Reachable B (some 1) ((nativeEmbedding .eastSouth a b e).extend outside
      (Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).initial)
      ((nativeEmbedding .eastSouth a b e).extend outside
      ⟨Out.player 99970 98979,(Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).board.goals⟩)
    rw [Out.initial_state,Out.goals_eq]
    exact f.transition a b
  · change Reachable B (some 1) ((nativeEmbedding .southEast a b e).extend outside
      (In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).initial)
      ((nativeEmbedding .southEast a b e).extend outside
      ⟨In.player 98981 99969,(In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).board.goals⟩)
    rw [In.initial_state,In.goals_eq]
    exact f.transition a b
  · change Reachable B (some 1) ((nativeEmbedding .southWest a b e).extend outside
      (Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).initial)
      ((nativeEmbedding .southWest a b e).extend outside
      ⟨Polyline.L.player 99001 99969,(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board.goals⟩)
    rw [Polyline.L.initial_state,Polyline.L.goals_eq]
    exact f.transition a b

private theorem extend_trans_empty {w h u v : ℕ} (e : GridEmbedding w h u v) (f : GridEmbedding u v W H)
    (outside : Finset (PushFS.Cell W H)) (s : State w h) :
    (e.trans f).extend outside s=f.extend outside (e.extend ∅ s) := by
  simpa only [Finset.map_empty,Finset.empty_union] using Polyline.Frame.extend_trans e f outside ∅ s

private theorem isometry_extend {w h u v : ℕ} (e : GridIsometry w h u v) (s : State w h) :
    e.embedding.extend ∅ s=e.state s := by
  apply State.ext
  · rfl
  · exact Finset.union_empty _

theorem native_place_initial (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    (outside : Finset (PushFS.Cell W H)) :
    (nativeEmbedding k a b e).extend outside (native k a b).initial=
      e.extend outside (puzzle k a b).initial := by
  dsimp only [nativeEmbedding]
  rw [extend_trans_empty,extend_trans_empty,isometry_extend,native_initial]
  have hh : ((atlas k a b).embedding 0).extend ∅ (base k a b).initial=(puzzle k a b).initial :=
    (placed_initial (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)).symm
  exact congrArg (e.extend outside) hh

private theorem native_place_target (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    (outside : Finset (PushFS.Cell W H)) :
    (nativeEmbedding k a b e).extend outside ⟨(native k a b).initial.player,(native k a b).board.goals⟩=
      e.extend outside ⟨(puzzle k a b).initial.player,(puzzle k a b).board.goals⟩ := by
  dsimp only [nativeEmbedding]
  rw [extend_trans_empty,extend_trans_empty,isometry_extend]
  have hn : (nativeIsometry k a b).state ⟨(native k a b).initial.player,(native k a b).board.goals⟩=
      ⟨(base k a b).initial.player,(base k a b).board.goals⟩ := by
    apply State.ext
    · have hp:=congrArg (fun s : State (base k a b).width (base k a b).height=>s.player) (native_initial k a b)
      exact hp
    · exact native_goals k a b
  rw [hn]
  congr 1
  apply State.ext
  · rfl
  · change (base k a b).board.goals.map ((atlas k a b).embedding 0).cells∪∅=(puzzle k a b).board.goals
    rw [Finset.union_empty]
    exact (placed_goals (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)).symm

/-- All seven actual catalog macros transport to the ambient board with their complete foreign inventory. -/
theorem ambient_transition (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    {B : Board W H} {outside : Finset (PushFS.Cell W H)} (f : AmbientFrame k a b e B outside) :
    Reachable B (some 1) (e.extend outside (puzzle k a b).initial)
      (e.extend outside ⟨(puzzle k a b).initial.player,(puzzle k a b).board.goals⟩) := by
  have hh:=native_frame_transition k a b e f
  rw [native_place_initial,native_place_target] at hh
  exact hh

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
