/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.EndWalls

/-! Exact two-pixel exterior wall sets of all real output caps. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def capGuardPoints : Direction→Finset (ℕ×ℕ)
  | .west => {(0,99035),(0,99036)}
  | .east => {(200006,99035),(200006,99036)}
  | .north => {(100001,0),(100002,0)}
  | .south => {(100001,198067),(100002,198067)}

def capWallCoordinates (k : GateAnnulus.Key) : Finset (ℕ×ℕ) :=
  (capPiece k).board.walls.image fun q=>((capOffset k).1+q.1.val,(capOffset k).2+q.2.val)

private theorem cap_walls_coordinates : ∀k : GateAnnulus.Key,
    capWallCoordinates k=capGuardPoints (PortAnnulus.outerDirection k.2) := by decide +kernel

private theorem mem_capGuardPoints (d : Direction) (p : ℕ×ℕ) :
    p∈capGuardPoints d ↔CapPoint d p ∧Guard d p := by
  rcases p with ⟨x,y⟩
  cases d <;> simp only [capGuardPoints,Finset.mem_insert,Finset.mem_singleton,
    Prod.mk.injEq,CapPoint,Guard] <;> tauto

theorem cap_wall_guard (k : GateAnnulus.Key)
    (q : Cell (capPiece k).width (capPiece k).height) (hq : q∈(capPiece k).board.walls) :
    Guard (PortAnnulus.outerDirection k.2) ((capOffset k).1+q.1.val,(capOffset k).2+q.2.val) := by
  have hh : ((capOffset k).1+q.1.val,(capOffset k).2+q.2.val)∈capWallCoordinates k :=
    Finset.mem_image.mpr ⟨q,hq,rfl⟩
  rw [cap_walls_coordinates,mem_capGuardPoints] at hh
  exact hh.2

theorem cap_covers (k : GateAnnulus.Key) (p : ℕ×ℕ)
    (hc : CapPoint (PortAnnulus.outerDirection k.2) p) (hg : Guard (PortAnnulus.outerDirection k.2) p) :
    ∃q : Cell (capPiece k).width (capPiece k).height,
      q∈(capPiece k).board.walls ∧((capOffset k).1+q.1.val,(capOffset k).2+q.2.val)=p := by
  have hh:=(mem_capGuardPoints _ p).mpr ⟨hc,hg⟩
  rw [←cap_walls_coordinates] at hh
  exact Finset.mem_image.mp hh

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
