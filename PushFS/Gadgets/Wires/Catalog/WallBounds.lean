/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RawWallBounds

/-! Global support of the complete padded-cell wall bitmap. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem padding_wall_preimage (k : Kind) (a b : Bool) {p : Cell}
    (hp : p∈(puzzle k a b).board.walls) :
    ∃q, q∈(base k a b).board.walls ∧(padding k a b).cells q=p := by
  change p∈(atlas k a b).walls at hp
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
  change p∈(base k a b).board.walls.map (padding k a b).cells at hi
  obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hi
  exact ⟨q,hq,he⟩

def HorizontalBand (p : Cell) : Prop := 99031≤p.2.val ∧p.2.val≤99035
def VerticalBand (p : Cell) : Prop := 100000≤p.1.val ∧p.1.val≤100004

/-- Exact conservative supports, retaining the real used half-arms. -/
def WallRegion (k : Kind) (p : Cell) : Prop :=
  match k with
  | .east | .west=>HorizontalBand p
  | .south=>VerticalBand p
  | .westSouth=>(100000≤p.1.val ∧HorizontalBand p) ∨ (VerticalBand p ∧99031≤p.2.val)
  | .eastSouth=>(p.1.val≤100004 ∧HorizontalBand p) ∨ (VerticalBand p ∧99031≤p.2.val)
  | .southEast=>(100000≤p.1.val ∧HorizontalBand p) ∨ (VerticalBand p ∧p.2.val≤99035)
  | .southWest=>(p.1.val≤100004 ∧HorizontalBand p) ∨ (VerticalBand p ∧p.2.val≤99035)

/-- Every actual wall, including every helper stencil and padding cell, lies on the asserted physical arm support. -/
theorem wall_bounds (k : Kind) (a b : Bool) {p : Cell} (hp : p∈(puzzle k a b).board.walls) : WallRegion k p := by
  obtain ⟨q,hq,rfl⟩:=padding_wall_preimage k a b hp
  cases k
  · let r:=q
    have hb:=Chain.walls_rows 200000 (by decide) r hq
    change 99031≤99023+(r.2.val) ∧99023+(r.2.val)≤99035
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega
  · obtain ⟨r,he⟩:=(GridIsometry.reflectX 200005 21).cells.surjective q
    have heq : q=(GridIsometry.reflectX 200005 21).cells (r) := he.symm
    subst q
    change (GridIsometry.reflectX 200005 21).cells (r)∈((GridIsometry.reflectX 200005 21).board ((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b))))).walls at hq
    repeat rw [GridIsometry.mem_walls] at hq
    have hb:=Chain.walls_rows 200000 (by decide) r hq
    change 99031≤99023+(r.2.val) ∧99023+(r.2.val)≤99035
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega
  · obtain ⟨r,he⟩:=((GridIsometry.transpose 198066 21).trans (GridIsometry.reflectX 21 198066)).cells.surjective q
    have heq : q=(GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (r)) := he.symm
    subst q
    change (GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (r))∈((GridIsometry.reflectX 21 198066).board ((GridIsometry.transpose 198066 21).board ((Chain.board 198061 (by decide) (Chain.boxes 198061 (by decide) (Chain.uniform 198061 b)))))).walls at hq
    repeat rw [GridIsometry.mem_walls] at hq
    have hb:=Chain.walls_rows 198061 (by decide) r hq
    change 100000≤99992+(21-(r.2.val+1)) ∧99992+(21-(r.2.val+1))≤100004
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega
  · let r:=q
    change r∈(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).walls at hq
    rw [Polyline.L.atlas_walls] at hq
    have hb:=normal_wall_bounds 99970 98999 (by decide) (by decide) hq
    unfold RawWallRegion at hb
    change (100000≤99992+(r.1.val) ∧(99031≤99023+(r.2.val) ∧99023+(r.2.val)≤99035)) ∨ ((100000≤99992+(r.1.val) ∧99992+(r.1.val)≤100004) ∧99031≤99023+(r.2.val))
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega
  · obtain ⟨r,he⟩:=(GridIsometry.reflectX 100013 99043).cells.surjective q
    have heq : q=(GridIsometry.reflectX 100013 99043).cells (r) := he.symm
    subst q
    change (GridIsometry.reflectX 100013 99043).cells (r)∈((GridIsometry.reflectX 100013 99043).board ((Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).board)).walls at hq
    repeat rw [GridIsometry.mem_walls] at hq
    change r∈(Out.atlas 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)).walls at hq
    rw [Out.atlas_walls] at hq
    have hb:=out_wall_bounds 99970 98979 (by decide) (by decide) hq
    unfold RawWallRegion at hb
    change (0+(100013-(r.1.val+1))≤100004 ∧(99031≤99023+(r.2.val) ∧99023+(r.2.val)≤99035)) ∨ ((100000≤0+(100013-(r.1.val+1)) ∧0+(100013-(r.1.val+1))≤100004) ∧99031≤99023+(r.2.val))
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega
  · obtain ⟨r,he⟩:=((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013)).cells.surjective q
    have heq : q=(GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (r)) := he.symm
    subst q
    change (GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (r))∈((GridIsometry.transpose 99044 100013).board ((GridIsometry.reflectX 99044 100013).board ((In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).board))).walls at hq
    repeat rw [GridIsometry.mem_walls] at hq
    change r∈(In.atlas 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)).walls at hq
    rw [In.atlas_walls] at hq
    have hb:=in_wall_bounds 98981 99969 (by decide) (by decide) hq
    unfold RawWallRegion at hb
    change (100000≤99992+(r.2.val) ∧(99031≤0+(99044-(r.1.val+1)) ∧0+(99044-(r.1.val+1))≤99035)) ∨ ((100000≤99992+(r.2.val) ∧99992+(r.2.val)≤100004) ∧0+(99044-(r.1.val+1))≤99035)
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega
  · obtain ⟨r,he⟩:=(((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013)).trans (GridIsometry.reflectX 100013 99044)).cells.surjective q
    have heq : q=(GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (r))) := he.symm
    subst q
    change (GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (r)))∈((GridIsometry.reflectX 100013 99044).board ((GridIsometry.transpose 99044 100013).board ((GridIsometry.reflectX 99044 100013).board ((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board)))).walls at hq
    repeat rw [GridIsometry.mem_walls] at hq
    change r∈(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).walls at hq
    rw [Polyline.L.atlas_walls] at hq
    have hb:=normal_wall_bounds 99001 99969 (by decide) (by decide) hq
    unfold RawWallRegion at hb
    change (0+(100013-(r.2.val+1))≤100004 ∧(99031≤0+(99044-(r.1.val+1)) ∧0+(99044-(r.1.val+1))≤99035)) ∨ ((100000≤0+(100013-(r.2.val+1)) ∧0+(100013-(r.2.val+1))≤100004) ∧0+(99044-(r.1.val+1))≤99035)
    have hx:=r.1.isLt
    have hy:=r.2.isLt
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
