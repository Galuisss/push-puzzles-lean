/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalNeighbors
public import PushFS.Reduction.FullGateStatics.Components
public import PushFS.Reduction.FullGateStatics.BoundaryNames
public import PushFS.Gadgets.Wires.Catalog.CoordinateNames

/-! The actual complete physical macrocells as translated wall displacement charts. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Gadgets.Wires GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

noncomputable def classifier : (k : Key)→AxisClassifier (piece k).board
  | .inl g=>FullGateStatics.classifier g
  | .inr a=>Polyline.axisClassifier (Catalog.axisTracks a.1 a.2.1 a.2.2)

theorem initial_active (k : Key) (p : Cell (piece k).width (piece k).height)
    (hp : p∈(piece k).initial.boxes) : (classifier k).name p≠.outside := by
  cases k with
  | inl g=>exact FullGateStatics.initial_active g p hp
  | inr a=>exact (Catalog.axisTracks a.1 a.2.1 a.2.2).active p hp

def OnSide (k : Key) : Direction→Cell (piece k).width (piece k).height→Prop
  | .north,p=>p.2.val=0
  | .east,p=>p.1.val+1=(piece k).width
  | .south,p=>p.2.val+1=(piece k).height
  | .west,p=>p.1.val=0

def portName (k : Key) : Direction→AxisTrack
  | .west | .east=>.horizontal (99034-pad k)
  | .north | .south=>.vertical (100003-pad k)

structure BoundaryPort (k : Key) (p : Cell (piece k).width (piece k).height) where
  direction : Direction
  side : OnSide k direction p
  used : Used k direction
  name : (classifier k).name p=portName k direction

private theorem boundary_cases {w h : ℕ} (p : Cell w h) (hp : ¬Interior p) :
    p.1.val=0 ∨p.1.val+1=w ∨p.2.val=0 ∨p.2.val+1=h := by
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  dsimp only [Interior] at hp
  omega

private theorem wire_boundary_port (a : Catalog.Bitmap.Args) (p : Catalog.Cell) (d : Direction)
    (ha : (classifier (.inr a)).name p≠.outside) (hs : OnSide (.inr a) d p)
    (hc : Catalog.InCollar (face d) p) : Nonempty (BoundaryPort (.inr a) p) := by
  have ht:=Catalog.axisTracks_collar a.1 a.2.1 a.2.2 (face d) p hc
  have hu : Catalog.FaceUsed a.1 (face d) := by
    by_contra he
    exact ha (ht.trans (ite_eq_right he))
  rw [ite_eq_left hu] at ht
  have hn : Catalog.collarName (face d) p≠.outside := fun he=>ha (ht.trans he)
  refine ⟨⟨d,hs,hu,ht.trans ?_⟩⟩
  cases d <;> dsimp only [face,Catalog.collarName,portName,pad] at hn ⊢ <;>
    split_ifs <;> simp_all

theorem boundary_port (k : Key) (p : Cell (piece k).width (piece k).height)
    (ha : (classifier k).name p≠.outside) (hp : ¬Interior p) : Nonempty (BoundaryPort k p) := by
  have hb:=boundary_cases p hp
  cases k with
  | inl g=>
    have he : FullGateStatics.OnEdge (p.1.val,p.2.val) := by
      change p.1.val=0 ∨p.1.val+1=200007 ∨p.2.val=0 ∨p.2.val+1=198068 at hb
      dsimp only [FullGateStatics.OnEdge]
      omega
    have ht:=FullGateStatics.classifier_edge_name g p ha he
    by_cases hh : p.2.val=99034 ∧(p.1.val=0 ∧FullGateBoundary.Used g .west ∨
        p.1.val=200006 ∧FullGateBoundary.Used g .east)
    · have hn : (classifier (.inl g)).name p=.horizontal 99034 := by
        exact ht.trans (ite_eq_left hh)
      rcases hh.2 with ⟨hx,hu⟩|⟨hx,hu⟩
      · exact ⟨⟨.west,hx,hu,hn⟩⟩
      · exact ⟨⟨.east,by change p.1.val+1=200007; omega,hu,hn⟩⟩
    · by_cases hv : p.1.val=100003 ∧(p.2.val=0 ∧FullGateBoundary.Used g .north ∨
          p.2.val=198067 ∧FullGateBoundary.Used g .south)
      · have hn : (classifier (.inl g)).name p=.vertical 100003 := by
          exact ht.trans ((ite_eq_right hh).trans (ite_eq_left hv))
        rcases hv.2 with ⟨hy,hu⟩|⟨hy,hu⟩
        · exact ⟨⟨.north,hy,hu,hn⟩⟩
        · exact ⟨⟨.south,by change p.2.val+1=198068; omega,hu,hn⟩⟩
      · exact False.elim (ha (ht.trans ((ite_eq_right hh).trans (ite_eq_right hv))))
  | inr a=>
    change p.1.val=0 ∨p.1.val+1=200005 ∨p.2.val=0 ∨p.2.val+1=198066 at hb
    rcases hb with hw|he|hn|hs
    · exact wire_boundary_port a p .west ha hw (by change p.1.val<7; omega)
    · exact wire_boundary_port a p .east ha he (by change 199998≤p.1.val; omega)
    · exact wire_boundary_port a p .north ha hn (by change p.2.val<7; omega)
    · exact wire_boundary_port a p .south ha hs (by change 198059≤p.2.val; omega)

end PushPuzzle.PushFS.Reduction.PhysicalTiles

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory
open PhysicalBitmap
attribute [local irreducible] Raster.width Raster.height

noncomputable def axisChart (v : CellPlan.Source) (i : Index v) :
    TranslatedAxisChart (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) where
  width:=(PhysicalTiles.piece (tile i)).width
  height:=(PhysicalTiles.piece (tile i)).height
  board:=(PhysicalTiles.piece (tile i)).board
  dx:=(PhysicalTiles.offset (position i) (tile i)).1
  dy:=(PhysicalTiles.offset (position i) (tile i)).2
  fits_x:=(PhysicalTiles.fits v.1 i.val.1 (tile i)).1
  fits_y:=(PhysicalTiles.fits v.1 i.val.1 (tile i)).2
  classifier:=PhysicalTiles.classifier (tile i)

theorem axisChart_walls (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) : (axisChart v i).embedding.WallsAgree (axisChart v i).board (puzzle v hP hT).board :=
  walls_agree v hP hT i

end PushPuzzle.PushFS.Reduction.PhysicalInventory
