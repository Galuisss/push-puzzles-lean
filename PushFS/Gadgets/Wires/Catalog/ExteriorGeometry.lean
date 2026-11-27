/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.AmbientMacros
public import PushFS.Gadgets.Wires.Catalog.BoundaryWalls
public import PushFS.Gadgets.Wires.Catalog.SlotBounds

/-! Literal empty quadrant corridors connect actual primitive portals to the full catalog rectangle corners. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def outerCorner (i : Fin 4) : Cell := ![(0,0),(200004,0),(0,198065),(200004,198065)] i

/-- The only possible foreign slots in the overlapping outer collars. -/
def ExternalRail (p : Cell) : Prop :=
  (p.2.val=99033 ∧(p.1.val<5 ∨200000≤p.1.val)) ∨
    (p.1.val=100002 ∧(p.2.val<5 ∨198061≤p.2.val))

def WalkingMask : Kind→Cell→Prop
  | .east,p=>p.2.val=99033 ∧(p.1.val≤1 ∨200002≤p.1.val)
  | .west,p=>p.2.val=99033 ∧(p.1.val≤2 ∨200003≤p.1.val)
  | .south,p=>p.1.val=100002 ∧(p.2.val≤1 ∨198063≤p.2.val)
  | .westSouth,p=>(p.2.val=99033 ∧200003≤p.1.val) ∨(p.1.val=100002 ∧198063≤p.2.val)
  | .eastSouth,p=>(p.2.val=99033 ∧p.1.val≤1) ∨(p.1.val=100002 ∧198063≤p.2.val)
  | .southEast,p=>(p.1.val=100002 ∧p.2.val≤1) ∨(p.2.val=99033 ∧200002≤p.1.val)
  | .southWest,p=>(p.1.val=100002 ∧p.2.val≤1) ∨(p.2.val=99033 ∧p.1.val≤2)

theorem walkingMask_rail (k : Kind) (p : Cell) (hp : WalkingMask k p) : ExternalRail p := by
  cases k <;> dsimp only [WalkingMask,ExternalRail] at * <;> omega

def Quadrant (i : Fin 4) (p : Cell) : Prop :=
  (if i.val%2=0 then p.1.val<100000 else 100004<p.1.val) ∧
    (if i.val<2 then p.2.val<99031 else 99035<p.2.val)

theorem external_rail_floor (k : Kind) (a b : Bool) {p : Cell} (hp : ExternalRail p) :
    p∉(puzzle k a b).board.walls := by
  rcases hp with ⟨hy,hx|hx⟩|⟨hx,hy|hy⟩
  · intro hw
    have hh:=((boundary_walls k a b .west p hx).mp hw).2
    dsimp only [FaceGuard] at hh
    omega
  · intro hw
    have hh:=((boundary_walls k a b .east p hx).mp hw).2
    dsimp only [FaceGuard] at hh
    omega
  · intro hw
    have hh:=((boundary_walls k a b .north p hy).mp hw).2
    dsimp only [FaceGuard] at hh
    omega
  · intro hw
    have hh:=((boundary_walls k a b .south p hy).mp hw).2
    dsimp only [FaceGuard] at hh
    omega

private theorem quadrant_free (k : Kind) (a b : Bool) (fixed : Finset Cell)
    (hm : ∀p∈fixed,ExternalRail p) (i : Fin 4) (p : Cell) (hp : Quadrant i p) :
    Free (puzzle k a b).board ((puzzle k a b).initial.boxes∪fixed) p := by
  have hxy : (p.1.val<100000 ∨100004<p.1.val) ∧(p.2.val<99031 ∨99035<p.2.val) := by
    unfold Quadrant at hp
    split_ifs at hp <;> omega
  constructor
  · intro hw
    have hh:=wall_bounds k a b hw
    cases k <;> dsimp only [WallRegion,HorizontalBand,VerticalBand] at hh <;> omega
  · intro hb
    rcases Finset.mem_union.mp hb with hb|hb
    · rw [←(slotMatching k a b).source_image] at hb
      obtain ⟨l,_,rfl⟩:=Finset.mem_map.mp hb
      have hh:=source_bounds k a b l
      cases k <;> dsimp only [SlotRegion,SlotBounds] at hh <;> omega
    · have hh:=hm p hb
      dsimp only [ExternalRail] at hh
      omega

/-- Every such corridor is a real walk with all owned and foreign boxes fixed. -/
theorem quadrant_walk (k : Kind) (a b : Bool) (fixed : Finset Cell)
    (hm : ∀p∈fixed,ExternalRail p) (i : Fin 4) (p q : Cell)
    (hp : Quadrant i p) (hq : Quadrant i q) :
    Reachable (puzzle k a b).board (some 1) ⟨p,(puzzle k a b).initial.boxes∪fixed⟩
      ⟨q,(puzzle k a b).initial.boxes∪fixed⟩ := by
  have hf : Disjoint ((puzzle k a b).initial.boxes∪fixed) (puzzle k a b).board.walls :=
    Finset.disjoint_union_left.mpr ⟨(puzzle k a b).initial_valid.2.1,
      Finset.disjoint_left.mpr (fun p hp=>external_rail_floor k a b (hm p hp))⟩
  have hx:=walk_horizontal hf p.1 q.1 p.2 (by
    intro x hlo hhi
    apply quadrant_free k a b fixed hm i (x,p.2)
    unfold Quadrant at hp hq ⊢
    dsimp only at hlo hhi ⊢
    split_ifs at hp hq ⊢ <;> omega)
  have hy:=walk_vertical hf q.1 p.2 q.2 (by
    intro y hlo hhi
    apply quadrant_free k a b fixed hm i (q.1,y)
    unfold Quadrant at hp hq ⊢
    dsimp only at hlo hhi ⊢
    split_ifs at hp hq ⊢ <;> omega)
  exact hx.trans hy

theorem outerCorner_quadrant (i : Fin 4) : Quadrant i (outerCorner i) := by
  fin_cases i <;> unfold Quadrant outerCorner <;> decide +kernel

def nativePortal (k : Kind) (a b : Bool) (i : Fin 4) :
    PushFS.Cell (native k a b).width (native k a b).height :=
  match k with
  | .east | .west=>Chain.corner 200000 i
  | .south=>Chain.corner 198061 i
  | .westSouth=>(Polyline.L.turnRect 99970 98999 (by decide) (by decide)).cells (Turn.corner i)
  | .eastSouth=>(Out.turnRect 99970 98979 (by decide) (by decide)).cells (Turn.corner i)
  | .southEast=>(In.turnRect 98981 99969 (by decide) (by decide)).cells (Turn.corner i)
  | .southWest=>(Polyline.L.turnRect 99001 99969 (by decide) (by decide)).cells (Turn.corner i)

def portal (k : Kind) (a b : Bool) (i : Fin 4) : Cell :=
  (nativeEmbedding k a b (GridIsometry.refl width height).embedding).cells (nativePortal k a b i)

def portalPoint : Kind→Fin 4→ℕ×ℕ
  | .east,i=>![(1,99024),(200003,99024),(1,99042),(200003,99042)] i
  | .west,i=>![(200003,99024),(1,99024),(200003,99042),(1,99042)] i
  | .south,i=>![(100011,1),(100011,198064),(99993,1),(99993,198064)] i
  | .westSouth,i=>![(99993,99025),(100035,99025),(99993,99063),(100035,99063)] i
  | .eastSouth,i=>![(100011,99025),(99969,99025),(100011,99063),(99969,99063)] i
  | .southEast,i=>![(99994,99042),(99994,99000),(100032,99042),(100032,99000)] i
  | .southWest,i=>![(100010,99042),(100010,99000),(99972,99042),(99972,99000)] i

private theorem portal_coordinates (k : Kind) (a b : Bool) (i : Fin 4) :
    ((portal k a b i).1.val,(portal k a b i).2.val)=portalPoint k i := by
  cases k
  · change (0+(Chain.corner 200000 i).1.val,99023+(Chain.corner 200000 i).2.val)=_
    fin_cases i <;> norm_num [Chain.corner,portalPoint]
  · change (0+(200005-((Chain.corner 200000 i).1.val+1)),99023+(Chain.corner 200000 i).2.val)=_
    fin_cases i <;> norm_num [Chain.corner,portalPoint]
  · change (99992+(21-((Chain.corner 198061 i).2.val+1)),0+(Chain.corner 198061 i).1.val)=_
    fin_cases i <;> norm_num [Chain.corner,portalPoint]
  · change (99992+(0+(Turn.corner i).1.val),99023+(1+(Turn.corner i).2.val))=_
    fin_cases i <;> norm_num [Turn.corner,portalPoint]
  · change (0+(100013-((0+(Turn.corner i).1.val)+1)),99023+(1+(Turn.corner i).2.val))=_
    fin_cases i <;> norm_num [Turn.corner,portalPoint]
  · change (99992+(1+(Turn.corner i).2.val),0+(99044-((0+(Turn.corner i).1.val)+1)))=_
    fin_cases i <;> norm_num [Turn.corner,portalPoint]
  · change (0+(100013-((1+(Turn.corner i).2.val)+1)),0+(99044-((0+(Turn.corner i).1.val)+1)))=_
    fin_cases i <;> norm_num [Turn.corner,portalPoint]

theorem portal_quadrant_exists (k : Kind) (a b : Bool) (i : Fin 4) :
    ∃j : Fin 4,Quadrant i (portal k a b j) := by
  have check : ∀k : Kind,∀i : Fin 4,∃j : Fin 4,
      (if i.val%2=0 then (portalPoint k j).1<100000 else 100004<(portalPoint k j).1) ∧
      (if i.val<2 then (portalPoint k j).2<99031 else 99035<(portalPoint k j).2) := by decide +kernel
  obtain ⟨j,hj⟩:=check k i
  refine ⟨j,?_⟩
  have he:=portal_coordinates k a b j
  unfold Quadrant
  rw [←he] at hj
  exact hj

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
