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
public import PushFS.Reduction.FullGateSlots
public import PushFS.Walking

/-! Real free walking corridors in the complete gate's exterior frame. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

def outerCorner (i : Fin 4) : C := ![(1,1),(200005,1),(1,198066),(200005,198066)] i

/-- Possible external endpoint boxes lie only on the true exposed port rails. -/
def OuterRail (p : C) : Prop :=
  (p.2.val=99034 ∧(p.1.val<7 ∨200000≤p.1.val)) ∨
    (p.1.val=100003 ∧(p.2.val<7 ∨198061≤p.2.val))

def FrameTrack : Direction→C→Prop
  | .west,p | .east,p=>p.2.val=99034
  | .north,p | .south,p=>p.1.val=100003

def FrameSafe : Direction→C→Prop
  | .west,p | .east,p=>p.2.val<99034 ∨99036<p.2.val
  | .north,p | .south,p=>p.1.val<100001 ∨100003<p.1.val

def SameFrameSide : Direction→C→C→Prop
  | .west,p,q | .east,p,q=>(p.2.val<99034 ∧q.2.val<99034) ∨(99036<p.2.val ∧99036<q.2.val)
  | .north,p,q | .south,p,q=>(p.1.val<100001 ∧q.1.val<100001) ∨(100003<p.1.val ∧100003<q.1.val)

private theorem endpoint_track (d : Direction) (inc a prev : Bool) (p : C)
    (he : (p.1.val,p.2.val)=endpointPoint d inc a prev) : FrameTrack d p := by
  cases d <;> dsimp only [endpointPoint,FrameTrack] at he ⊢
  all_goals first | exact congrArg Prod.fst he | exact congrArg Prod.snd he

private theorem source_frame_track (g : GateTileState) (d : Direction) (i : Inventory.Index g)
    (l : Inventory.Labels g i)
    (hf : InFrame d ((Inventory.offset g i).1+((Inventory.matching g i).source l).1.val,
      (Inventory.offset g i).2+((Inventory.matching g i).source l).2.val)) :
    ∃inc a prev,((Inventory.offset g i).1+((Inventory.matching g i).source l).1.val,
      (Inventory.offset g i).2+((Inventory.matching g i).source l).2.val)=endpointPoint d inc a prev := by
  have hh:=source_identity g d i l hf
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact hh.elim
  · rcases hh with ⟨_,_,hh|hh⟩
    · exact ⟨_,_,false,hh.2⟩
    · exact ⟨_,_,true,hh.2.2⟩
  · exact hh.elim
  · exact l.elim0

private theorem target_frame_track (g : GateTileState) (d : Direction) (i : Inventory.Index g)
    (l : Inventory.Labels g i)
    (hf : InFrame d ((Inventory.offset g i).1+((Inventory.matching g i).target l).1.val,
      (Inventory.offset g i).2+((Inventory.matching g i).target l).2.val)) :
    ∃inc a prev,((Inventory.offset g i).1+((Inventory.matching g i).target l).1.val,
      (Inventory.offset g i).2+((Inventory.matching g i).target l).2.val)=endpointPoint d inc a prev := by
  have hh:=target_identity g d i l hf
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact hh.elim
  · rcases hh with ⟨_,_,hh|hh⟩
    · exact ⟨_,_,false,hh.2⟩
    · exact ⟨_,_,true,hh.2.2⟩
  · exact hh.elim
  · exact l.elim0

private theorem matching_mem {P : Instance} {Label : Type} [Fintype Label] (M : SlotMatching P Label) (goal : Bool) (q : Cell P.width P.height)
    (hq : q∈(if goal then P.board.goals else P.initial.boxes)) :
    ∃l,(if goal then M.target l else M.source l)=q := by
  cases goal
  · change q∈P.initial.boxes at hq
    rw [←M.source_image] at hq
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hq
    exact ⟨l,he⟩
  · change q∈P.board.goals at hq
    rw [←M.target_image] at hq
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hq
    exact ⟨l,he⟩

private theorem profile_frame_track (g : GateTileState) (f : Inventory.Index g→Bool) (player : C)
    (d : Direction) (p : C) (hf : InFrame d (p.1.val,p.2.val)) (hp : p∈(profile g f player).boxes) : FrameTrack d p := by
  obtain ⟨i,q,hq,he⟩:=(mem_profile g f player p).mp hp
  obtain ⟨l,hl⟩:=matching_mem (Inventory.matching g i) (f i) q hq
  have hecoords : ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)=(p.1.val,p.2.val):=
    congrArg (fun p : C=>(p.1.val,p.2.val)) he
  have he':=(congrArg (fun q : Cell (Inventory.piece g i).width (Inventory.piece g i).height=>
    ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)) hl).trans hecoords
  cases hb : f i
  · simp only [hb,Bool.false_eq_true,ite_false] at he'
    obtain ⟨inc,a,prev,hh⟩:=source_frame_track g d i l (he'.symm ▸hf)
    exact endpoint_track d inc a prev p (he'.symm.trans hh)
  · simp only [hb,ite_true] at he'
    obtain ⟨inc,a,prev,hh⟩:=target_frame_track g d i l (he'.symm ▸hf)
    exact endpoint_track d inc a prev p (he'.symm.trans hh)

private theorem outer_rail_track (d : Direction) (p : C) (hf : InFrame d (p.1.val,p.2.val)) (hp : OuterRail p) : FrameTrack d p := by
  cases d <;> dsimp only [OuterRail,InFrame,FrameTrack] at * <;> omega

theorem outer_rail_floor (g : GateTileState) (p : C) (hp : OuterRail p) : p∉(fullPuzzle g).board.walls := by
  rcases hp with ⟨hy,hx|hx⟩|⟨hx,hy|hy⟩
  · intro hw
    have hh:=(walls g .west p hx).mp hw
    dsimp only [Guard] at hh
    omega
  · intro hw
    have hh:=(walls g .east p hx).mp hw
    dsimp only [Guard] at hh
    omega
  · intro hw
    have hh:=(walls g .north p hy).mp hw
    dsimp only [Guard] at hh
    omega
  · intro hw
    have hh:=(walls g .south p hy).mp hw
    dsimp only [Guard] at hh
    omega

private theorem track_not_safe (d : Direction) (p : C) (ht : FrameTrack d p) (hs : FrameSafe d p) : False := by
  cases d <;> dsimp only [FrameTrack,FrameSafe] at * <;> omega

/-- Both complete canonical inventories and all possible endpoint-neighbor boxes leave these literal exterior lanes free. -/
private theorem outer_frame_free (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterRail p) (d : Direction) (p : C)
    (hf : InFrame d (p.1.val,p.2.val)) (hs : FrameSafe d p) :
    Free (fullPuzzle g).board ((profile g f (fullAtlas g).player).boxes∪fixed) p := by
  constructor
  · intro hw
    have hh:=(walls g d p hf).mp hw
    cases d <;> dsimp only [FrameSafe,Guard] at * <;> omega
  · intro hb
    rcases Finset.mem_union.mp hb with hb|hb
    · exact track_not_safe d p (profile_frame_track g f _ d p hf hb) hs
    · exact track_not_safe d p (outer_rail_track d p hf (hm p hb)) hs

private theorem outer_frame_boxes_floor (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterRail p) : Disjoint ((profile g f (fullAtlas g).player).boxes∪fixed) (fullPuzzle g).board.walls := by
  apply Finset.disjoint_union_left.mpr
  refine ⟨profile_floor g f _,Finset.disjoint_left.mpr ?_⟩
  exact fun p hp hw=>outer_rail_floor g p (hm p hp) hw

private theorem frame_walk_forward (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterRail p) (d : Direction) (p q : C)
    (hp : InFrame d (p.1.val,p.2.val)) (hq : InFrame d (q.1.val,q.2.val)) (hs : SameFrameSide d p q) :
    Reachable (fullPuzzle g).board (some 1) ⟨p,(profile g f (fullAtlas g).player).boxes∪fixed⟩
      ⟨q,(profile g f (fullAtlas g).player).boxes∪fixed⟩ := by
  have hfloor:=outer_frame_boxes_floor g f fixed hm
  cases d <;> dsimp only [InFrame,SameFrameSide] at hp hq hs
  case west=>
    have hx := walk_horizontal hfloor p.1 q.1 p.2 (by
      intro x hlo hhi
      apply outer_frame_free g f fixed hm .west (x,p.2)
      · dsimp only [InFrame]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega
      · dsimp only [FrameSafe]; omega)
    have hy := walk_vertical hfloor q.1 p.2 q.2 (by
      intro y hlo hhi
      apply outer_frame_free g f fixed hm .west (q.1,y)
      · exact hq
      · dsimp only [FrameSafe]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega)
    exact hx.trans hy
  case east=>
    have hx := walk_horizontal hfloor p.1 q.1 p.2 (by
      intro x hlo hhi
      apply outer_frame_free g f fixed hm .east (x,p.2)
      · dsimp only [InFrame]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega
      · dsimp only [FrameSafe]; omega)
    have hy := walk_vertical hfloor q.1 p.2 q.2 (by
      intro y hlo hhi
      apply outer_frame_free g f fixed hm .east (q.1,y)
      · exact hq
      · dsimp only [FrameSafe]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega)
    exact hx.trans hy
  case north=>
    have hy := walk_vertical hfloor p.1 p.2 q.2 (by
      intro y hlo hhi
      apply outer_frame_free g f fixed hm .north (p.1,y)
      · dsimp only [InFrame]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega
      · dsimp only [FrameSafe]; omega)
    have hx := walk_horizontal hfloor p.1 q.1 q.2 (by
      intro x hlo hhi
      apply outer_frame_free g f fixed hm .north (x,q.2)
      · exact hq
      · dsimp only [FrameSafe]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega)
    exact hy.trans hx
  case south=>
    have hy := walk_vertical hfloor p.1 p.2 q.2 (by
      intro y hlo hhi
      apply outer_frame_free g f fixed hm .south (p.1,y)
      · dsimp only [InFrame]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega
      · dsimp only [FrameSafe]; omega)
    have hx := walk_horizontal hfloor p.1 q.1 q.2 (by
      intro x hlo hhi
      apply outer_frame_free g f fixed hm .south (x,q.2)
      · exact hq
      · dsimp only [FrameSafe]
        simp only [Nat.min_def,Nat.max_def] at hlo hhi
        split_ifs at hlo hhi <;> omega)
    exact hy.trans hx

/-- Two true exterior-frame points on the same side of a port connect by literal horizontal and vertical walks. -/
theorem outer_frame_walk (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterRail p) (d : Direction) (p q : C)
    (hp : InFrame d (p.1.val,p.2.val)) (hq : InFrame d (q.1.val,q.2.val)) (hs : SameFrameSide d p q) :
    Reachable (fullPuzzle g).board (some 1) ⟨p,(profile g f (fullAtlas g).player).boxes∪fixed⟩
      ⟨q,(profile g f (fullAtlas g).player).boxes∪fixed⟩ ∧
    Reachable (fullPuzzle g).board (some 1) ⟨q,(profile g f (fullAtlas g).player).boxes∪fixed⟩
      ⟨p,(profile g f (fullAtlas g).player).boxes∪fixed⟩ := by
  have hsym : SameFrameSide d q p:=by
    cases d <;> dsimp only [SameFrameSide] at * <;> tauto
  exact ⟨frame_walk_forward g f fixed hm d p q hp hq hs,frame_walk_forward g f fixed hm d q p hq hp hsym⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
