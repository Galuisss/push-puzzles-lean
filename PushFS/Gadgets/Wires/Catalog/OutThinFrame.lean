/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutMovement
public import PushFS.Gadgets.Wires.Polyline.ThinFrame

/-! Full actual mixed-L replay under three thin wall charts and literal physical endpoint collars. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {W H : ℕ}

/-- Only actual thin-glyph walls and real physical neighbor boxes constrain the ambient board. -/
structure ThinFrame (e : GridEmbedding (m+43) (n+64) W H) (B : Board W H)
    (outside : Finset (PushFS.Cell W H)) : Prop where
  incoming : ((inEmbed m n hm hn).trans e).WallsAgree (Chain.board m hm ∅) B
  turn : ((turnRect m n hm hn).trans e).WallsAgree (Turn.template.board ∅) B
  outgoing : ((outEmbed m n hm hn).trans e).WallsAgree (Tail.board n hn ∅) B
  outside_floor : Disjoint outside B.walls
  incoming_collar : Polyline.Frame.fixed ((inEmbed m n hm hn).trans e) outside ⊆ Chain.neighbors m
  turn_collar : Polyline.Frame.fixed ((turnRect m n hm hn).trans e) outside ⊆ Turn.template.neighbors
  outgoing_collar : Polyline.Frame.fixed ((outEmbed m n hm hn).trans e) outside ⊆ Tail.neighbors n

namespace ThinFrame

variable {m n hm hn} {e : GridEmbedding (m+43) (n+64) W H} {B : Board W H}
    {outside : Finset (PushFS.Cell W H)} (f : ThinFrame m n hm hn e B outside)

private theorem mapped_floor {w h : ℕ} {z : GridEmbedding w h W H} {C : Board w h}
    (hw : z.WallsAgree C B) {xs : Finset (PushFS.Cell w h)} (hf : Disjoint xs C.walls) :
    Disjoint (xs.map z.cells) B.walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hwP
  obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
  exact Finset.disjoint_left.mp hf hq ((hw q).mp hwP)

include f in
/-- All complete owned inventories remain genuine ambient floor in independently mixed phases. -/
private theorem boxes_floor (a : Phases) : Disjoint
    ((boxes m n hm hn a).map e.cells∪outside) B.walls := by
  have hin:=mapped_floor f.incoming (Chain.boxes_floor m hm (Chain.uniform m (a 0)))
  have ht:=mapped_floor f.turn (Turn.checked.boxes_floor (a 1))
  have hout:=mapped_floor f.outgoing (Tail.boxes_floor n hn (Tail.uniform n (a 2)))
  change Disjoint (((inBoxes m n hm hn (a 0)∪turnBoxes m n hm hn (a 1))∪outBoxes m n hm hn (a 2)).map e.cells∪outside) B.walls
  simp only [Finset.map_union,Finset.disjoint_union_left]
  exact ⟨⟨⟨by simpa only [inBoxes,Finset.map_map,GridEmbedding.trans] using hin,
    by simpa only [turnBoxes,Finset.map_map,GridEmbedding.trans] using ht⟩,
    by simpa only [outBoxes,Finset.map_map,GridEmbedding.trans] using hout⟩,f.outside_floor⟩

include f in
private theorem external_floor (a : Phases) :
    Disjoint ((inExternal m n hm hn a).map e.cells∪outside) B.walls ∧
    Disjoint ((turnExternal m n hm hn a).map e.cells∪outside) B.walls ∧
    Disjoint ((outExternal m n hm hn a).map e.cells∪outside) B.walls := by
  have hf:=f.boxes_floor a
  simp only [boxes,Finset.map_union,Finset.disjoint_union_left] at hf
  simp only [inExternal,turnExternal,outExternal,Finset.map_union,Finset.disjoint_union_left]
  exact ⟨⟨⟨hf.1.1.2,hf.1.2⟩,hf.2⟩,⟨⟨hf.1.1.1,hf.1.2⟩,hf.2⟩,⟨hf.1.1,hf.2⟩⟩

private theorem inFixed_eq (a : Phases) :
    Polyline.Frame.fixed ((inEmbed m n hm hn).trans e) ((inExternal m n hm hn a).map e.cells∪outside)=
      inFixed m n hm hn a∪Polyline.Frame.fixed ((inEmbed m n hm hn).trans e) outside := by
  rw [Polyline.Frame.fixed_trans]
  rfl
private theorem turnFixed_eq (a : Phases) :
    Polyline.Frame.fixed ((turnRect m n hm hn).trans e) ((turnExternal m n hm hn a).map e.cells∪outside)=
      turnFixed m n hm hn a∪Polyline.Frame.fixed ((turnRect m n hm hn).trans e) outside := by
  rw [Polyline.Frame.fixed_trans]
  rfl
private theorem outFixed_eq (a : Phases) :
    Polyline.Frame.fixed ((outEmbed m n hm hn).trans e) ((outExternal m n hm hn a).map e.cells∪outside)=
      outFixed m n hm hn a∪Polyline.Frame.fixed ((outEmbed m n hm hn).trans e) outside := by
  rw [Polyline.Frame.fixed_trans]
  rfl

include f in
/-- Exact local macro transport, preserving the entire incoming/turn/outgoing and foreign inventory. -/
private theorem incoming_macro (a : Phases) (ha : a 1=true) (b : Bool) :
    Reachable B (some 1) (e.extend outside (atIn m n hm hn a))
      (e.extend outside ⟨(inEmbed m n hm hn).cells (Chain.hub m hm),
        inBoxes m n hm hn b∪turnBoxes m n hm hn (a 1)∪outBoxes m n hm hn (a 2)⟩) := by
  let z:=(inEmbed m n hm hn).trans e
  let xs:=(inExternal m n hm hn a).map e.cells∪outside
  let fixed:=Polyline.Frame.fixed z xs
  have hfixed : fixed⊆Chain.neighbors m := by
    dsimp only [fixed,xs,z]
    rw [inFixed_eq]
    exact Finset.union_subset (inFixed_neighbors m n hm hn a ha) f.incoming_collar
  have hr:=Chain.transition_placed m hm (a 0) b fixed hfixed z f.incoming
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
    (f.external_floor a).1
  simp only [State.place] at hr
  rw [Polyline.Frame.extend_trans,Polyline.Frame.extend_trans] at hr
  have hs : (inEmbed m n hm hn).extend (inExternal m n hm hn a) (Chain.state m hm (Chain.uniform m (a 0)))=atIn m n hm hn a :=
    place_in m n hm hn a (Chain.hub m hm)
  rw [hs] at hr
  have hh : (inEmbed m n hm hn).extend (inExternal m n hm hn a) (Chain.state m hm (Chain.uniform m b))=
      ⟨(inEmbed m n hm hn).cells (Chain.hub m hm),
        inBoxes m n hm hn b∪turnBoxes m n hm hn (a 1)∪outBoxes m n hm hn (a 2)⟩ := by
    apply State.ext
    · rfl
    change inBoxes m n hm hn b∪(turnBoxes m n hm hn (a 1)∪outBoxes m n hm hn (a 2))=_
    ac_rfl
  rw [hh] at hr
  exact hr

include f in
/-- The outgoing chain changes its complete inventory while every actual foreign box remains fixed. -/
private theorem outgoing_macro (a : Phases) (ha : a 1=false) (b : Bool) :
    Reachable B (some 1) (e.extend outside (atOut m n hm hn a))
      (e.extend outside ⟨(outEmbed m n hm hn).cells (Tail.hub n hn),
        inBoxes m n hm hn (a 0)∪turnBoxes m n hm hn (a 1)∪outBoxes m n hm hn b⟩) := by
  let z:=(outEmbed m n hm hn).trans e
  let xs:=(outExternal m n hm hn a).map e.cells∪outside
  let fixed:=Polyline.Frame.fixed z xs
  have hfixed : fixed⊆Tail.neighbors n := by
    dsimp only [fixed,xs,z]
    rw [outFixed_eq]
    exact Finset.union_subset (outFixed_neighbors m n hm hn a ha) f.outgoing_collar
  have hr:=Tail.transition_placed n hn (a 2) b fixed hfixed z f.outgoing
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
    (f.external_floor a).2.2
  simp only [State.place] at hr
  rw [Polyline.Frame.extend_trans,Polyline.Frame.extend_trans] at hr
  have hs : (outEmbed m n hm hn).extend (outExternal m n hm hn a) (Tail.state n hn (Tail.uniform n (a 2)))=atOut m n hm hn a :=
    place_out m n hm hn a (Tail.hub n hn)
  simp only [Tail.uniform] at hs
  rw [hs] at hr
  have hh : (outEmbed m n hm hn).extend (outExternal m n hm hn a) (Tail.state n hn (Tail.uniform n b))=
      ⟨(outEmbed m n hm hn).cells (Tail.hub n hn),
        inBoxes m n hm hn (a 0)∪turnBoxes m n hm hn (a 1)∪outBoxes m n hm hn b⟩ := by
    apply State.ext
    · rfl
    change outBoxes m n hm hn b∪(inBoxes m n hm hn (a 0)∪turnBoxes m n hm hn (a 1))=_
    ac_rfl
  simp only [Tail.uniform] at hh
  rw [hh] at hr
  exact hr

include f in
/-- The complete turn macro has its precise real two-box eastern collar and southern clearance. -/
private theorem turn_macro (a : Phases) (hi : a 0=false) (ho : a 2=true) (b : Bool) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a))
      (e.extend outside ⟨player m n,inBoxes m n hm hn (a 0)∪turnBoxes m n hm hn b∪outBoxes m n hm hn (a 2)⟩) := by
  let z:=(turnRect m n hm hn).trans e
  let xs:=(turnExternal m n hm hn a).map e.cells∪outside
  let fixed:=Polyline.Frame.fixed z xs
  have hfixed : fixed⊆Turn.template.neighbors := by
    dsimp only [fixed,xs,z]
    rw [turnFixed_eq]
    exact Finset.union_subset (turnFixed_neighbors m n hm hn a hi ho) f.turn_collar
  have hr:=z.reachable_withFixed f.turn
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
    (f.external_floor a).2.1 (Turn.checked.transition (a 1) b ∅ fixed hfixed)
  rw [Polyline.Frame.extend_trans,Polyline.Frame.extend_trans] at hr
  have hs : (turnRect m n hm hn).extend (turnExternal m n hm hn a) (Turn.template.state (a 1))=state m n hm hn a := by
    rw [Template.state,place_turn]
    apply State.ext
    · exact turn_hub m n hm hn
    · rfl
  rw [hs] at hr
  have hh : (turnRect m n hm hn).extend (turnExternal m n hm hn a) (Turn.template.state b)=
      ⟨player m n,inBoxes m n hm hn (a 0)∪turnBoxes m n hm hn b∪outBoxes m n hm hn (a 2)⟩ := by
    apply State.ext
    · exact turn_hub m n hm hn
    change turnBoxes m n hm hn b∪(inBoxes m n hm hn (a 0)∪outBoxes m n hm hn (a 2))=_
    ac_rfl
  rw [hh] at hr
  exact hr

private theorem neighbors_all (k : ℕ) : Chain.neighbors k⊆Chain.allNeighbors k := by
  intro p hp
  simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl <;> simp [Chain.allNeighbors]

private theorem tail_neighbors_all (k : ℕ) : Tail.neighbors k⊆Tail.allNeighbors k := by
  intro p hp
  simp only [FlippedChain.neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl <;> simp [FlippedChain.allNeighbors]

include f in
private theorem incoming_walking_fixed (a : Phases) :
    Polyline.Frame.fixed ((inEmbed m n hm hn).trans e) ((inExternal m n hm hn a).map e.cells∪outside)⊆Chain.allNeighbors m := by
  rw [inFixed_eq]
  exact Finset.union_subset (inFixed_allNeighbors m n hm hn a) (fun _ hp=>neighbors_all m (f.incoming_collar hp))

include f in
private theorem outgoing_walking_fixed (a : Phases) :
    Polyline.Frame.fixed ((outEmbed m n hm hn).trans e) ((outExternal m n hm hn a).map e.cells∪outside)⊆Tail.allNeighbors n := by
  rw [outFixed_eq]
  exact Finset.union_subset (outFixed_allNeighbors m n hm hn a) (fun _ hp=>tail_neighbors_all n (f.outgoing_collar hp))

include f in
private theorem turn_walking_fixed (a : Phases) :
    Polyline.Frame.fixed ((turnRect m n hm hn).trans e) ((turnExternal m n hm hn a).map e.cells∪outside)⊆Turn.template.reservedCells := by
  rw [turnFixed_eq]
  apply Finset.union_subset (turnFixed_reserved m n hm hn a)
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Turn.checked.neighbors_reserved p (f.turn_collar hp)⟩

include f in
/-- Exact incoming corner walks hold in every independently mixed global phase. -/
private theorem incoming_corners (a : Phases) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (atIn m n hm hn a))
      (e.extend outside ⟨(inEmbed m n hm hn).cells (Chain.corner m i),boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(inEmbed m n hm hn).cells (Chain.corner m i),boxes m n hm hn a⟩)
      (e.extend outside (atIn m n hm hn a)) := by
  let z:=(inEmbed m n hm hn).trans e
  let xs:=(inExternal m n hm hn a).map e.cells∪outside
  have hr:=Chain.corners_placed_allNeighbors m hm (Chain.uniform m (a 0)) i (Polyline.Frame.fixed z xs)
    (f.incoming_walking_fixed a) z f.incoming
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
    (f.external_floor a).1
  change Reachable _ _ ((inEmbed m n hm hn).trans e |>.extend xs ⟨Chain.hub m hm,Chain.boxes m hm (Chain.uniform m (a 0))⟩)
      ((inEmbed m n hm hn).trans e |>.extend xs ⟨Chain.corner m i,Chain.boxes m hm (Chain.uniform m (a 0))⟩) ∧
    Reachable _ _ ((inEmbed m n hm hn).trans e |>.extend xs ⟨Chain.corner m i,Chain.boxes m hm (Chain.uniform m (a 0))⟩)
      ((inEmbed m n hm hn).trans e |>.extend xs ⟨Chain.hub m hm,Chain.boxes m hm (Chain.uniform m (a 0))⟩) at hr
  simp only [xs,Polyline.Frame.extend_trans,place_in] at hr
  exact hr

include f in
/-- Exact outgoing corner walks retain every physical box, including both true collars. -/
private theorem outgoing_corners (a : Phases) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (atOut m n hm hn a))
      (e.extend outside ⟨(outEmbed m n hm hn).cells (Tail.corner n i),boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(outEmbed m n hm hn).cells (Tail.corner n i),boxes m n hm hn a⟩)
      (e.extend outside (atOut m n hm hn a)) := by
  let z:=(outEmbed m n hm hn).trans e
  let xs:=(outExternal m n hm hn a).map e.cells∪outside
  have hr:=Tail.corners_placed_allNeighbors n hn (Tail.uniform n (a 2)) i (Polyline.Frame.fixed z xs)
    (f.outgoing_walking_fixed a) z f.outgoing
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
    (f.external_floor a).2.2
  change Reachable _ _ ((outEmbed m n hm hn).trans e |>.extend xs ⟨Tail.hub n hn,Tail.boxes n hn (Tail.uniform n (a 2))⟩)
      ((outEmbed m n hm hn).trans e |>.extend xs ⟨Tail.corner n i,Tail.boxes n hn (Tail.uniform n (a 2))⟩) ∧
    Reachable _ _ ((outEmbed m n hm hn).trans e |>.extend xs ⟨Tail.corner n i,Tail.boxes n hn (Tail.uniform n (a 2))⟩)
      ((outEmbed m n hm hn).trans e |>.extend xs ⟨Tail.hub n hn,Tail.boxes n hn (Tail.uniform n (a 2))⟩) at hr
  simp only [xs,Polyline.Frame.extend_trans,place_out] at hr
  exact hr

include f in
/-- All four exact Turn corner walks hold with the actual full external inventory. -/
private theorem turn_corners (a : Phases) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a))
      (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩)
      (e.extend outside (state m n hm hn a)) := by
  let z:=(turnRect m n hm hn).trans e
  let xs:=(turnExternal m n hm hn a).map e.cells∪outside
  have hfw : Disjoint (Polyline.Frame.fixed z xs) Turn.template.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hw
    exact Finset.disjoint_left.mp (f.external_floor a).2.1 ((Polyline.Frame.mem_fixed z xs p).mp hp) ((f.turn p).mpr hw)
  have hr:=Turn.checked.corners_covered (a 1) i (Polyline.Frame.fixed z xs) (f.turn_walking_fixed a) hfw z f.turn
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
    (f.external_floor a).2.1
  change Reachable _ _ (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩) ∧
    Reachable _ _ (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩) at hr
  simp only [z,xs,Polyline.Frame.extend_trans,place_turn,turn_hub] at hr
  exact hr

private theorem corridor_free {actual : Finset Turn.C} (ha : actual⊆Turn.template.reservedCells)
    (p : Turn.C) (hp : (39≤p.1.val ∧ p.1.val≤43 ∧ p.2.val≤1) ∨
      (19≤p.1.val ∧ p.1.val≤43 ∧ p.2.val=39)) : Free (Turn.template.board ∅) actual p := by
  have check : ∀ p : Turn.C, ((39≤p.1.val ∧ p.1.val≤43 ∧ p.2.val≤1) ∨
      (19≤p.1.val ∧ p.1.val≤43 ∧ p.2.val=39)) → Turn.template.walkTest p=false := by decide +kernel
  have hh:=check p hp
  have hf : Turn.template.wall p=false ∧ Turn.template.reserved p=false := Bool.or_eq_false_iff.mp hh
  constructor
  · exact fun hw=>Bool.false_ne_true (hf.1.symm.trans ((Turn.template.mem_walls p).mp hw))
  · intro hb
    have hr:=(Finset.mem_filter.mp (ha hb)).2
    rw [hf.2] at hr
    contradiction

private theorem local_top {actual : Finset Turn.C} (ha : actual⊆Turn.template.reservedCells)
    (haw : Disjoint actual Turn.template.walls) (p q : Turn.C)
    (hp : 39≤p.1.val ∧ p.1.val≤43 ∧ p.2.val≤1)
    (hq : 39≤q.1.val ∧ q.1.val≤43 ∧ q.2.val≤1) :
    Reachable (Turn.template.board ∅) (some 1) ⟨p,actual⟩ ⟨q,actual⟩ := by
  rcases p with ⟨px,py⟩
  rcases q with ⟨qx,qy⟩
  dsimp only at hp hq
  have hv:=walk_vertical haw px py qy (fun y _ hhi=>corridor_free ha (px,y)
    (Or.inl ⟨hp.1,hp.2.1,by change y.val≤1; omega⟩))
  have hh:=walk_horizontal haw px qx qy (fun x hlo hhi=>corridor_free ha (x,qy)
    (Or.inl ⟨by change 39≤x.val; omega,by change x.val≤43; omega,hq.2.2⟩))
  exact hv.trans hh

private theorem local_tail {actual : Finset Turn.C} (ha : actual⊆Turn.template.reservedCells)
    (haw : Disjoint actual Turn.template.walls) (x y : Fin 45)
    (hx : 19≤x.val ∧ x.val≤43) (hy : 19≤y.val ∧ y.val≤43) :
    Reachable (Turn.template.board ∅) (some 1) ⟨(x,39),actual⟩ ⟨(y,39),actual⟩ := by
  apply walk_horizontal haw
  intro z hlo hhi
  exact corridor_free ha (z,39) (Or.inr ⟨by change 19≤z.val; omega,by change z.val≤43; omega,rfl⟩)

include f in
/-- Both short joining paths lie inside the actual guarded Turn rectangle, in every phase. -/
private theorem corridors (a : Phases) :
    (Reachable B (some 1) (e.extend outside ⟨topTurnPoint m n hm,boxes m n hm hn a⟩)
      (e.extend outside ⟨topInPoint m n,boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨topInPoint m n,boxes m n hm hn a⟩)
      (e.extend outside ⟨topTurnPoint m n hm,boxes m n hm hn a⟩)) ∧
    (Reachable B (some 1) (e.extend outside ⟨tailTurnPoint m n hm,boxes m n hm hn a⟩)
      (e.extend outside ⟨tailOutPoint m n,boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨tailOutPoint m n,boxes m n hm hn a⟩)
      (e.extend outside ⟨tailTurnPoint m n hm,boxes m n hm hn a⟩)) := by
  let z:=(turnRect m n hm hn).trans e
  let xs:=(turnExternal m n hm hn a).map e.cells∪outside
  let fixed:=Polyline.Frame.fixed z xs
  have hfw : Disjoint fixed Turn.template.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hw
    exact Finset.disjoint_left.mp (f.external_floor a).2.1 ((Polyline.Frame.mem_fixed z xs p).mp hp) ((f.turn p).mpr hw)
  have ha : Turn.template.boxes (a 1)∪fixed⊆Turn.template.reservedCells :=
    Finset.union_subset (Turn.checked.boxes_reserved _) (f.turn_walking_fixed a)
  have haw : Disjoint (Turn.template.boxes (a 1)∪fixed) Turn.template.walls :=
    Finset.disjoint_union_left.mpr ⟨Turn.checked.boxes_floor _,hfw⟩
  have lift (p q : Turn.C)
      (hr : Reachable (Turn.template.board ∅) (some 1) ⟨p,Turn.template.boxes (a 1)∪fixed⟩
        ⟨q,Turn.template.boxes (a 1)∪fixed⟩) :
      Reachable B (some 1) (e.extend outside ⟨(turnRect m n hm hn).cells p,boxes m n hm hn a⟩)
        (e.extend outside ⟨(turnRect m n hm hn).cells q,boxes m n hm hn a⟩) := by
    have hh:=z.reachable_withFixed (s:=⟨p,Turn.template.boxes (a 1)⟩)
      (t:=⟨q,Turn.template.boxes (a 1)⟩) f.turn
      (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp) (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp)
      (f.external_floor a).2.1 hr
    change Reachable B (some 1) (z.extend xs ⟨p,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨q,Turn.template.boxes (a 1)⟩) at hh
    simpa only [z,xs,Polyline.Frame.extend_trans,place_turn] using hh
  have ht0:=lift (43,1) (39,0) (local_top ha haw _ _ (by decide) (by decide))
  have ht1:=lift (39,0) (43,1) (local_top ha haw _ _ (by decide) (by decide))
  have hb0:=lift (43,39) (19,39) (local_tail ha haw _ _ (by decide) (by decide))
  have hb1:=lift (19,39) (43,39) (local_tail ha haw _ _ (by decide) (by decide))
  exact ⟨⟨ht0,ht1⟩,hb0,hb1⟩

include f in
/-- The common hub and incoming train hub have genuine bidirectional physical walks in every mixed phase. -/
private theorem incoming_hubs (a : Phases) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a)) (e.extend outside (atIn m n hm hn a)) ∧
    Reachable B (some 1) (e.extend outside (atIn m n hm hn a)) (e.extend outside (state m n hm hn a)) := by
  have ht:=f.turn_corners a 1
  have hi:=f.incoming_corners a 1
  rw [turn_corner1] at ht
  rw [in_corner1] at hi
  exact ⟨ht.1.trans ((f.corridors a).1.1.trans hi.2),hi.1.trans ((f.corridors a).1.2.trans ht.2)⟩

include f in
/-- The common hub and outgoing train hub remain connected with the complete actual inventories. -/
private theorem outgoing_hubs (a : Phases) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a)) (e.extend outside (atOut m n hm hn a)) ∧
    Reachable B (some 1) (e.extend outside (atOut m n hm hn a)) (e.extend outside (state m n hm hn a)) := by
  have ht:=f.turn_corners a 3
  have ho:=f.outgoing_corners a 0
  rw [turn_corner3] at ht
  rw [out_corner0] at ho
  exact ⟨ht.1.trans ((f.corridors a).2.1.trans ho.2),ho.1.trans ((f.corridors a).2.2.trans ht.2)⟩

include f in
/-- An entire actual L phase change is transported by three thin wall charts and literal collar cells. -/
theorem transition (a b : Bool) : Reachable B (some 1)
    (e.extend outside (state m n hm hn (uniform a))) (e.extend outside (state m n hm hn (uniform b))) := by
  have hin (i i' o : Bool) : Reachable B (some 1)
      (e.extend outside (state m n hm hn (phases i true o)))
      (e.extend outside (state m n hm hn (phases i' true o))) := by
    have hh:=f.incoming_macro (phases i true o) rfl i'
    exact (f.incoming_hubs (phases i true o)).1.trans (hh.trans (f.incoming_hubs (phases i' true o)).2)
  have hout (i o o' : Bool) : Reachable B (some 1)
      (e.extend outside (state m n hm hn (phases i false o)))
      (e.extend outside (state m n hm hn (phases i false o'))) := by
    have hh:=f.outgoing_macro (phases i false o) rfl o'
    exact (f.outgoing_hubs (phases i false o)).1.trans (hh.trans (f.outgoing_hubs (phases i false o')).2)
  have ht (t t' : Bool) : Reachable B (some 1)
      (e.extend outside (state m n hm hn (phases false t true)))
      (e.extend outside (state m n hm hn (phases false t' true))) := f.turn_macro _ rfl rfl t'
  have hf:=(hout false false true).trans ((ht false true).trans (hin false true true))
  have hb:=(hin true false true).trans ((ht true false).trans (hout false true false))
  rw [phases_uniform,phases_uniform] at hf hb
  cases a <;> cases b
  · exact .refl
  · exact hf
  · exact hb
  · exact .refl

end ThinFrame
end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out
