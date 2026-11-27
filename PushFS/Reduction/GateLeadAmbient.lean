/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadStorage
public import PushFS.Gadgets.Wires.Polyline.ThinFrame

/-! Four actual glyph stencils suffice for replay inside a larger physical board. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead

open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

variable {kind : Bool} {n W H : ℕ} {hn : 2301≤n}

/-- Literal wall agreement and real outer neighbors of the four primitive pieces. -/
structure ThinShell (kind : Bool) (n : ℕ) (hn : 2301≤n)
    (e : GridEmbedding (2*n+101) (2*n+137) W H) (B : Board W H) (outside : Finset (Cell W H)) : Prop where
  gate : ((GateLead.gate n).trans e).WallsAgree (Gates.board kind ∅) B
  west : ((GateLead.west kind n).trans e).WallsAgree (Chain.board n hn ∅) B
  north : ((GateLead.north kind n).trans e).WallsAgree (Chain.board n hn ∅) B
  east : ((GateLead.east kind n).trans e).WallsAgree (Chain.board n hn ∅) B
  outside_floor : Disjoint outside B.walls
  gate_empty : ∀ p, ((GateLead.gate n).trans e).cells p ∉ outside

/-- The literal outside-box condition at the single port being propagated. -/
def portCollar (kind : Bool) (n : ℕ)
    (e : GridEmbedding (2*n+101) (2*n+137) W H) (outside : Finset (Cell W H)) (i : Fin 3) : Prop :=
  if i=0 then fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.neighbors n
  else if i=1 then fixed ((GateLead.north kind n).trans e) outside ⊆ Chain.neighbors n
  else fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.neighbors n

namespace ThinShell

variable {e : GridEmbedding (2*n+101) (2*n+137) W H} {B : Board W H} {outside : Finset (Cell W H)}
    (f : ThinShell kind n hn e B outside)

private theorem mapped_floor {w h : ℕ} {z : GridEmbedding w h W H} {C : Board w h}
    (hw : z.WallsAgree C B) {xs : Finset (Cell w h)} (hf : Disjoint xs C.walls) :
    Disjoint (xs.map z.cells) B.walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hwP
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  exact Finset.disjoint_left.mp hf hq ((hw q).mp hwP)

include f in
/-- Every independently phased owned box remains actual ambient floor. -/
private theorem pieces_floor (a c : Gates.Signals) :
    Disjoint ((gateBoxes n kind a).map e.cells) B.walls ∧
    Disjoint ((westBoxes kind n hn c.left).map e.cells) B.walls ∧
    Disjoint ((northBoxes kind n hn c.upper).map e.cells) B.walls ∧
    Disjoint ((eastBoxes kind n hn (!c.right)).map e.cells) B.walls := by
  have hg := mapped_floor f.gate (Gates.canonicalBoxes_floor kind a)
  have hw := mapped_floor f.west (Chain.boxes_floor n hn (Chain.uniform n c.left))
  have hno := mapped_floor f.north (Chain.boxes_floor n hn (Chain.uniform n c.upper))
  have he := mapped_floor f.east (Chain.boxes_floor n hn (Chain.uniform n (!c.right)))
  simpa only [gateBoxes,westBoxes,northBoxes,eastBoxes,Finset.map_map,GridEmbedding.trans]
    using And.intro hg (And.intro hw (And.intro hno he))

include f in
theorem leads_floor (c : Gates.Signals) : Disjoint ((leadBoxes kind n hn c).map e.cells∪outside) B.walls := by
  have hh := f.pieces_floor zero c
  simp only [leadBoxes,Finset.map_union,Finset.disjoint_union_left]
  exact ⟨⟨⟨hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩,f.outside_floor⟩

include f in
theorem external_floor (a c : Gates.Signals) :
    Disjoint ((westExternal kind n hn a c).map e.cells∪outside) B.walls ∧
    Disjoint ((northExternal kind n hn a c).map e.cells∪outside) B.walls ∧
    Disjoint ((eastExternal kind n hn a c).map e.cells∪outside) B.walls := by
  have hh := f.pieces_floor a c
  simp only [westExternal,northExternal,eastExternal,Finset.map_union,Finset.disjoint_union_left]
  exact ⟨⟨⟨⟨hh.1,hh.2.2.1⟩,hh.2.2.2⟩,f.outside_floor⟩,
    ⟨⟨⟨hh.1,hh.2.1⟩,hh.2.2.2⟩,f.outside_floor⟩,
    ⟨⟨⟨hh.1,hh.2.1⟩,hh.2.2.1⟩,f.outside_floor⟩⟩

theorem fixed_inside {w h : ℕ} (z : GridEmbedding w h (2*n+101) (2*n+137))
    (xs : Finset (C n)) (mask : Finset (Cell w h))
    (hin : fixed z xs ⊆ mask) (hout : fixed (z.trans e) outside ⊆ mask) :
    fixed (z.trans e) (xs.map e.cells∪outside) ⊆ mask := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_fixed _ _ p).mp hp) with hp | hp
  · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
    have he' : q=z.cells p := e.cells.injective he
    exact hin ((mem_fixed _ _ p).mpr (he' ▸ hq))
  · exact hout ((mem_fixed _ _ p).mpr hp)

include f in
theorem gate_fixed_neighbors (c : Gates.Signals) :
    fixed ((GateLead.gate n).trans e) ((leadBoxes kind n hn c).map e.cells∪outside) ⊆ Gates.boundaryNeighbors kind c := by
  apply fixed_inside _ _ _ (GateLead.gate_fixed_neighbors kind n hn c)
  intro p hp
  exact False.elim (f.gate_empty p ((mem_fixed _ _ p).mp hp))

theorem west_fixed_neighbors (hc : fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha : a.left=false) :
    fixed ((GateLead.west kind n).trans e) ((westExternal kind n hn a c).map e.cells∪outside) ⊆ Chain.neighbors n :=
  fixed_inside _ _ _ (GateLead.west_fixed_neighbors kind n hn a c ha) hc

theorem north_fixed_neighbors (hc : fixed ((GateLead.north kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha : a.upper=false) :
    fixed ((GateLead.north kind n).trans e) ((northExternal kind n hn a c).map e.cells∪outside) ⊆ Chain.neighbors n :=
  fixed_inside _ _ _ (GateLead.north_fixed_neighbors kind n hn a c ha) hc

theorem east_fixed_neighbors (hc : fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha : a.right=true) :
    fixed ((GateLead.east kind n).trans e) ((eastExternal kind n hn a c).map e.cells∪outside) ⊆ Chain.neighbors n :=
  fixed_inside _ _ _ (GateLead.east_fixed_neighbors kind n hn a c ha) hc

/-- Exact nested placement retains every box once and the same actual player position. -/
theorem place_gate (a c : Gates.Signals) :
    ((GateLead.gate n).trans e).extend ((leadBoxes kind n hn c).map e.cells∪outside) (Gates.canonical kind a)=
      e.extend outside (state kind n hn a c) := by
  rw [Polyline.Frame.extend_trans,GateLead.place_gate]

theorem place_gate_at (a c : Gates.Signals) (p : Gates.C) :
    ((GateLead.gate n).trans e).extend ((leadBoxes kind n hn c).map e.cells∪outside)
      ⟨p,Gates.canonicalBoxes kind a⟩=
      e.extend outside ⟨(GateLead.gate n).cells p,boxes kind n hn a c⟩ := by
  rw [Polyline.Frame.extend_trans]
  rfl

theorem place_west (a c : Gates.Signals) (p : Chain.C n) :
    ((GateLead.west kind n).trans e).extend ((westExternal kind n hn a c).map e.cells∪outside)
      ⟨p,Chain.boxes n hn (Chain.uniform n c.left)⟩=
      e.extend outside ⟨(GateLead.west kind n).cells p,boxes kind n hn a c⟩ := by
  rw [Polyline.Frame.extend_trans,GateLead.place_west]

theorem place_north (a c : Gates.Signals) (p : Chain.C n) :
    ((GateLead.north kind n).trans e).extend ((northExternal kind n hn a c).map e.cells∪outside)
      ⟨p,Chain.boxes n hn (Chain.uniform n c.upper)⟩=
      e.extend outside ⟨(GateLead.north kind n).cells p,boxes kind n hn a c⟩ := by
  rw [Polyline.Frame.extend_trans,GateLead.place_north]

theorem place_east (a c : Gates.Signals) (p : Chain.C n) :
    ((GateLead.east kind n).trans e).extend ((eastExternal kind n hn a c).map e.cells∪outside)
      ⟨p,Chain.boxes n hn (Chain.uniform n (!c.right))⟩=
      e.extend outside ⟨(GateLead.east kind n).cells p,boxes kind n hn a c⟩ := by
  rw [Polyline.Frame.extend_trans,GateLead.place_east]

include f in
/-- The full gate macro uses only its actual local wall stencil and real physical neighbors. -/
theorem gate_macro (a b : Gates.Signals) (ha : Gates.legal kind a) (hb : Gates.legal kind b) (hs : Gates.singleChange a b) :
    Reachable B (some 1) (e.extend outside (state kind n hn a (Gates.neighborSignals a b)))
      (e.extend outside (state kind n hn b (Gates.neighborSignals a b))) := by
  let c := Gates.neighborSignals a b
  let z := (GateLead.gate n).trans e
  let xs := (leadBoxes kind n hn c).map e.cells∪outside
  let fs := fixed z xs
  have hr := Gates.canonical_transition_neighbors kind a b ha hb hs ∅ fs (f.gate_fixed_neighbors c)
  have hh := z.reachable_withFixed f.gate
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.leads_floor c) hr
  simpa only [z,xs,place_gate] using hh

include f in
theorem west_macro (hc : fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha : a.left=false) (b : Bool) :
    Reachable B (some 1) (e.extend outside (atWest kind n hn a c))
      (e.extend outside (atWest kind n hn a ⟨b,c.upper,c.right⟩)) := by
  let z := (GateLead.west kind n).trans e
  let xs := (westExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hh := Chain.transition_placed n hn c.left b fs (west_fixed_neighbors hc a c ha) z f.west
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).1
  have hx : xs=(westExternal kind n hn a ⟨b,c.upper,c.right⟩).map e.cells∪outside := rfl
  change Reachable _ _ (z.extend xs ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n c.left)⟩)
    (z.extend xs ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n b)⟩) at hh
  rw [place_west,hx,place_west] at hh
  exact hh

include f in
theorem north_macro (hc : fixed ((GateLead.north kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha : a.upper=false) (b : Bool) :
    Reachable B (some 1) (e.extend outside (atNorth kind n hn a c))
      (e.extend outside (atNorth kind n hn a ⟨c.left,b,c.right⟩)) := by
  let z := (GateLead.north kind n).trans e
  let xs := (northExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hh := Chain.transition_placed n hn c.upper b fs (north_fixed_neighbors hc a c ha) z f.north
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.1
  have hx : xs=(northExternal kind n hn a ⟨c.left,b,c.right⟩).map e.cells∪outside := rfl
  change Reachable _ _ (z.extend xs ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n c.upper)⟩)
    (z.extend xs ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n b)⟩) at hh
  rw [place_north,hx,place_north] at hh
  exact hh

include f in
theorem east_macro (hc : fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha : a.right=true) (b : Bool) :
    Reachable B (some 1) (e.extend outside (atEast kind n hn a c))
      (e.extend outside (atEast kind n hn a ⟨c.left,c.upper,b⟩)) := by
  let z := (GateLead.east kind n).trans e
  let xs := (eastExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hh := Chain.transition_placed n hn (!c.right) (!b) fs (east_fixed_neighbors hc a c ha) z f.east
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.2
  have hx : xs=(eastExternal kind n hn a ⟨c.left,c.upper,b⟩).map e.cells∪outside := rfl
  change Reachable _ _ (z.extend xs ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n (!c.right))⟩)
    (z.extend xs ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n (!b))⟩) at hh
  rw [place_east,hx,place_east] at hh
  exact hh

end ThinShell
end PushPuzzle.PushFS.Reduction.GateLead
