/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadAmbient
public import PushFS.Reduction.GatePropagation

/-! Complete buffered-gate player routes and canonical macros using only four thin ambient wall stencils. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead.ThinShell

open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

variable {kind : Bool} {n W H : ℕ} {hn : 2301≤n}
    {e : GridEmbedding (2*n+101) (2*n+137) W H} {B : Board W H} {outside : Finset (Cell W H)}
    (f : ThinShell kind n hn e B outside)

include f in
theorem gate_bridge (a c : Gates.Signals) (i : Fin 3) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside ⟨(GateLead.gate n).cells (bridgePoint kind i),boxes kind n hn a c⟩) ∧
    Reachable B (some 1)
      (e.extend outside ⟨(GateLead.gate n).cells (bridgePoint kind i),boxes kind n hn a c⟩)
      (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.gate n).trans e
  let xs := (leadBoxes kind n hn c).map e.cells∪outside
  let fs := fixed z xs
  let fr := Gates.canonicalBoxes kind a∪fs
  have hfs : fs ⊆ Gates.boundaryNeighbors kind c := f.gate_fixed_neighbors c
  have hf : fr ⊆ Gates.reserved kind :=
    Finset.union_subset (Gates.canonicalBoxes_reserved kind a) (hfs.trans (boundary_reserved kind c))
  have hw : Disjoint fr (Gates.walls kind) := Finset.disjoint_union_left.mpr
    ⟨Gates.canonicalBoxes_floor kind a,(Gates.boundaryNeighbors_floor kind c).mono_left hfs⟩
  have hb := bridge_paths kind i
  have hforward := (Gates.corner_reachable kind (bridgeCorner kind i) ∅ fr hf hw).trans (frame_empty hf hw hb.1)
  have hback := (frame_empty hf hw hb.2).trans (Gates.corner_to_hub kind (bridgeCorner kind i) ∅ fr hf hw)
  have hfwd : Reachable (Gates.board kind ∅) (some 1)
      (Gates.withFixed fs (Gates.canonical kind a))
      (Gates.withFixed fs ⟨bridgePoint kind i,Gates.canonicalBoxes kind a⟩) := hforward
  have hbak : Reachable (Gates.board kind ∅) (some 1)
      (Gates.withFixed fs ⟨bridgePoint kind i,Gates.canonicalBoxes kind a⟩)
      (Gates.withFixed fs (Gates.canonical kind a)) := hback
  have hfwd' := z.reachable_withFixed f.gate
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.leads_floor c) hfwd
  have hbak' := z.reachable_withFixed f.gate
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.leads_floor c) hbak
  simpa only [z,xs,place_gate,place_gate_at] using And.intro hfwd' hbak'

include f in
private theorem west_hubs (hc : fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.neighbors n)
    (a c : Gates.Signals) (ha : a.left=false) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c)) (e.extend outside (atWest kind n hn a c)) ∧
    Reachable B (some 1) (e.extend outside (atWest kind n hn a c)) (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.west kind n).trans e
  let xs := (westExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hh := Chain.corners_placed n hn (Chain.uniform n c.left) 0 fs
    (west_fixed_neighbors hc a c ha) z f.west
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).1
  simp only [Chain.state,State.place,z,xs,place_west] at hh
  have hg := f.gate_bridge a c 0
  rw [west_bridge] at hg
  exact ⟨hg.1.trans hh.2,hh.1.trans hg.2⟩

include f in
private theorem north_hubs (hc : fixed
    ((GateLead.north kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha :
        a.upper=false) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c)) (e.extend outside (atNorth kind n hn a c)) ∧
    Reachable B (some 1) (e.extend outside (atNorth kind n hn a c)) (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.north kind n).trans e
  let xs := (northExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hh := Chain.corners_placed n hn (Chain.uniform n c.upper) 0 fs
    (north_fixed_neighbors hc a c ha) z f.north
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.1
  simp only [Chain.state,State.place,z,xs,place_north] at hh
  have hg := f.gate_bridge a c 1
  rw [north_bridge] at hg
  exact ⟨hg.1.trans hh.2,hh.1.trans hg.2⟩

include f in
private theorem east_hubs (hc : fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.neighbors n)
    (a c : Gates.Signals) (ha : a.right=true) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c)) (e.extend outside (atEast kind n hn a c)) ∧
    Reachable B (some 1) (e.extend outside (atEast kind n hn a c)) (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.east kind n).trans e
  let xs := (eastExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hh := Chain.corners_placed n hn (Chain.uniform n (!c.right)) 0 fs
    (east_fixed_neighbors hc a c ha) z f.east
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.2
  simp only [Chain.state,State.place,z,xs,place_east] at hh
  have hg := f.gate_bridge a c 2
  rw [east_bridge] at hg
  exact ⟨hg.1.trans hh.2,hh.1.trans hg.2⟩

include f in
private theorem west_update (hc : fixed
    ((GateLead.west kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha :
        a.left=false) (b : Bool) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside (state kind n hn a ⟨b,c.upper,c.right⟩)) :=
  (f.west_hubs hc a c ha).1.trans ((f.west_macro hc a c ha b).trans (f.west_hubs hc a ⟨b,c.upper,c.right⟩ ha).2)

include f in
private theorem north_update (hc : fixed
    ((GateLead.north kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha :
        a.upper=false) (b : Bool) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside (state kind n hn a ⟨c.left,b,c.right⟩)) :=
  (f.north_hubs hc a c ha).1.trans ((f.north_macro hc a c ha b).trans (f.north_hubs hc a ⟨c.left,b,c.right⟩ ha).2)

include f in
private theorem east_update (hc : fixed
    ((GateLead.east kind n).trans e) outside ⊆ Chain.neighbors n) (a c : Gates.Signals) (ha :
        a.right=true) (b : Bool) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside (state kind n hn a ⟨c.left,c.upper,b⟩)) :=
  (f.east_hubs hc a c ha).1.trans ((f.east_macro hc a c ha b).trans (f.east_hubs hc a ⟨c.left,c.upper,b⟩ ha).2)

include f in
/-- One actual canonical port reversal needs the released outer frontier of that port alone. -/
theorem canonical_transition (a b : Gates.Signals) (ha : Gates.legal kind a) (hb : Gates.legal kind b)
    (hs : Gates.singleChange a b) (hc : portCollar kind n e outside (Gates.changingPort a b)) :
    Reachable B (some 1) (e.extend outside (state kind n hn a a)) (e.extend outside (state kind n hn b b)) := by
  rcases a with ⟨al,au,ar⟩
  rcases b with ⟨bl,bu,br⟩
  change (al≠bl ∧ au=bu ∧ ar=br) ∨ (al=bl ∧ au≠bu ∧ ar=br) ∨ (al=bl ∧ au=bu ∧ ar≠br) at hs
  rcases hs with ⟨hl,rfl,rfl⟩ | ⟨rfl,hu,rfl⟩ | ⟨rfl,rfl,hr⟩
  · have hw : fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.neighbors n := by
      simpa [portCollar,Gates.changingPort,hl] using hc
    exact GatePropagation.change_left f.gate_macro (f.west_update hw) _ _ _ _ hl ha hb
  · have hw : fixed ((GateLead.north kind n).trans e) outside ⊆ Chain.neighbors n := by
      simpa [portCollar,Gates.changingPort,hu] using hc
    exact GatePropagation.change_upper f.gate_macro (f.north_update hw) _ _ _ _ hu ha hb
  · have hw : fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.neighbors n := by
      simpa [portCollar,Gates.changingPort] using hc
    exact GatePropagation.change_right f.gate_macro (f.east_update hw) _ _ _ _ hr ha hb

end PushPuzzle.PushFS.Reduction.GateLead.ThinShell
