/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadAmbientWalking

/-! Buffered-gate transit keeps every gate and neighboring wire phase fixed. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem west_any_checked : ∀ (kind : Bool) (a : Gates.Signals) (i : Fin (Gates.slots kind).length),
    (Gates.position kind a i).1.val≤(if kind then 2 else 3) →
    (Gates.position kind a i).1.val+a.left.toNat=(if kind then 2 else 3) ∧
    (Gates.position kind a i).2.val=(if kind then 29 else 90) := by decide +kernel

private theorem north_any_checked : ∀ (kind : Bool) (a : Gates.Signals) (i : Fin (Gates.slots kind).length),
    (Gates.position kind a i).2.val≤3 →
    (Gates.position kind a i).1.val=(if kind then 43 else 44) ∧
    (Gates.position kind a i).2.val+a.upper.toNat=3 := by decide +kernel

private theorem east_any_checked : ∀ (kind : Bool) (a : Gates.Signals) (i : Fin (Gates.slots kind).length),
    (if kind then 78 else 77)≤(Gates.position kind a i).1.val →
    (Gates.position kind a i).1.val+a.right.toNat=(if kind then 79 else 78) ∧
    (Gates.position kind a i).2.val=90 := by decide +kernel

private theorem head_neighbor (n : ℕ) (p : Chain.C n) (hx : p.1.val≤1) (hy : p.2.val=10) :
    p∈Chain.allNeighbors n := by
  by_cases hz : p.1.val=0
  · have he : p=(⟨0,by omega⟩,10) := Prod.ext (Fin.ext hz) (Fin.ext hy)
    rw [he]
    simp [Chain.allNeighbors]
  · have hpx : p.1.val=1 := by omega
    have he : p=(⟨1,by omega⟩,10) := Prod.ext (Fin.ext hpx) (Fin.ext hy)
    rw [he]
    simp [Chain.allNeighbors]

private theorem west_gate_allNeighbors (kind : Bool) (n : ℕ) (a : Gates.Signals)
    (p : Chain.C n) (q : Gates.C) (hq : q∈Gates.canonicalBoxes kind a)
    (he : (west kind n).cells p=(gate n).cells q) : p∈Chain.allNeighbors n := by
  have hx := congrArg (fun p : C n=>p.1.val) he
  have hy := congrArg (fun p : C n=>p.2.val) he
  simp only [west_x,west_y,gate_x,gate_y] at hx hy
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  rw [← Gates.position_image] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  have hh := west_any_checked kind a i (by cases kind <;> simp_all <;> omega)
  have hb : a.left.toNat≤1 := by cases a.left <;> decide
  apply head_neighbor
  · cases kind <;> simp at hx hy hh <;> omega
  · cases kind <;> simp at hx hy hh <;> omega

private theorem north_gate_allNeighbors (kind : Bool) (n : ℕ) (a : Gates.Signals)
    (p : Chain.C n) (q : Gates.C) (hq : q∈Gates.canonicalBoxes kind a)
    (he : (north kind n).cells p=(gate n).cells q) : p∈Chain.allNeighbors n := by
  have hx := congrArg (fun p : C n=>p.1.val) he
  have hy := congrArg (fun p : C n=>p.2.val) he
  simp only [north_x,north_y,gate_x,gate_y] at hx hy
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  rw [← Gates.position_image] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  have hh := north_any_checked kind a i (by omega)
  have hb : a.upper.toNat≤1 := by cases a.upper <;> decide
  apply head_neighbor
  · omega
  · cases kind <;> simp at hx hy hh <;> omega

private theorem east_gate_allNeighbors (kind : Bool) (n : ℕ) (a : Gates.Signals)
    (p : Chain.C n) (q : Gates.C) (hq : q∈Gates.canonicalBoxes kind a)
    (he : (east kind n).cells p=(gate n).cells q) : p∈Chain.allNeighbors n := by
  have hx := congrArg (fun p : C n=>p.1.val) he
  have hy := congrArg (fun p : C n=>p.2.val) he
  simp only [east_x,east_y,gate_x,gate_y] at hx hy
  have hpy := p.2.isLt
  rw [← Gates.position_image] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  have hh := east_any_checked kind a i (by cases kind <;> simp_all <;> omega)
  have hb : a.right.toNat≤1 := by cases a.right <;> decide
  apply head_neighbor
  · cases kind <;> simp at hx hy hh <;> omega
  · omega

private theorem west_fixed_allNeighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) :
    fixed (west kind n) (westExternal kind n hn a c) ⊆ Chain.allNeighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_fixed _ _ p).mp hp) with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact west_gate_allNeighbors kind n a p q hq he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
      exact False.elim (west_ne_north kind n p q he.symm)
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (west_ne_east kind n p q he.symm)

private theorem north_fixed_allNeighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) :
    fixed (north kind n) (northExternal kind n hn a c) ⊆ Chain.allNeighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_fixed _ _ p).mp hp) with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact north_gate_allNeighbors kind n a p q hq he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
      exact False.elim (west_ne_north kind n q p he)
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (north_ne_east kind n p q he.symm)

private theorem east_fixed_allNeighbors (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) :
    fixed (east kind n) (eastExternal kind n hn a c) ⊆ Chain.allNeighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_fixed _ _ p).mp hp) with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
      exact east_gate_allNeighbors kind n a p q hq he.symm
    · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
      exact False.elim (west_ne_east kind n q p he)
  · obtain ⟨q,_,he⟩ := Finset.mem_map.mp hp
    exact False.elim (north_ne_east kind n q p he)

namespace ThinShell

variable {kind : Bool} {n W H : ℕ} {hn : 2301≤n}
    {e : GridEmbedding (2*n+101) (2*n+137) W H} {B : Board W H} {outside : Finset (Cell W H)}
    (f : ThinShell kind n hn e B outside)

include f in
/-- Actual gate and lead hubs connect in all independently fixed phases. -/
private theorem west_hubs_all
    (hc : fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.allNeighbors n) (a c : Gates.Signals) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c)) (e.extend outside (atWest kind n hn a c)) ∧
    Reachable B (some 1) (e.extend outside (atWest kind n hn a c)) (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.west kind n).trans e
  let xs := (westExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hfs : fs ⊆ Chain.allNeighbors n :=
    fixed_inside _ _ _ (GateLead.west_fixed_allNeighbors kind n hn a c) hc
  have hh := Chain.corners_placed_allNeighbors n hn (Chain.uniform n c.left) 0 fs
    hfs z f.west
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).1
  simp only [Chain.state,State.place,z,xs,place_west] at hh
  have hg := f.gate_bridge a c 0
  rw [west_bridge] at hg
  exact ⟨hg.1.trans hh.2,hh.1.trans hg.2⟩

include f in
/-- Every real lead corner is accessible with all owned and foreign box phases fixed. -/
theorem west_corners
    (hc : fixed ((GateLead.west kind n).trans e) outside ⊆ Chain.allNeighbors n) (a c : Gates.Signals) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside ⟨(GateLead.west kind n).cells (Chain.corner n i),boxes kind n hn a c⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(GateLead.west kind n).cells (Chain.corner n i),boxes kind n hn a c⟩)
      (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.west kind n).trans e
  let xs := (westExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hfs : fs ⊆ Chain.allNeighbors n :=
    fixed_inside _ _ _ (GateLead.west_fixed_allNeighbors kind n hn a c) hc
  have hh := Chain.corners_placed_allNeighbors n hn (Chain.uniform n c.left) i fs
    hfs z f.west
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).1
  simp only [Chain.state,State.place,z,xs,place_west] at hh
  have hg := f.west_hubs_all hc a c
  exact ⟨hg.1.trans hh.1,hh.2.trans hg.2⟩

include f in
/-- Actual gate and lead hubs connect in all independently fixed phases. -/
private theorem north_hubs_all
    (hc : fixed ((GateLead.north kind n).trans e) outside ⊆ Chain.allNeighbors n) (a c : Gates.Signals) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c)) (e.extend outside (atNorth kind n hn a c)) ∧
    Reachable B (some 1) (e.extend outside (atNorth kind n hn a c)) (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.north kind n).trans e
  let xs := (northExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hfs : fs ⊆ Chain.allNeighbors n :=
    fixed_inside _ _ _ (GateLead.north_fixed_allNeighbors kind n hn a c) hc
  have hh := Chain.corners_placed_allNeighbors n hn (Chain.uniform n c.upper) 0 fs
    hfs z f.north
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.1
  simp only [Chain.state,State.place,z,xs,place_north] at hh
  have hg := f.gate_bridge a c 1
  rw [north_bridge] at hg
  exact ⟨hg.1.trans hh.2,hh.1.trans hg.2⟩

include f in
/-- Every real lead corner is accessible with all owned and foreign box phases fixed. -/
theorem north_corners
    (hc : fixed ((GateLead.north kind n).trans e) outside ⊆ Chain.allNeighbors n) (a c : Gates.Signals) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside ⟨(GateLead.north kind n).cells (Chain.corner n i),boxes kind n hn a c⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(GateLead.north kind n).cells (Chain.corner n i),boxes kind n hn a c⟩)
      (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.north kind n).trans e
  let xs := (northExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hfs : fs ⊆ Chain.allNeighbors n :=
    fixed_inside _ _ _ (GateLead.north_fixed_allNeighbors kind n hn a c) hc
  have hh := Chain.corners_placed_allNeighbors n hn (Chain.uniform n c.upper) i fs
    hfs z f.north
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.1
  simp only [Chain.state,State.place,z,xs,place_north] at hh
  have hg := f.north_hubs_all hc a c
  exact ⟨hg.1.trans hh.1,hh.2.trans hg.2⟩

include f in
/-- Actual gate and lead hubs connect in all independently fixed phases. -/
private theorem east_hubs_all
    (hc : fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.allNeighbors n) (a c : Gates.Signals) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c)) (e.extend outside (atEast kind n hn a c)) ∧
    Reachable B (some 1) (e.extend outside (atEast kind n hn a c)) (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.east kind n).trans e
  let xs := (eastExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hfs : fs ⊆ Chain.allNeighbors n :=
    fixed_inside _ _ _ (GateLead.east_fixed_allNeighbors kind n hn a c) hc
  have hh := Chain.corners_placed_allNeighbors n hn (Chain.uniform n (!c.right)) 0 fs
    hfs z f.east
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.2
  simp only [Chain.state,State.place,z,xs,place_east] at hh
  have hg := f.gate_bridge a c 2
  rw [east_bridge] at hg
  exact ⟨hg.1.trans hh.2,hh.1.trans hg.2⟩

include f in
/-- Every real lead corner is accessible with all owned and foreign box phases fixed. -/
theorem east_corners
    (hc : fixed ((GateLead.east kind n).trans e) outside ⊆ Chain.allNeighbors n) (a c : Gates.Signals) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state kind n hn a c))
      (e.extend outside ⟨(GateLead.east kind n).cells (Chain.corner n i),boxes kind n hn a c⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(GateLead.east kind n).cells (Chain.corner n i),boxes kind n hn a c⟩)
      (e.extend outside (state kind n hn a c)) := by
  let z := (GateLead.east kind n).trans e
  let xs := (eastExternal kind n hn a c).map e.cells∪outside
  let fs := fixed z xs
  have hfs : fs ⊆ Chain.allNeighbors n :=
    fixed_inside _ _ _ (GateLead.east_fixed_allNeighbors kind n hn a c) hc
  have hh := Chain.corners_placed_allNeighbors n hn (Chain.uniform n (!c.right)) i fs
    hfs z f.east
    (fun p hp => (mem_fixed _ _ p).mpr hp) (fun p hp => (mem_fixed _ _ p).mp hp) (f.external_floor a c).2.2
  simp only [Chain.state,State.place,z,xs,place_east] at hh
  have hg := f.east_hubs_all hc a c
  exact ⟨hg.1.trans hh.1,hh.2.trans hg.2⟩

end ThinShell
end PushPuzzle.PushFS.Reduction.GateLead
