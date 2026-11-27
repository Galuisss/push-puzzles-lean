/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadCollar

/-! Real gate boxes provide the permitted fixed frame while any one lead updates. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires Gadgets.Wires.Polyline

set_option maxRecDepth 65536

theorem west_ne_north (kind : Bool) (n : ℕ) (p q : Chain.C n) :
    (west kind n).cells p ≠ (north kind n).cells q := by
  intro he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [west_y,north_y] at hy
  cases kind <;> simp_all <;> omega

theorem west_ne_east (kind : Bool) (n : ℕ) (p q : Chain.C n) :
    (west kind n).cells p ≠ (east kind n).cells q := by
  intro he
  have hx := congrArg (fun p : C n => p.1.val) he
  simp only [west_x,east_x] at hx
  cases kind <;> simp_all <;> omega

theorem north_ne_east (kind : Bool) (n : ℕ) (p q : Chain.C n) :
    (north kind n).cells p ≠ (east kind n).cells q := by
  intro he
  have hx := congrArg (fun p : C n => p.1.val) he
  simp only [north_x,east_x] at hx
  cases kind <;> simp_all <;> omega

set_option maxHeartbeats 0 in
private theorem west_low_checked : ∀ (kind b c : Bool) (i : Fin (Gates.slots kind).length),
    (Gates.position kind ⟨false,b,c⟩ i).1.val≤3 →
    (Gates.position kind ⟨false,b,c⟩ i).1.val=(if kind then 2 else 3) ∧
    (Gates.position kind ⟨false,b,c⟩ i).2.val=(if kind then 29 else 90) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem north_low_checked : ∀ (kind a c : Bool) (i : Fin (Gates.slots kind).length),
    (Gates.position kind ⟨a,false,c⟩ i).2.val≤3 →
    (Gates.position kind ⟨a,false,c⟩ i).1.val=(if kind then 43 else 44) ∧
    (Gates.position kind ⟨a,false,c⟩ i).2.val=3 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem east_high_checked : ∀ (kind a b : Bool) (i : Fin (Gates.slots kind).length),
    77≤(Gates.position kind ⟨a,b,true⟩ i).1.val →
    (Gates.position kind ⟨a,b,true⟩ i).1.val=(if kind then 78 else 77) ∧
    (Gates.position kind ⟨a,b,true⟩ i).2.val=90 := by
  decide +kernel

private theorem gate_west_low (kind : Bool) (a : Gates.Signals) {q : Gates.C}
    (ha : a.left=false) (hq : q ∈ Gates.canonicalBoxes kind a) (hx : q.1.val≤3) :
    q.1.val=(if kind then 2 else 3) ∧ q.2.val=(if kind then 29 else 90) := by
  rcases a with ⟨a,b,c⟩
  change a=false at ha
  subst a
  rw [← Gates.position_image] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  exact west_low_checked kind b c i hx

private theorem gate_north_low (kind : Bool) (a : Gates.Signals) {q : Gates.C}
    (ha : a.upper=false) (hq : q ∈ Gates.canonicalBoxes kind a) (hy : q.2.val≤3) :
    q.1.val=(if kind then 43 else 44) ∧ q.2.val=3 := by
  rcases a with ⟨a,b,c⟩
  change b=false at ha
  subst b
  rw [← Gates.position_image] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  exact north_low_checked kind a c i hy

private theorem gate_east_high (kind : Bool) (a : Gates.Signals) {q : Gates.C}
    (ha : a.right=true) (hq : q ∈ Gates.canonicalBoxes kind a) (hx : 77≤q.1.val) :
    q.1.val=(if kind then 78 else 77) ∧ q.2.val=90 := by
  rcases a with ⟨a,b,c⟩
  change c=true at ha
  subst c
  rw [← Gates.position_image] at hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  exact east_high_checked kind a b i hx

/-- With the left core flag released, its visible box is exactly the west chain's real neighbor. -/
theorem west_gate_neighbor (kind : Bool) (n : ℕ) (a : Gates.Signals) (ha : a.left=false)
    (p : Chain.C n) (q : Gates.C) (hq : q ∈ Gates.canonicalBoxes kind a)
    (he : (west kind n).cells p=(gate n).cells q) : p ∈ Chain.neighbors n := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [west_x,west_y,gate_x,gate_y] at hx hy
  have hp := p.1.isLt
  have hpy := p.2.isLt
  have hqx : q.1.val≤3 := by cases kind <;> simp_all <;> omega
  have hh := gate_west_low kind a ha hq hqx
  have heq : p=(⟨0,by omega⟩,10) := by
    have hpx : p.1.val=0 := by cases kind <;> simp at hx hy hh <;> omega
    have hpy' : p.2.val=10 := by cases kind <;> simp at hx hy hh <;> omega
    exact Prod.ext (Fin.ext hpx) (Fin.ext hpy')
  rw [heq]
  simp [Chain.neighbors]

/-- With the north core flag released, its visible box occupies the checked chain collar. -/
theorem north_gate_neighbor (kind : Bool) (n : ℕ) (a : Gates.Signals) (ha : a.upper=false)
    (p : Chain.C n) (q : Gates.C) (hq : q ∈ Gates.canonicalBoxes kind a)
    (he : (north kind n).cells p=(gate n).cells q) : p ∈ Chain.neighbors n := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [north_x,north_y,gate_x,gate_y] at hx hy
  have hp := p.1.isLt
  have hpy := p.2.isLt
  have hqy : q.2.val≤3 := by omega
  have hh := gate_north_low kind a ha hq hqy
  have heq : p=(⟨0,by omega⟩,10) := by
    have hpx : p.1.val=0 := by cases kind <;> simp at hx hy hh <;> omega
    have hpy' : p.2.val=10 := by cases kind <;> simp at hx hy hh <;> omega
    exact Prod.ext (Fin.ext hpx) (Fin.ext hpy')
  rw [heq]
  simp [Chain.neighbors]

/-- The outward right-flag convention releases the east-chain update at precisely `right=true`. -/
theorem east_gate_neighbor (kind : Bool) (n : ℕ) (a : Gates.Signals) (ha : a.right=true)
    (p : Chain.C n) (q : Gates.C) (hq : q ∈ Gates.canonicalBoxes kind a)
    (he : (east kind n).cells p=(gate n).cells q) : p ∈ Chain.neighbors n := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [east_x,east_y,gate_x,gate_y] at hx hy
  have hpy := p.2.isLt
  have hqx : 77≤q.1.val := by cases kind <;> simp_all <;> omega
  have hh := gate_east_high kind a ha hq hqx
  have heq : p=(⟨0,by omega⟩,10) := by
    have hpx : p.1.val=0 := by cases kind <;> simp at hx hy hh <;> omega
    have hpy' : p.2.val=10 := by cases kind <;> simp at hx hy hh <;> omega
    exact Prod.ext (Fin.ext hpx) (Fin.ext hpy')
  rw [heq]
  simp [Chain.neighbors]

end PushPuzzle.PushFS.Reduction.GateLead
