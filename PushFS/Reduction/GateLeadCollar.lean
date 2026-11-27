/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLead
public import PushFS.Gadgets.Gates.Slots

/-! Actual box occupancy in both directions across the gate/long-chain collars. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires Gadgets.Wires.Polyline

set_option maxRecDepth 65536

set_option maxRecDepth 65536 in
private theorem tile_near_checked : ∀ (kind phase : Bool) (i : Fin (Chain.Tile.count kind)),
    (Chain.Tile.position kind phase i).1.val≤3 →
      (Chain.Tile.position kind phase i).1.val=2+phase.toNat := by
  decide +kernel

/-- Only the real first box of a uniform chain can occupy its first four columns. -/
private theorem chain_near (n : ℕ) (hn : 2301≤n) (a : Bool) {p : Chain.C n}
    (hp : p ∈ Chain.boxes n hn (Chain.uniform n a)) (hx : p.1.val≤3) :
    p.1.val=2+a.toNat ∧ p.2.val=10 := by
  have hy := Chain.boxes_row n hn _ hp
  rw [Chain.boxes_image] at hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  have hb := Chain.Tile.position_bounds (Chain.kind n l.1) a l.2
  have hg := Chain.offset_gap n 0 l.1.val (Nat.zero_le _)
  have hz : Chain.offset n 0=0 := Chain.Spans.offset_zero n
  rw [hz] at hg
  simp only [Nat.sub_zero,Nat.zero_add] at hg
  change Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) a l.2).1.val≤3 at hx
  have hi : l.1.val=0 := by omega
  have hh := tile_near_checked (Chain.kind n l.1) a l.2 (by omega)
  change Chain.offset n l.1.val+(Chain.Tile.position (Chain.kind n l.1) a l.2).1.val=2+a.toNat ∧ _
  rw [hi,hz,hh,Nat.zero_add]
  exact ⟨rfl,hy⟩

private theorem west_boundary_member (kind : Bool) (a : Gates.Signals) (q : Gates.C)
    (hy : q.2.val=if kind then 29 else 90)
    (hx : q.1.val+(2+a.left.toNat)=(if kind then 2 else 3)) :
    q ∈ Gates.boundaryNeighbors kind a := by
  cases kind with
  | false =>
    have heq : q=(if a.left then 0 else 1,90) := by
      apply Prod.ext <;> apply Fin.ext
      · cases hh : a.left <;> simp [hh] at hx ⊢ <;> omega
      · exact hy
    rw [heq]
    simp [Gates.boundaryNeighbors]
  | true =>
    cases hh : a.left with
    | false =>
      have heq : q=(0,29) := by
        apply Prod.ext <;> apply Fin.ext
        · simp [hh] at hx ⊢
          omega
        · exact hy
      rw [heq]
      simp [Gates.boundaryNeighbors,hh]
    | true =>
      simp [hh] at hx

private theorem north_boundary_member (kind : Bool) (a : Gates.Signals) (q : Gates.C)
    (hx : q.1.val=if kind then 43 else 44) (hy : q.2.val+(2+a.upper.toNat)=3) :
    q ∈ Gates.boundaryNeighbors kind a := by
  have heq : q=(if kind then 43 else 44,if a.upper then 0 else 1) := by
    apply Prod.ext <;> apply Fin.ext
    · cases kind <;> simpa using hx
    · cases hh : a.upper <;> simp [hh] at hy ⊢ <;> omega
  rw [heq]
  cases kind <;> simp [Gates.boundaryNeighbors]

private theorem east_boundary_member (kind : Bool) (a : Gates.Signals) (q : Gates.C)
    (hy : q.2.val=90) (hx : q.1.val=(if kind then 78 else 77)+(2+(!a.right).toNat)) :
    q ∈ Gates.boundaryNeighbors kind a := by
  cases kind with
  | false =>
    have heq : q=(if a.right then 79 else 80,90) := by
      apply Prod.ext <;> apply Fin.ext
      · cases hh : a.right <;> simp [hh] at hx ⊢ <;> omega
      · exact hy
    rw [heq]
    simp [Gates.boundaryNeighbors]
  | true =>
    cases hh : a.right with
    | false =>
      have hq := q.1.isLt
      simp [hh] at hx
      omega
    | true =>
      have heq : q=(80,90) := by
        apply Prod.ext <;> apply Fin.ext
        · simp [hh] at hx ⊢
          omega
        · exact hy
      rw [heq]
      simp [Gates.boundaryNeighbors,hh]

/-- Every actual west-chain box visible to the gate is its checked boundary neighbor. -/
theorem west_box_neighbor (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (p : Chain.C n) (q : Gates.C)
    (hp : p ∈ Chain.boxes n hn (Chain.uniform n a.left))
    (he : (west kind n).cells p=(gate n).cells q) :
    q ∈ Gates.boundaryNeighbors kind a := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [west_x,west_y,gate_x,gate_y] at hx hy
  have hpB := p.1.isLt
  have hl : p.1.val≤3 := by cases kind <;> simp_all <;> omega
  have hp' := chain_near n hn a.left hp hl
  apply west_boundary_member kind a q
  · cases kind <;> simp_all <;> omega
  · cases kind <;> simp_all <;> omega

/-- The real one-cell north offset produces exactly the checked gate neighbor. -/
theorem north_box_neighbor (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (p : Chain.C n) (q : Gates.C)
    (hp : p ∈ Chain.boxes n hn (Chain.uniform n a.upper))
    (he : (north kind n).cells p=(gate n).cells q) :
    q ∈ Gates.boundaryNeighbors kind a := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [north_x,north_y,gate_x,gate_y] at hx hy
  have hpB := p.1.isLt
  have hl : p.1.val≤3 := by omega
  have hp' := chain_near n hn a.upper hp hl
  apply north_boundary_member kind a q
  · cases kind <;> simp_all <;> omega
  · omega

/-- The right flag's outward convention supplies the actual east-chain neighbor. -/
theorem east_box_neighbor (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (p : Chain.C n) (q : Gates.C)
    (hp : p ∈ Chain.boxes n hn (Chain.uniform n (!a.right)))
    (he : (east kind n).cells p=(gate n).cells q) :
    q ∈ Gates.boundaryNeighbors kind a := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [east_x,east_y,gate_x,gate_y] at hx hy
  have hqB := q.1.isLt
  have hl : p.1.val≤3 := by cases kind <;> simp_all <;> omega
  have hp' := chain_near n hn (!a.right) hp hl
  apply east_boundary_member kind a q
  · omega
  · cases kind <;> simp_all <;> omega

end PushPuzzle.PushFS.Reduction.GateLead
