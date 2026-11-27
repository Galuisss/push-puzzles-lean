/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadPieces

/-! The complete legal storage instance of the gate and all three real long leads. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

set_option maxHeartbeats 0 in
private theorem position_not_boundary_checked : ∀ (kind a b c : Bool) (i : Fin (Gates.slots kind).length),
    Gates.position kind ⟨a,b,c⟩ i ∉ Gates.boundaryNeighbors kind ⟨a,b,c⟩ := by
  decide +kernel

private theorem chain_position_mem (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Chain.Label n) :
    Chain.position n hn (Chain.uniform n a) l ∈ Chain.boxes n hn (Chain.uniform n a) := by
  rw [Chain.boxes_image]
  exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩

private theorem position_ne01 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (l : Labels kind n 0) (k : Labels kind n 1) : position kind n hn a 0 l ≠ position kind n hn a 1 k := by
  intro he
  have hh := west_box_neighbor kind n hn a _ _ (chain_position_mem n hn a.left k) he.symm
  exact position_not_boundary_checked kind a.left a.upper a.right l hh

private theorem position_ne02 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (l : Labels kind n 0) (k : Labels kind n 2) : position kind n hn a 0 l ≠ position kind n hn a 2 k := by
  intro he
  have hh := north_box_neighbor kind n hn a _ _ (chain_position_mem n hn a.upper k) he.symm
  exact position_not_boundary_checked kind a.left a.upper a.right l hh

private theorem position_ne03 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (l : Labels kind n 0) (k : Labels kind n 3) : position kind n hn a 0 l ≠ position kind n hn a 3 k := by
  intro he
  have hh := east_box_neighbor kind n hn a _ _ (chain_position_mem n hn (!a.right) k) he.symm
  exact position_not_boundary_checked kind a.left a.upper a.right l hh

/-- Every actual physical slot has one glyph owner, for every canonical flag assignment. -/
theorem position_owners (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals)
    (i j : Fin 4) (l : Labels kind n i) (k : Labels kind n j)
    (he : position kind n hn a i l=position kind n hn a j k) : i=j := by
  by_cases hij : i=j
  · exact hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact False.elim (position_ne01 kind n hn a l k he)
  · exact False.elim (position_ne02 kind n hn a l k he)
  · exact False.elim (position_ne03 kind n hn a l k he)
  · exact False.elim (position_ne01 kind n hn a k l he.symm)
  · exact False.elim (hij rfl)
  · exact False.elim (west_ne_north kind n _ _ he)
  · exact False.elim (west_ne_east kind n _ _ he)
  · exact False.elim (position_ne02 kind n hn a k l he.symm)
  · exact False.elim (west_ne_north kind n _ _ he.symm)
  · exact False.elim (hij rfl)
  · exact False.elim (north_ne_east kind n _ _ he)
  · exact False.elim (position_ne03 kind n hn a k l he.symm)
  · exact False.elim (west_ne_east kind n _ _ he.symm)
  · exact False.elim (north_ne_east kind n _ _ he.symm)
  · exact False.elim (hij rfl)

def player (n : ℕ) : C n := (gate n).cells Gates.hub

private theorem player_outside (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) (hi : i≠0) (p : Cell (piece kind n hn a b i).width (piece kind n hn a b i).height) :
    player n ≠ (placement kind n hn a b i).cells p := by
  fin_cases i
  · exact False.elim (hi rfl)
  · intro he
    have hx := congrArg (fun p : C n => p.1.val) he
    have hp : p.1.val<n+5 := p.1.isLt
    change n+10+40=(if kind then 8 else 9)+p.1.val at hx
    cases kind <;> simp at hx <;> omega
  · intro he
    have hy := congrArg (fun p : C n => p.2.val) he
    have hp : p.2.val<n+5 := p.2.isLt
    change n+20+82=19+p.2.val at hy
    omega
  · intro he
    have hx := congrArg (fun p : C n => p.1.val) he
    change n+10+40=n+(if kind then 88 else 87)+p.1.val at hx
    cases kind <;> simp at hx <;> omega

theorem player_floor (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) (p : Cell (piece kind n hn a b i).width (piece kind n hn a b i).height)
    (hp : p ∈ (piece kind n hn a b i).board.walls) :
    ((player n).1.val,(player n).2.val) ≠ (dx kind n i+p.1.val,dy kind n i+p.2.val) := by
  intro he
  have he' : player n=(placement kind n hn a b i).cells p := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  by_cases hi : i=0
  · subst i
    have hp' : Gates.hub=p := (gate n).cells.injective he'
    cases hp'
    exact (Gates.canonical_valid kind a ∅).1 hp
  · exact player_outside kind n hn a b i hi p he'

theorem player_empty (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) (l : Labels kind n i) :
    ((player n).1.val,(player n).2.val) ≠
      (dx kind n i+((matching kind n hn a b i).source l).1.val,
       dy kind n i+((matching kind n hn a b i).source l).2.val) := by
  intro he
  have he' : player n=(placement kind n hn a b i).cells ((matching kind n hn a b i).source l) := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  by_cases hi : i=0
  · subst i
    rw [source_position] at he'
    have hh : Gates.hub=Gates.position kind a l := (gate n).cells.injective he'
    have hb : Gates.position kind a l ∈ Gates.canonicalBoxes kind a := by
      rw [← Gates.position_image]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
    have hb' : Gates.hub ∈ Gates.canonicalBoxes kind a := hh.symm ▸ hb
    exact (Gates.canonical_valid kind a ∅).2.2 hb'
  · exact player_outside kind n hn a b i hi _ he'

/-- A complete physical gate with all three long arms and every owned auxiliary box and target. -/
def atlas (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) :
    StorageAtlas 4 (2*n+101) (2*n+137) (Labels kind n) where
  piece := piece kind n hn a b
  matching := matching kind n hn a b
  dx := dx kind n
  dy := dy kind n
  fitsX := fitsX kind n hn a b
  fitsY := fitsY kind n hn a b
  walls_compatible := walls_compatible kind n hn a b
  source_owners := by
    intro i j l k he
    apply position_owners kind n hn a i j l k
    rw [← source_position kind n hn a b i,← source_position kind n hn a b j]
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  target_owners := by
    intro i j l k he
    apply position_owners kind n hn b i j l k
    rw [← target_position kind n hn a b i,← target_position kind n hn a b j]
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  player := player n
  player_floor := player_floor kind n hn a b
  player_empty := player_empty kind n hn a b

end PushPuzzle.PushFS.Reduction.GateLead
