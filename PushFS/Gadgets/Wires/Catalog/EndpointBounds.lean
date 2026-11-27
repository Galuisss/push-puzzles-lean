/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Endpoints
public import PushFS.Gadgets.Wires.Catalog.InOrder

/-! Exact physical identity classification in the five-column collars of complete canonical trains. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem near_sparse {w h : ℕ} (a : Bool) (p q : PushFS.Cell w h)
    (hlo : 2+a.toNat≤p.1.val) (hhi : p.1.val<5) (hq : q.1.val=2+a.toNat)
    (hy : q.2=p.2) (hno : ¬Adjacent .east q p) :
    p.1.val=2+a.toNat ∨a=false ∧p.1.val=4 := by
  have hgap : p.1.val≠q.1.val+1 := by
    intro he
    exact hno ⟨he,hy.symm⟩
  cases a <;> simp_all <;> omega

private theorem far_sparse {w h : ℕ} (span : ℕ) (a : Bool) (p q : PushFS.Cell w h)
    (hlo : span≤p.1.val) (hhi : p.1.val≤span+a.toNat) (hq : q.1.val=span+a.toNat)
    (hy : p.2=q.2) (hno : ¬Adjacent .east p q) : p.1.val=span+a.toNat := by
  have ha : a.toNat≤1 := by cases a <;> decide
  have hgap : p.1.val+1≠q.1.val := fun he=>hno ⟨he.symm,hy.symm⟩
  omega

/-- The second real identity belongs to the first physical 40/59 block. -/
def chainSecond (n : ℕ) (hn : 2301≤n) : Chain.Label n :=
  ⟨Chain.firstBlock n hn,⟨1,by cases Chain.kind n (Chain.firstBlock n hn) <;> decide⟩⟩

theorem chain_second_x (n : ℕ) (hn : 2301≤n) (a : Bool) :
    (Chain.position n hn (Chain.uniform n a) (chainSecond n hn)).1.val=4+a.toNat := by
  change Chain.offset n (Chain.firstBlock n hn).val+
    (Chain.Tile.position (Chain.kind n (Chain.firstBlock n hn)) a ⟨1,_⟩).1.val=4+a.toNat
  rw [Chain.first_offset]
  have check : ∀(kind a : Bool),
      (Chain.Tile.position kind a ⟨1,by cases kind <;> decide⟩).1.val=4+a.toNat := by decide +kernel
  simpa only [Nat.zero_add] using check (Chain.kind n (Chain.firstBlock n hn)) a

theorem chain_near_x (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Chain.Label n)
    (hx : (Chain.position n hn (Chain.uniform n a) l).1.val<5) :
    (Chain.position n hn (Chain.uniform n a) l).1.val=2+a.toNat ∨
      a=false ∧(Chain.position n hn (Chain.uniform n a) l).1.val=4 := by
  apply near_sparse a _ _ (Polyline.chain_phase_bounds n hn a l).1 hx (Polyline.ChainEnds.first_x n hn a)
  · exact Fin.ext ((Chain.position_row n hn _ _).trans (Chain.position_row n hn _ _).symm)
  · exact Chain.sparse_targets n hn a (Polyline.ChainEnds.first n hn) l .east

theorem chain_far_x (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Chain.Label n)
    (hx : n≤(Chain.position n hn (Chain.uniform n a) l).1.val) :
    (Chain.position n hn (Chain.uniform n a) l).1.val=n+a.toNat := by
  apply far_sparse n a _ _ hx (Polyline.chain_phase_bounds n hn a l).2 (Polyline.ChainEnds.last_x n hn a)
  · exact Fin.ext ((Chain.position_row n hn _ _).trans (Chain.position_row n hn _ _).symm)
  · exact Chain.sparse_targets n hn a l (Polyline.ChainEnds.last n hn) .east

def flippedSecond (n : ℕ) (hn : 2301≤n) : FlippedChain.Label n := ⟨0,chainSecond n hn⟩

theorem flipped_second_x (n : ℕ) (hn : 2301≤n) (a : Bool) :
    (FlippedChain.position n hn a (flippedSecond n hn)).1.val=4+a.toNat := by
  change (FlippedChain.position n hn a ⟨0,chainSecond n hn⟩).1.val=_
  rw [FlippedChain.position0,FlippedChain.chain_x,chain_second_x]

theorem flipped_near_x (n : ℕ) (hn : 2301≤n) (a : Bool) (l : FlippedChain.Label n)
    (hx : (FlippedChain.position n hn a l).1.val<5) :
    (FlippedChain.position n hn a l).1.val=2+a.toNat ∨a=false ∧(FlippedChain.position n hn a l).1.val=4 := by
  apply near_sparse a _ _ (FlippedChain.position_bounds n hn a l).1 hx (FlippedChain.endpoints n hn a).1
  · exact Fin.ext ((FlippedChain.position_row n hn _ _).trans (FlippedChain.position_row n hn _ _).symm)
  · exact Tail.sparse_targets n hn a (FlippedChain.firstLabel n hn) l .east

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
