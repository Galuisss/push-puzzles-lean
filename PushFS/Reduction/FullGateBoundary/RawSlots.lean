/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.EndWalls
public import PushFS.Reduction.AnnulusLineEndpoints

/-! The two actual far-end physical identities of every canonical long chain. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def chainPenultimate (n : ℕ) (hn : 2301≤n) : Chain.Label n :=
  ⟨Chain.lastBlock n hn,⟨Chain.Tile.count (Chain.kind n (Chain.lastBlock n hn))-2,
    by cases Chain.kind n (Chain.lastBlock n hn) <;> decide⟩⟩

theorem chain_penultimate_x (n : ℕ) (hn : 2301≤n) (a : Bool) :
    (Chain.position n hn (Chain.uniform n a) (chainPenultimate n hn)).1.val=n-2+a.toNat := by
  have h : ∀(k a : Bool),
      (Chain.Tile.position k a ⟨Chain.Tile.count k-2,by cases k <;> decide⟩).1.val+2=
        Chain.Tile.span k+a.toNat := by decide +kernel
  have hs:=h (Chain.kind n (Chain.lastBlock n hn)) a
  have hf:=Chain.last_finish n hn
  change Chain.offset n (Chain.lastBlock n hn).val+
    (Chain.Tile.position (Chain.kind n (Chain.lastBlock n hn)) a ⟨_,_⟩).1.val=n-2+a.toNat
  omega

/-- Complete canonical identities within two cells of the final false-phase box position. -/
private theorem chain_far_two (n : ℕ) (hn : 2301≤n) (a : Bool) (l : Chain.Label n)
    (hx : n≤(Chain.position n hn (Chain.uniform n a) l).1.val+2) :
    l=Polyline.ChainEnds.last n hn ∨l=chainPenultimate n hn := by
  let p:=Chain.position n hn (Chain.uniform n a) l
  let q:=Chain.position n hn (Chain.uniform n a) (Polyline.ChainEnds.last n hn)
  let r:=Chain.position n hn (Chain.uniform n a) (chainPenultimate n hn)
  have hq : q.1.val=n+a.toNat := Polyline.ChainEnds.last_x n hn a
  have hr : r.1.val=n-2+a.toNat := chain_penultimate_x n hn a
  have hb:= (Polyline.chain_phase_bounds n hn a l).2
  have hnoq : p.1.val+1≠q.1.val := by
    intro he
    apply Chain.sparse_targets n hn a l (Polyline.ChainEnds.last n hn) .east
    exact ⟨he.symm,Fin.ext ((Chain.position_row n hn _ _).trans (Chain.position_row n hn _ _).symm)⟩
  have hnor : p.1.val+1≠r.1.val := by
    intro he
    apply Chain.sparse_targets n hn a l (chainPenultimate n hn) .east
    exact ⟨he.symm,Fin.ext ((Chain.position_row n hn _ _).trans (Chain.position_row n hn _ _).symm)⟩
  have he : p.1.val=q.1.val ∨p.1.val=r.1.val := by
    change n≤p.1.val+2 at hx
    change p.1.val≤n+a.toNat at hb
    cases a <;> simp_all <;> omega
  have unique (i : Chain.Label n)
      (hi : p.1.val=(Chain.position n hn (Chain.uniform n a) i).1.val) : l=i := by
    apply Chain.position_injective n hn (Chain.uniform n a)
    apply Prod.ext
    · exact Fin.ext hi
    · exact Fin.ext ((Chain.position_row n hn _ _).trans (Chain.position_row n hn _ _).symm)
  exact he.elim (fun h=>Or.inl (unique _ h)) (fun h=>Or.inr (unique _ h))

def endpointPoint : Direction→Bool→Bool→Bool→ℕ×ℕ
  | .west,inc,a,prev => (5-inc.toNat-a.toNat+(if prev then 2 else 0),99034)
  | .east,inc,a,prev => (200001+inc.toNat+a.toNat-(if prev then 2 else 0),99034)
  | .north,inc,a,prev => (100003,5-inc.toNat-a.toNat+(if prev then 2 else 0))
  | .south,inc,a,prev => (100003,198062+inc.toNat+a.toNat-(if prev then 2 else 0))

theorem endpoint_frame (d : Direction) (inc a prev : Bool) :
    InFrame d (endpointPoint d inc a prev) ↔prev=false ∨inc=true ∨a=true := by
  cases d <;> cases inc <;> cases a <;> cases prev <;> decide

theorem normal_endpoint_coordinates (d : Direction) (inc a prev : Bool) (n : ℕ) (hn : 2301≤n)
    (dx dy : ℕ) (hd : EndPlacement d inc n dx dy) (q : Chain.C n)
    (hx : q.1.val=n-(if prev then 2 else 0)+a.toNat) (hy : q.2.val=10) :
    (lineOrientation d false).coordinates (n+5) 21 dx dy q=endpointPoint d inc a prev := by
  rw [RectOrientation.coordinates_point]
  have hb : inc.toNat≤1 := by cases inc <;> decide
  have ha : a.toNat≤1 := by cases a <;> decide
  cases d <;> cases prev <;>
    simp only [lineOrientation,RectOrientation.point,RectOrientation.width,RectOrientation.height,
      Bool.not_false,Bool.false_eq_true,reduceIte,endpointPoint,Nat.sub_zero] at hd hx ⊢ <;>
    dsimp only [EndPlacement] at hd <;> apply Prod.ext <;> dsimp only <;> omega

/-- Every actual canonical slot in the seven-cell outer frame is the last or penultimate identity. -/
theorem normal_slot_frame (d : Direction) (inc : Bool) (n : ℕ) (hn : 2301≤n) (a : Bool)
    (dx dy : ℕ) (hd : EndPlacement d inc n dx dy) (l : Chain.Label n) (p : ℕ×ℕ)
    (he : (lineOrientation d false).coordinates (n+5) 21 dx dy (Chain.position n hn (Chain.uniform n a) l)=p)
    (hf : InFrame d p) :
    (l=Polyline.ChainEnds.last n hn ∧p=endpointPoint d inc a false) ∨
      ((inc=true ∨a=true) ∧l=chainPenultimate n hn ∧p=endpointPoint d inc a true) := by
  have hh:=he
  rw [RectOrientation.coordinates_point] at hh
  have hx:=congrArg Prod.fst hh
  have hy:=congrArg Prod.snd hh
  have hb : inc.toNat≤1 := by cases inc <;> decide
  have hclose : n≤(Chain.position n hn (Chain.uniform n a) l).1.val+2 := by
    cases d <;>
      simp only [lineOrientation,RectOrientation.point,RectOrientation.width,RectOrientation.height,
        Bool.not_false,Bool.false_eq_true,reduceIte,EndPlacement,InFrame] at hd hf hx hy <;> omega
  rcases chain_far_two n hn a l hclose with rfl|rfl
  · exact Or.inl ⟨rfl,he.symm.trans (normal_endpoint_coordinates d inc a false n hn dx dy hd _
      (Polyline.ChainEnds.last_x n hn a) (Chain.position_row n hn _ _))⟩
  · have hp:=he.symm.trans (normal_endpoint_coordinates d inc a true n hn dx dy hd _
      (chain_penultimate_x n hn a) (Chain.position_row n hn _ _))
    rw [hp,endpoint_frame] at hf
    exact Or.inr ⟨hf.resolve_left (by decide),rfl,hp⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
