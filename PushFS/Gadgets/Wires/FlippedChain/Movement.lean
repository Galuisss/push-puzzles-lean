/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Statics
public import PushFS.Gadgets.Wires.Polyline.Transport

/-! Real full physical macros of the long train and terminal SingleFlip, with exact visible collars. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (n : ℕ) (hn : 2301≤n)

def neighbors : Finset (C n) := {(⟨0,by clear hn; omega⟩,10),(⟨n+23,by clear hn; omega⟩,10)}
def allNeighbors : Finset (C n) := {(⟨0,by clear hn; omega⟩,10),(⟨1,by clear hn; omega⟩,10),
  (⟨n+22,by clear hn; omega⟩,10),(⟨n+23,by clear hn; omega⟩,10),(⟨n+24,by clear hn; omega⟩,10)}

private theorem neighbors_row {p : C n} (hp : p∈neighbors n) : p.2.val=10 := by
  simp only [neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl <;> rfl

private theorem neighbors_floor : Disjoint (neighbors n) (walls n hn) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  have hy:=neighbors_row n hp
  have hh:=walls_rows n hn hw
  omega

namespace Frame

variable (fixed : Finset (C n)) (hf : fixed⊆neighbors n)

def state (a : Phases) : State (n+25) 21 := Gates.withFixed fixed (FlippedChain.state n hn a)
private def atFlip (a : Phases) : State
    (n+25) 21 := ⟨(flipPlacement n).cells Flip.hub,boxes n hn a∪fixed⟩
def chainExternal (a : Phases) : Finset (C n) := flipBoxes n a.2∪fixed
def flipExternal (a : Phases) : Finset (C n) := chainBoxes n hn a.1∪fixed
def chainFixed (a : Phases) : Finset (Chain.C n) := Finset.univ.filter fun p=>(chainPlacement n).cells p∈chainExternal n fixed a
def flipFixed (a : Phases) : Finset Flip.C := Finset.univ.filter fun p=>(flipPlacement n).cells p∈flipExternal n hn fixed a

@[simp] theorem mem_chainFixed (a : Phases) (p : Chain.C n) :
    p∈chainFixed n fixed a ↔ (chainPlacement n).cells p∈chainExternal n fixed a := by simp [chainFixed]
@[simp] theorem mem_flipFixed (a : Phases) (p : Flip.C) :
    p∈flipFixed n hn fixed a ↔ (flipPlacement n).cells p∈flipExternal n hn fixed a := by simp [flipFixed]

include hf in
private theorem external_floor (goals : Finset (C n)) (a : Phases) :
    Disjoint (chainExternal n fixed a) (board n hn goals).walls ∧
    Disjoint (flipExternal n hn fixed a) (board n hn goals).walls := by
  have hh:=Finset.disjoint_union_left.mp (boxes_floor n hn a goals)
  have hfix:=(neighbors_floor n hn).mono_left hf
  exact ⟨Finset.disjoint_union_left.mpr ⟨hh.2,hfix⟩,Finset.disjoint_union_left.mpr ⟨hh.1,hfix⟩⟩

include hf in
private theorem chainFixed_neighbors (a : Phases)
    (ha : a.2=true) : chainFixed n fixed a⊆Chain.neighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_chainFixed n fixed a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hq
    have hx:=congrArg (fun p : C n=>p.1.val) he
    have hy:=congrArg (fun p : C n=>p.2.val) he
    rw [flip_x,chain_x,ha] at hx
    rw [flip_y,chain_y,ha] at hy
    have check : ∀i : Fin 9, (Flip.template.position true i).1.val<5 → Flip.template.position true i=(3,10) := by decide +kernel
    have heq:=check i (by have := p.1.isLt; omega)
    rw [heq] at hx hy
    change n+3=p.1.val at hx
    change 10=p.2.val at hy
    have hpEq : p=(⟨n+3,by omega⟩,10) := Prod.ext (Fin.ext (by change p.1.val=n+3; omega)) (Fin.ext (by change p.2.val=10; exact hy.symm))
    rw [hpEq]
    simp [Chain.neighbors]
  · have hp:=hf hp
    simp only [neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with hp|hp
    · have hx:=congrArg (fun p : C n=>p.1.val) hp
      have hy:=congrArg (fun p : C n=>p.2.val) hp
      rw [chain_x] at hx
      rw [chain_y] at hy
      have heq : p=(0,10) := Prod.ext (Fin.ext hx) (Fin.ext hy)
      rw [heq]
      simp [Chain.neighbors]
    · have hx:=congrArg (fun p : C n=>p.1.val) hp
      rw [chain_x] at hx
      have := p.1.isLt
      change p.1.val=n+23 at hx
      omega

include hf in
private theorem flipFixed_neighbors (a : Phases)
    (ha : a.1=false) : flipFixed n hn fixed a⊆Flip.template.neighbors := by
  intro p hp
  rcases Finset.mem_union.mp ((mem_flipFixed n hn fixed a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
    rw [ha,Chain.boxes_image] at hq
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hq
    have hx:=congrArg (fun p : C n=>p.1.val) he
    have hy:=congrArg (fun p : C n=>p.2.val) he
    rw [chain_x,flip_x] at hx
    rw [chain_y,flip_y,Chain.position_row] at hy
    have hh:=Polyline.chain_phase_bounds n hn false i
    have heq : p=(0,10) := by
      apply Prod.ext <;> apply Fin.ext
      · change p.1.val=0
        simp only [Bool.toNat_false] at hh
        omega
      · change p.2.val=10
        exact hy.symm
    rw [heq]
    simp [Flip.template,Flip.neighbors]
  · have hp:=hf hp
    simp only [neighbors,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with hp|hp
    · have hx:=congrArg (fun p : C n=>p.1.val) hp
      rw [flip_x] at hx
      change n+p.1.val=0 at hx
      omega
    · have hx:=congrArg (fun p : C n=>p.1.val) hp
      have hy:=congrArg (fun p : C n=>p.2.val) hp
      rw [flip_x] at hx
      rw [flip_y] at hy
      have heq : p=(23,10) := Prod.ext (Fin.ext (by change p.1.val=23; change n+p.1.val=n+23 at hx; omega)) (Fin.ext hy)
      rw [heq]
      simp [Flip.template,Flip.neighbors]

theorem place_chain (a : Phases) (p : Chain.C n) :
    (chainPlacement n).extend (chainExternal n fixed a) ⟨p,Chain.boxes n hn (Chain.uniform n a.1)⟩=
      ⟨(chainPlacement n).cells p,boxes n hn a∪fixed⟩ := by
  apply State.ext
  · rfl
  change chainBoxes n hn a.1∪(flipBoxes n a.2∪fixed)=(chainBoxes n hn a.1∪flipBoxes n a.2)∪fixed
  ac_rfl

theorem place_flip (a : Phases) (p : Flip.C) :
    (flipPlacement n).extend (flipExternal n hn fixed a) ⟨p,Flip.template.boxes a.2⟩=
      ⟨(flipPlacement n).cells p,boxes n hn a∪fixed⟩ := by
  apply State.ext
  · rfl
  change flipBoxes n a.2∪(chainBoxes n hn a.1∪fixed)=(chainBoxes n hn a.1∪flipBoxes n a.2)∪fixed
  ac_rfl

include hf in
private theorem walk_row (goals : Finset (C n)) (a : Phases) (p q : C n) (hp : p.2.val=3)
    (hq : q.2.val=3) :
    Reachable (board n hn goals) (some 1) ⟨p,boxes n hn a∪fixed⟩ ⟨q,boxes n hn a∪fixed⟩ := by
  have hp' : p=(p.1,3) := Prod.ext rfl (Fin.ext hp)
  have hq' : q=(q.1,3) := Prod.ext rfl (Fin.ext hq)
  rw [hp',hq']
  apply walk_horizontal (Finset.disjoint_union_left.mpr ⟨boxes_floor n hn a goals,(neighbors_floor n hn).mono_left hf⟩)
  intro x _ _
  constructor
  · intro hw
    have hh:=walls_rows n hn hw
    change 3=8∨3=9∨3=11∨3=12 at hh
    omega
  · intro hb
    rcases Finset.mem_union.mp hb with hb|hb
    · have hh:=boxes_row n hn a hb
      change 3=10 at hh
      contradiction
    · have hh:=neighbors_row n (hf hb)
      change 3=10 at hh
      contradiction

include hf in
private theorem update_chain (goals : Finset (C n)) (a b : Bool) :
    Reachable (board n hn goals) (some 1) (state n hn fixed (a,true)) (state n hn fixed (b,true)) := by
  have hh:=Chain.transition_placed n hn a b (chainFixed n fixed (a,true))
    (chainFixed_neighbors n fixed hf (a,true) rfl) (chainPlacement n) (chain_walls n hn goals)
    (fun p hp=>(mem_chainFixed n fixed (a,true) p).mpr hp) (fun p hp=>(mem_chainFixed n fixed (a,true) p).mp hp)
    (external_floor n hn fixed hf goals (a,true)).1
  simp only [State.place] at hh
  have hs : (chainPlacement n).extend (chainExternal n fixed (a,true)) (Chain.state n hn (Chain.uniform n a))=state n hn fixed (a,true) := place_chain n hn fixed (a,true) (Chain.hub n hn)
  have ht : (chainPlacement n).extend (chainExternal n fixed (a,true)) (Chain.state n hn (Chain.uniform n b))=state n hn fixed (b,true) := place_chain n hn fixed (b,true) (Chain.hub n hn)
  rw [hs,ht] at hh
  exact hh

include hf in
private theorem update_flip (goals : Finset (C n)) (a b : Bool) :
    Reachable (board n hn goals) (some 1) (state n hn fixed (false,a)) (state n hn fixed (false,b)) := by
  have hh:=(flipPlacement n).reachable_withFixed (flip_walls n hn goals)
    (fun p hp=>(mem_flipFixed n hn fixed (false,a) p).mpr hp) (fun p hp=>(mem_flipFixed n hn fixed (false,a) p).mp hp)
    (external_floor n hn fixed hf goals (false,a)).2
    (Flip.checked.transition a b ∅ (flipFixed n hn fixed (false,a)) (flipFixed_neighbors n hn fixed hf (false,a) rfl))
  have hs : (flipPlacement n).extend (flipExternal n hn fixed (false,a)) (Flip.template.state a)=atFlip n hn fixed (false,a) := place_flip n hn fixed (false,a) Flip.hub
  have ht : (flipPlacement n).extend (flipExternal n hn fixed (false,a)) (Flip.template.state b)=atFlip n hn fixed (false,b) := place_flip n hn fixed (false,b) Flip.hub
  rw [hs,ht] at hh
  exact (walk_row n hn fixed hf goals (false,a) (player n) ((flipPlacement n).cells Flip.hub) rfl rfl).trans
    (hh.trans (walk_row n hn fixed hf goals (false,b) ((flipPlacement n).cells Flip.hub) (player n) rfl rfl))

include hf in
/-- True first propagates through the terminal SingleFlip, then through the full train; reverse uses the inverse order. -/
theorem transition (goals : Finset (C n)) (a b : Bool) :
    Reachable (board n hn goals) (some 1) (state n hn fixed (uniform a)) (state n hn fixed (uniform b)) := by
  have hfwd:=(update_flip n hn fixed hf goals false true).trans (update_chain n hn fixed hf goals false true)
  have hback:=(update_chain n hn fixed hf goals true false).trans (update_flip n hn fixed hf goals true false)
  cases a <;> cases b
  · exact .refl
  · exact hfwd
  · exact hback
  · exact .refl

end Frame

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
