/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Geometry
public import PushFS.Reduction.StorageRaster

/-! Complete actual chain/terminal-flip source and target ownership and the full unlabelled storage instance. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


open Reduction
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

abbrev Phases := Bool×Bool
def uniform (a : Bool) : Phases := (a,a)
def Labels (n : ℕ) : Fin 2→Type := Fin.cases (Chain.Label n) (fun _ : Fin 1=>Fin 9)
instance (n : ℕ) : (i : Fin 2)→Fintype (Labels n i) :=
  Fin.cases (inferInstance : Fintype (Chain.Label n)) (fun _ : Fin 1=>inferInstanceAs (Fintype (Fin 9)))
abbrev Label (n : ℕ) := (i : Fin 2)×Labels n i

def piece (n : ℕ) (hn : 2301≤n) (a b : Phases) : Fin 2→Instance :=
  Fin.cases (Chain.puzzle n hn a.1 b.1) (fun _ : Fin 1=>Flip.checked.storageInstance a.2 b.2)
def matching (n : ℕ) (hn : 2301≤n) (a b : Phases) : (i : Fin 2)→SlotMatching (piece n hn a b i) (Labels n i) :=
  Fin.cases (Chain.slotMatching n hn a.1 b.1) (fun _ : Fin 1=>Flip.checked.slotMatching a.2 b.2)
def dx (n : ℕ) (i : Fin 2) : ℕ := if i=0 then 0 else n

theorem fitsX (n : ℕ) (hn : 2301≤n) (a b : Phases) (i : Fin 2) : dx n i+(piece n hn a b i).width≤n+25 := by
  fin_cases i
  · change 0+(n+5)≤n+25; omega
  · change n+25≤n+25; omega

theorem fitsY (n : ℕ) (hn : 2301≤n) (a b : Phases) (i : Fin 2) : 0+(piece n hn a b i).height≤21 := by
  fin_cases i <;> change 0+21≤21 <;> decide

theorem walls_compatible (n : ℕ) (hn : 2301≤n) (a b : Phases) (i j : Fin 2)
    (p : Cell (piece n hn a b i).width (piece n hn a b i).height)
    (q : Cell (piece n hn a b j).width (piece n hn a b j).height)
    (he : (dx n i+p.1.val,0+p.2.val)=(dx n j+q.1.val,0+q.2.val)) :
    p∈(piece n hn a b i).board.walls ↔ q∈(piece n hn a b j).board.walls := by
  by_cases hij : i=j
  · subst j
    have heq : p=q := by apply Prod.ext <;> apply Fin.ext <;> have hh:=congrArg Prod.fst he <;> have hh':=congrArg Prod.snd he <;> omega
    subst q
    rfl
  · fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · apply overlap_walls n hn p q
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    · apply (overlap_walls n hn q p _).symm
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst he.symm
      · exact congrArg Prod.snd he.symm
    · exact False.elim (hij rfl)

theorem source0_bounds (n : ℕ) (hn : 2301≤n) (a b : Phases) (l : Labels n 0) :
    ((matching n hn a b 0).source l).1.val≤n+1 ∧ ((matching n hn a b 0).source l).2.val=10 := by
  have hh:=Polyline.chain_phase_bounds n hn a.1 l
  have ha : a.1.toNat≤1 := by cases a.1 <;> decide
  change (Chain.position n hn (Chain.uniform n a.1) l).1.val≤n+1 ∧ _
  exact ⟨by omega,Chain.position_row n hn _ l⟩

theorem source1_bounds (n : ℕ) (hn : 2301≤n) (a b : Phases) (l : Labels n 1) :
    2≤((matching n hn a b 1).source l).1.val ∧ ((matching n hn a b 1).source l).2.val=10 := by
  have hh:=flip_bounds a.2 l
  change 2≤(Flip.template.position a.2 l).1.val ∧ _
  exact ⟨by omega,hh.1⟩

theorem source_owners (n : ℕ) (hn : 2301≤n) (a b : Phases) (i j : Fin 2) (l : Labels n i) (k : Labels n j)
    (he : (dx n i+((matching n hn a b i).source l).1.val,0+((matching n hn a b i).source l).2.val)=
      (dx n j+((matching n hn a b j).source k).1.val,0+((matching n hn a b j).source k).2.val)) : i=j := by
  have cases2 (i : Fin 2) : i=0∨i=1 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases2 i with rfl|rfl <;> rcases cases2 j with rfl|rfl
  · rfl
  · have hp:=source0_bounds n hn a b l
    have hq:=source1_bounds n hn a b k
    have hx:=congrArg Prod.fst he
    change 0+_=n+_ at hx
    omega
  · have hp:=source1_bounds n hn a b l
    have hq:=source0_bounds n hn a b k
    have hx:=congrArg Prod.fst he
    change n+_=0+_ at hx
    omega
  · rfl

theorem target_source (n : ℕ) (hn : 2301≤n) (a b : Phases) (i : Fin 2) (l : Labels n i) :
    (((matching n hn a b i).target l).1.val,((matching n hn a b i).target l).2.val)=
      (((matching n hn b a i).source l).1.val,((matching n hn b a i).source l).2.val) := by fin_cases i <;> rfl

def player (n : ℕ) : C n := (⟨20,by omega⟩,3)

def atlas (n : ℕ) (hn : 2301≤n) (a b : Phases) : StorageAtlas 2 (n+25) 21 (Labels n) where
  piece:=piece n hn a b
  matching:=matching n hn a b
  dx:=dx n
  dy:=fun _=>0
  fitsX:=fitsX n hn a b
  fitsY:=fitsY n hn a b
  walls_compatible:=walls_compatible n hn a b
  source_owners:=source_owners n hn a b
  target_owners:=by
    intro i j l k he
    have hi:=target_source n hn a b i l
    have hj:=target_source n hn a b j k
    apply source_owners n hn b a i j l k
    apply Prod.ext
    · have hx:=congrArg Prod.fst he
      have hix:=congrArg Prod.fst hi
      have hjx:=congrArg Prod.fst hj
      dsimp only at hx hix hjx ⊢
      omega
    · have hy:=congrArg Prod.snd he
      have hiy:=congrArg Prod.snd hi
      have hjy:=congrArg Prod.snd hj
      dsimp only at hy hiy hjy ⊢
      omega
  player:=player n
  player_floor:=by
    intro i p hp he
    have hy:=congrArg Prod.snd he
    fin_cases i
    · have hh:=Chain.walls_rows n hn p hp
      change 3=0+p.2.val at hy
      omega
    · have check : ∀p : Flip.C, Flip.wallTest p=true → p.2.val=8∨p.2.val=9∨p.2.val=11∨p.2.val=12 := by decide +kernel
      have hh:=check p ((Flip.template.mem_walls p).mp hp)
      change 3=0+p.2.val at hy
      omega
  player_empty:=by
    intro i l he
    have hy:=congrArg Prod.snd he
    fin_cases i
    · have hh:=source0_bounds n hn a b l
      change 3=0+((matching n hn a b 0).source l).2.val at hy
      omega
    · have hh:=source1_bounds n hn a b l
      change 3=0+((matching n hn a b 1).source l).2.val at hy
      omega

def chainBoxes (n : ℕ) (hn : 2301≤n) (a : Bool) : Finset (C n) :=
  (Chain.boxes n hn (Chain.uniform n a)).map (chainPlacement n).cells
def flipBoxes (n : ℕ) (a : Bool) : Finset (C n) := (Flip.template.boxes a).map (flipPlacement n).cells
def boxes (n : ℕ) (hn : 2301≤n) (a : Phases) : Finset (C n) := chainBoxes n hn a.1∪flipBoxes n a.2
def state (n : ℕ) (hn : 2301≤n) (a : Phases) : State (n+25) 21 := ⟨player n,boxes n hn a⟩

private theorem source0 (n : ℕ) (hn : 2301≤n) (a b : Phases) (l : Chain.Label n) :
    (atlas n hn a b).source ⟨0,l⟩=(chainPlacement n).cells (Chain.position n hn (Chain.uniform n a.1) l) := rfl
private theorem source1 (n : ℕ) (hn : 2301≤n) (a b : Phases) (l : Fin 9) :
    (atlas n hn a b).source ⟨1,l⟩=(flipPlacement n).cells (Flip.template.position a.2 l) := rfl

theorem initial_boxes (n : ℕ) (hn : 2301≤n) (a b : Phases) : (atlas n hn a b).initial.boxes=boxes n hn a := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩,_,rfl⟩:=Finset.mem_map.mp hp
    fin_cases i
    · apply Finset.mem_union_left
      apply Finset.mem_map.mpr
      refine ⟨_,?_,rfl⟩
      rw [Chain.boxes_image]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_,Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩,rfl⟩)
  · rintro hp
    rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      rw [Chain.boxes_image] at hq
      obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp hq
      exact Finset.mem_map.mpr ⟨⟨0,l⟩,Finset.mem_univ _,source0 n hn a b l⟩
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
      obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp hq
      exact Finset.mem_map.mpr ⟨⟨1,l⟩,Finset.mem_univ _,source1 n hn a b l⟩

theorem atlas_walls (n : ℕ) (hn : 2301≤n) (a b : Phases) : (atlas n hn a b).walls=walls n hn := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
    fin_cases i
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ hi
  · intro hp
    rcases Finset.mem_union.mp hp with hp|hp
    · exact Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,hp⟩
    · exact Finset.mem_biUnion.mpr ⟨1,Finset.mem_univ _,hp⟩

theorem target_source_global (n : ℕ) (hn : 2301≤n) (a b : Phases) : (atlas n hn a b).target=(atlas n hn b a).source := by
  apply Function.Embedding.ext
  rintro ⟨i,l⟩
  have hh:=target_source n hn a b i l
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (dx n i+·) (congrArg Prod.fst hh)
  · exact congrArg (0+·) (congrArg Prod.snd hh)

theorem goals_eq (n : ℕ) (hn : 2301≤n) (a b : Phases) : (atlas n hn a b).board.goals=boxes n hn b := by
  change Finset.univ.map (atlas n hn a b).target=_
  rw [target_source_global]
  exact initial_boxes n hn b a

theorem board_eq (n : ℕ) (hn : 2301≤n) (a b : Phases) : (atlas n hn a b).board=board n hn (boxes n hn b) :=
  Board.ext (atlas_walls n hn a b) (goals_eq n hn a b)

def storageInstance (n : ℕ) (hn : 2301≤n) (a b : Bool) : Instance := (atlas n hn (uniform a) (uniform b)).puzzle
def slotMatching (n : ℕ) (hn : 2301≤n) (a b : Bool) : SlotMatching (storageInstance n hn a b) (Label n) :=
  (atlas n hn (uniform a) (uniform b)).slotMatching

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
