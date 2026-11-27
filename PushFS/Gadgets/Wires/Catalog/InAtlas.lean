/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.InGeometry

/-! The actual three-piece L connector, every owned source/goal box and its static matching. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.In


open Reduction

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def Labels (m n : ℕ) : Fin 3 → Type :=
  Fin.cases (FlippedChain.Label m) (Fin.cases (Fin 29) (fun _ : Fin 1 => Chain.Label n))

instance (m n : ℕ) : (i : Fin 3) → Fintype (Labels m n i) :=
  Fin.cases (inferInstance : Fintype (FlippedChain.Label m))
    (Fin.cases (inferInstance : Fintype (Fin 29)) (fun _ : Fin 1 => inferInstanceAs (Fintype (Chain.Label n))))

def piece (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) : Fin 3 → Instance :=
  Fin.cases ((FlippedChain.storageInstance m hm (a 0) (b 0)).transposed.reflectedX.transposed.reflectedX)
    (Fin.cases (Turn.checked.storageInstance (a 1) (b 1))
      (fun _ : Fin 1 => (Chain.puzzle n hn (a 2) (b 2)).transposed.reflectedX))

def matching (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) :
    (i : Fin 3) → SlotMatching (piece m n hm hn a b i) (Labels m n i) :=
  Fin.cases (((((FlippedChain.slotMatching m hm (a 0) (b 0)).reorient (GridIsometry.transpose (m+25) 21)).reorient
      (GridIsometry.reflectX 21 (m+25))).reorient (GridIsometry.transpose 21 (m+25))).reorient
      (GridIsometry.reflectX (m+25) 21))
    (Fin.cases (Turn.checked.slotMatching (a 1) (b 1))
      (fun _ : Fin 1 => ((Chain.slotMatching n hn (a 2) (b 2)).reorient (GridIsometry.transpose (n+5) 21)).reorient
        (GridIsometry.reflectX 21 (n+5))))

def dx (i : Fin 3) : ℕ := if i=0 then 38 else 0
def dy (i : Fin 3) : ℕ := if i=0 then 0 else if i=1 then 1 else 39

theorem fitsX (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) (i : Fin 3) :
    dx i+(piece m n hm hn a b i).width ≤ m+63 := by
  fin_cases i
  · change 38+(m+25) ≤ m+63; omega
  · change 0+45 ≤ m+63; omega
  · change 0+21 ≤ m+63; omega

theorem fitsY (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) (i : Fin 3) :
    dy i+(piece m n hm hn a b i).height ≤ n+44 := by
  fin_cases i
  · change 0+21 ≤ n+44; omega
  · change 1+41 ≤ n+44; omega
  · change 39+(n+5) ≤ n+44; omega

theorem in_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Phases) (p : FlippedChain.C m) :
    (inIso m).cells p∈(piece m n hm hn a b 0).board.walls ↔p∈FlippedChain.walls m hm := by
  change (GridIsometry.reflectX (m+25) 21).cells ((GridIsometry.transpose 21 (m+25)).cells
      ((GridIsometry.reflectX 21 (m+25)).cells ((GridIsometry.transpose (m+25) 21).cells p)))∈
    ((GridIsometry.reflectX (m+25) 21).board ((GridIsometry.transpose 21 (m+25)).board
      ((GridIsometry.reflectX 21 (m+25)).board ((GridIsometry.transpose (m+25) 21).board
        (FlippedChain.atlas m hm (FlippedChain.uniform (a 0)) (FlippedChain.uniform (b 0))).board)))).walls ↔_
  rw [GridIsometry.mem_walls,GridIsometry.mem_walls,GridIsometry.mem_walls,GridIsometry.mem_walls]
  change p∈(FlippedChain.atlas m hm (FlippedChain.uniform (a 0)) (FlippedChain.uniform (b 0))).walls ↔_
  rw [FlippedChain.atlas_walls]

theorem out_walls (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) (p : Chain.C n) :
    (outIso n).cells p ∈ (piece m n hm hn a b 2).board.walls ↔ p ∈ Chain.walls n hn := by
  change (GridIsometry.reflectX 21 (n+5)).cells ((GridIsometry.transpose (n+5) 21).cells p) ∈
    ((GridIsometry.reflectX 21 (n+5)).board ((GridIsometry.transpose (n+5) 21).board
      (Chain.board n hn (Chain.boxes n hn (Chain.uniform n (b 2)))))).walls ↔ _
  rw [GridIsometry.mem_walls,GridIsometry.mem_walls]
  rfl

private theorem walls01 (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases)
    (p : Cell (piece m n hm hn a b 0).width (piece m n hm hn a b 0).height)
    (q : Cell (piece m n hm hn a b 1).width (piece m n hm hn a b 1).height)
    (he : (dx 0+p.1.val,dy 0+p.2.val)=(dx 1+q.1.val,dy 1+q.2.val)) :
    p ∈ (piece m n hm hn a b 0).board.walls ↔ q ∈ (piece m n hm hn a b 1).board.walls := by
  obtain ⟨r,rfl⟩ := (inIso m).cells.surjective p
  have he' : (inEmbed m n hm hn).cells r=(turnRect m n hm hn).cells q := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  exact (in_walls m n hm hn a b r).trans (in_turn_walls m n hm hn r q he')

private theorem walls12 (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases)
    (p : Cell (piece m n hm hn a b 1).width (piece m n hm hn a b 1).height)
    (q : Cell (piece m n hm hn a b 2).width (piece m n hm hn a b 2).height)
    (he : (dx 1+p.1.val,dy 1+p.2.val)=(dx 2+q.1.val,dy 2+q.2.val)) :
    p ∈ (piece m n hm hn a b 1).board.walls ↔ q ∈ (piece m n hm hn a b 2).board.walls := by
  obtain ⟨r,rfl⟩ := (outIso n).cells.surjective q
  have he' : (turnRect m n hm hn).cells p=(outEmbed m n hm hn).cells r := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  exact (turn_out_walls m n hm hn p r he').trans (out_walls m n hm hn a b r).symm

theorem walls_compatible (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases)
    (i j : Fin 3) (p : Cell (piece m n hm hn a b i).width (piece m n hm hn a b i).height)
    (q : Cell (piece m n hm hn a b j).width (piece m n hm hn a b j).height)
    (he : (dx i+p.1.val,dy i+p.2.val)=(dx j+q.1.val,dy j+q.2.val)) :
    p ∈ (piece m n hm hn a b i).board.walls ↔ q ∈ (piece m n hm hn a b j).board.walls := by
  by_cases hij : i=j
  · subst j
    have hpq : p=q := by
      apply Prod.ext <;> apply Fin.ext
      · have hh := congrArg Prod.fst he; omega
      · have hh := congrArg Prod.snd he; omega
    subst q
    rfl
  · fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact walls01 m n hm hn a b p q he
    · have hh := congrArg Prod.fst he
      have hq : q.1.val < 21 := q.1.isLt
      change 38+p.1.val=0+q.1.val at hh
      omega
    · exact (walls01 m n hm hn a b q p he.symm).symm
    · exact False.elim (hij rfl)
    · exact walls12 m n hm hn a b p q he
    · have hh := congrArg Prod.fst he
      have hp : p.1.val < 21 := p.1.isLt
      change 0+p.1.val=38+q.1.val at hh
      omega
    · exact (walls12 m n hm hn a b q p he.symm).symm
    · exact False.elim (hij rfl)

theorem source0_bounds (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Phases) (l : Labels m n 0) :
    41≤dx 0+((matching m n hm hn a b 0).source l).1.val ∧
      dy 0+((matching m n hm hn a b 0).source l).2.val=10 := by
  have hh:=FlippedChain.position_bounds m hm (a 0) l
  have hy:=FlippedChain.position_row m hm (a 0) l
  change 41≤38+((m+25)-(((FlippedChain.slotMatching m hm (a 0) (b 0)).source l).1.val+1)) ∧
    0+(21-(((FlippedChain.slotMatching m hm (a 0) (b 0)).source l).2.val+1))=10
  rw [FlippedChain.source_position m hm (a 0) (b 0) l]
  have ha : (a 0).toNat≤1 := by cases a 0 <;> decide
  omega

theorem source1_bounds (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) (l : Labels m n 1) :
    (dy 1+((matching m n hm hn a b 1).source l).2.val=10 ∧
      dx 1+((matching m n hm hn a b 1).source l).1.val ≤ 40) ∨
    (dx 1+((matching m n hm hn a b 1).source l).1.val=10 ∧
      dy 1+((matching m n hm hn a b 1).source l).2.val ≤ 40) := by
  have hh := Polyline.turn_slot_bounds (a 1) l
  change (1+(Turn.template.position (a 1) l).2.val=10 ∧ 0+(Turn.template.position (a 1) l).1.val ≤40) ∨
    (0+(Turn.template.position (a 1) l).1.val=10 ∧ 1+(Turn.template.position (a 1) l).2.val≤40)
  omega

theorem source2_bounds (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) (l : Labels m n 2) :
    dx 2+((matching m n hm hn a b 2).source l).1.val=10 ∧
      41 ≤ dy 2+((matching m n hm hn a b 2).source l).2.val := by
  have hh := Polyline.chain_slot_bounds n hn (Chain.uniform n (a 2)) l
  have hy := Chain.position_row n hn (Chain.uniform n (a 2)) l
  change ((outEmbed m n hm hn).cells (Chain.position n hn (Chain.uniform n (a 2)) l)).1.val=10 ∧
    41 ≤ ((outEmbed m n hm hn).cells (Chain.position n hn (Chain.uniform n (a 2)) l)).2.val
  rw [out_x,out_y,hy]
  omega

theorem source_owners (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases)
    (i j : Fin 3) (l : Labels m n i) (k : Labels m n j)
    (he : (dx i+((matching m n hm hn a b i).source l).1.val,dy i+((matching m n hm hn a b i).source l).2.val)=
      (dx j+((matching m n hm hn a b j).source k).1.val,dy j+((matching m n hm hn a b j).source k).2.val)) : i=j := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have cases3 (k : Fin 3) : k=0 ∨ k=1 ∨ k=2 := by
    have := k.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases3 i with rfl|rfl|rfl <;> rcases cases3 j with rfl|rfl|rfl
  · rfl
  · have hp := source0_bounds m n hm hn a b l; have hq := source1_bounds m n hm hn a b k; omega
  · have hp := source0_bounds m n hm hn a b l; have hq := source2_bounds m n hm hn a b k; omega
  · have hp := source1_bounds m n hm hn a b l; have hq := source0_bounds m n hm hn a b k; omega
  · rfl
  · have hp := source1_bounds m n hm hn a b l; have hq := source2_bounds m n hm hn a b k; omega
  · have hp := source2_bounds m n hm hn a b l; have hq := source0_bounds m n hm hn a b k; omega
  · have hp := source2_bounds m n hm hn a b l; have hq := source1_bounds m n hm hn a b k; omega
  · rfl

theorem target_source (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Phases)
    (i : Fin 3) (l : Labels m n i) :
    (((matching m n hm hn a b i).target l).1.val,((matching m n hm hn a b i).target l).2.val)=
      (((matching m n hm hn b a i).source l).1.val,((matching m n hm hn b a i).source l).2.val) := by
  fin_cases i
  · change ((m+25)-(((FlippedChain.slotMatching m hm (a 0) (b 0)).target l).1.val+1),
        21-(((FlippedChain.slotMatching m hm (a 0) (b 0)).target l).2.val+1))=
      ((m+25)-(((FlippedChain.slotMatching m hm (b 0) (a 0)).source l).1.val+1),
        21-(((FlippedChain.slotMatching m hm (b 0) (a 0)).source l).2.val+1))
    rw [FlippedChain.target_position m hm (a 0) (b 0) l,FlippedChain.source_position m hm (b 0) (a 0) l]
  · rfl
  · rfl

def player (m n : ℕ) : C m n := (⟨38,by omega⟩,⟨21,by omega⟩)

def atlas (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (a b : Phases) : StorageAtlas 3 (m+63) (n+44) (Labels m n) where
  piece := piece m n hm hn a b
  matching := matching m n hm hn a b
  dx := dx
  dy := dy
  fitsX := fitsX m n hm hn a b
  fitsY := fitsY m n hm hn a b
  walls_compatible := walls_compatible m n hm hn a b
  source_owners := source_owners m n hm hn a b
  target_owners := by
    intro i j l k he
    have hi := target_source m n hm hn a b i l
    have hj := target_source m n hm hn a b j k
    have hix := congrArg Prod.fst hi
    have hiy := congrArg Prod.snd hi
    have hjx := congrArg Prod.fst hj
    have hjy := congrArg Prod.snd hj
    have hex := congrArg Prod.fst he
    have hey := congrArg Prod.snd he
    apply source_owners m n hm hn b a i j l k
    apply Prod.ext
    · dsimp only at hix hjx hex ⊢; omega
    · dsimp only at hiy hjy hey ⊢; omega
  player := player m n
  player_floor := by
    intro i p hp he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    fin_cases i
    · have hy' : p.2.val < 21 := p.2.isLt
      change 21=0+p.2.val at hy
      omega
    · have he' : p=Turn.hub := by
        apply Prod.ext <;> apply Fin.ext
        · change 38=0+p.1.val at hx
          change p.1.val=38
          omega
        · change 21=1+p.2.val at hy
          change p.2.val=20
          omega
      change p∈Turn.template.walls at hp
      rw [he'] at hp
      exact (Turn.checked.state_valid (a 1) ∅).1 hp
    · have hx' : p.1.val < 21 := p.1.isLt
      change 38=0+p.1.val at hx
      omega
  player_empty := by
    intro i l he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    fin_cases i
    · have hh := source0_bounds m n hm hn a b l
      change 21=dy 0+((matching m n hm hn a b 0).source l).2.val at hy
      omega
    · have hh := source1_bounds m n hm hn a b l
      change 38=dx 1+((matching m n hm hn a b 1).source l).1.val at hx
      change 21=dy 1+((matching m n hm hn a b 1).source l).2.val at hy
      omega
    · have hh := source2_bounds m n hm hn a b l
      change 38=dx 2+((matching m n hm hn a b 2).source l).1.val at hx
      omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
