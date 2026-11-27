/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadFrame
public import PushFS.Reduction.StorageRaster

/-! The four real storage pieces of a gate with three complete long leads. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

def Labels (kind : Bool) (n : ℕ) : Fin 4 → Type :=
  Fin.cases (Fin (Gates.slots kind).length) (fun _ => Chain.Label n)

instance (kind : Bool) (n : ℕ) : (i : Fin 4) → Fintype (Labels kind n i) :=
  Fin.cases (inferInstance : Fintype (Fin (Gates.slots kind).length))
    (fun _ => inferInstanceAs (Fintype (Chain.Label n)))

def piece (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) : Fin 4 → Instance :=
  Fin.cases (Gates.storageInstance kind a b)
    (Fin.cases (GridIsometry.reorientInstance (Chain.puzzle n hn a.left b.left) (westIso kind n))
      (Fin.cases (GridIsometry.reorientInstance (Chain.puzzle n hn a.upper b.upper) (northIso n))
        (fun _ => GridIsometry.reorientInstance (Chain.puzzle n hn (!a.right) (!b.right)) (eastIso n))))

def matching (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) :
    (i : Fin 4) → SlotMatching (piece kind n hn a b i) (Labels kind n i) :=
  Fin.cases (Gates.slotMatching kind a b)
    (Fin.cases ((Chain.slotMatching n hn a.left b.left).reorient (westIso kind n))
      (Fin.cases ((Chain.slotMatching n hn a.upper b.upper).reorient (northIso n))
        (fun _ => (Chain.slotMatching n hn (!a.right) (!b.right)).reorient (eastIso n))))

def dx (kind : Bool) (n : ℕ) : Fin 4 → ℕ :=
  Fin.cases (n+10) (Fin.cases (if kind then 8 else 9)
    (Fin.cases (n+(if kind then 43 else 44)) (fun _ => n+(if kind then 88 else 87))))

def dy (kind : Bool) (n : ℕ) : Fin 4 → ℕ :=
  Fin.cases (n+20) (Fin.cases (n+10+(if kind then 29 else 90))
    (Fin.cases 19 (fun _ => n+100)))

theorem fitsX (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (i : Fin 4) :
    dx kind n i+(piece kind n hn a b i).width≤2*n+101 := by
  fin_cases i
  · change (n+10)+81≤2*n+101; omega
  · change (if kind then 8 else 9)+(n+5)≤2*n+101
    cases kind <;> simp <;> omega
  · change (n+(if kind then 43 else 44))+21≤2*n+101
    cases kind <;> simp <;> omega
  · change (n+(if kind then 88 else 87))+(n+5)≤2*n+101
    cases kind <;> simp <;> omega

theorem fitsY (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (i : Fin 4) :
    dy kind n i+(piece kind n hn a b i).height≤2*n+137 := by
  fin_cases i
  · change (n+20)+107≤2*n+137; omega
  · change (n+10+(if kind then 29 else 90))+21≤2*n+137
    cases kind <;> simp <;> omega
  · change 19+(n+5)≤2*n+137; omega
  · change (n+100)+21≤2*n+137; omega

def placement (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (i : Fin 4) :=
  GridEmbedding.translate (dx kind n i) (dy kind n i)
    (fitsX kind n hn a b i) (fitsY kind n hn a b i)

/-- Real globally placed positions of all physical identities in a canonical configuration. -/
def position (kind : Bool) (n : ℕ) (hn : 2301≤n) (a : Gates.Signals) :
    (i : Fin 4) → Labels kind n i → C n :=
  Fin.cases (fun l => (gate n).cells (Gates.position kind a l))
    (Fin.cases (fun l => (west kind n).cells (Chain.position n hn (Chain.uniform n a.left) l))
      (Fin.cases (fun l => (north kind n).cells (Chain.position n hn (Chain.uniform n a.upper) l))
        (fun _ l => (east kind n).cells (Chain.position n hn (Chain.uniform n (!a.right)) l))))

theorem source_position (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) (l : Labels kind n i) :
    (placement kind n hn a b i).cells ((matching kind n hn a b i).source l)=position kind n hn a i l := by
  fin_cases i <;> rfl

theorem target_position (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) (l : Labels kind n i) :
    (placement kind n hn a b i).cells ((matching kind n hn a b i).target l)=position kind n hn b i l := by
  fin_cases i <;> rfl

private theorem wall01 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (piece kind n hn a b 0).width (piece kind n hn a b 0).height)
    (q : Cell (piece kind n hn a b 1).width (piece kind n hn a b 1).height)
    (he : (placement kind n hn a b 0).cells p=(placement kind n hn a b 1).cells q) :
    p ∈ (piece kind n hn a b 0).board.walls ↔ q ∈ (piece kind n hn a b 1).board.walls := by
  obtain ⟨r,rfl⟩ := (westIso kind n).cells.surjective q
  have he' : (west kind n).cells r=(gate n).cells p := he.symm
  exact (west_walls kind n hn r p he').symm.trans
    ((westIso kind n).mem_walls (Chain.puzzle n hn a.left b.left).board r).symm

private theorem wall02 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (piece kind n hn a b 0).width (piece kind n hn a b 0).height)
    (q : Cell (piece kind n hn a b 2).width (piece kind n hn a b 2).height)
    (he : (placement kind n hn a b 0).cells p=(placement kind n hn a b 2).cells q) :
    p ∈ (piece kind n hn a b 0).board.walls ↔ q ∈ (piece kind n hn a b 2).board.walls := by
  obtain ⟨r,rfl⟩ := (northIso n).cells.surjective q
  have he' : (north kind n).cells r=(gate n).cells p := he.symm
  exact (north_walls kind n hn r p he').symm.trans
    ((northIso n).mem_walls (Chain.puzzle n hn a.upper b.upper).board r).symm

private theorem wall03 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (piece kind n hn a b 0).width (piece kind n hn a b 0).height)
    (q : Cell (piece kind n hn a b 3).width (piece kind n hn a b 3).height)
    (he : (placement kind n hn a b 0).cells p=(placement kind n hn a b 3).cells q) :
    p ∈ (piece kind n hn a b 0).board.walls ↔ q ∈ (piece kind n hn a b 3).board.walls := by
  obtain ⟨r,rfl⟩ := (eastIso n).cells.surjective q
  have he' : (east kind n).cells r=(gate n).cells p := he.symm
  exact (east_walls kind n hn r p he').symm.trans
    ((eastIso n).mem_walls (Chain.puzzle n hn (!a.right) (!b.right)).board r).symm

private theorem disjoint12 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (piece kind n hn a b 1).width (piece kind n hn a b 1).height)
    (q : Cell (piece kind n hn a b 2).width (piece kind n hn a b 2).height) :
    (placement kind n hn a b 1).cells p ≠ (placement kind n hn a b 2).cells q := by
  obtain ⟨r,rfl⟩ := (westIso kind n).cells.surjective p
  obtain ⟨s,rfl⟩ := (northIso n).cells.surjective q
  exact west_ne_north kind n r s

private theorem disjoint13 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (piece kind n hn a b 1).width (piece kind n hn a b 1).height)
    (q : Cell (piece kind n hn a b 3).width (piece kind n hn a b 3).height) :
    (placement kind n hn a b 1).cells p ≠ (placement kind n hn a b 3).cells q := by
  obtain ⟨r,rfl⟩ := (westIso kind n).cells.surjective p
  obtain ⟨s,rfl⟩ := (eastIso n).cells.surjective q
  exact west_ne_east kind n r s

private theorem disjoint23 (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (piece kind n hn a b 2).width (piece kind n hn a b 2).height)
    (q : Cell (piece kind n hn a b 3).width (piece kind n hn a b 3).height) :
    (placement kind n hn a b 2).cells p ≠ (placement kind n hn a b 3).cells q := by
  obtain ⟨r,rfl⟩ := (northIso n).cells.surjective p
  obtain ⟨s,rfl⟩ := (eastIso n).cells.surjective q
  exact north_ne_east kind n r s

/-- The real four-piece atlas agrees at every overlapped wall marker. -/
theorem walls_compatible (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i j : Fin 4) (p : Cell (piece kind n hn a b i).width (piece kind n hn a b i).height)
    (q : Cell (piece kind n hn a b j).width (piece kind n hn a b j).height)
    (he : (dx kind n i+p.1.val,dy kind n i+p.2.val)=
      (dx kind n j+q.1.val,dy kind n j+q.2.val)) :
    p ∈ (piece kind n hn a b i).board.walls ↔ q ∈ (piece kind n hn a b j).board.walls := by
  have he' : (placement kind n hn a b i).cells p=(placement kind n hn a b j).cells q := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  by_cases hij : i=j
  · subst j
    cases (placement kind n hn a b i).cells.injective he'
    rfl
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact wall01 kind n hn a b p q he'
  · exact wall02 kind n hn a b p q he'
  · exact wall03 kind n hn a b p q he'
  · exact (wall01 kind n hn a b q p he'.symm).symm
  · exact False.elim (hij rfl)
  · exact False.elim (disjoint12 kind n hn a b p q he')
  · exact False.elim (disjoint13 kind n hn a b p q he')
  · exact (wall02 kind n hn a b q p he'.symm).symm
  · exact False.elim (disjoint12 kind n hn a b q p he'.symm)
  · exact False.elim (hij rfl)
  · exact False.elim (disjoint23 kind n hn a b p q he')
  · exact (wall03 kind n hn a b q p he'.symm).symm
  · exact False.elim (disjoint13 kind n hn a b q p he'.symm)
  · exact False.elim (disjoint23 kind n hn a b q p he'.symm)
  · exact False.elim (hij rfl)

end PushPuzzle.PushFS.Reduction.GateLead
