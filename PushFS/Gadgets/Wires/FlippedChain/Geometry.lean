/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.Collars
public import PushFS.Gadgets.Wires.Polyline.Endpoints
public import PushFS.Gadgets.Wires.Flip

/-! Exact overlap, full inventories and literal wall stencils of a long chain followed by one terminal flip. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

abbrev C (n : ℕ) := Cell (n+25) 21

def chainPlacement (n : ℕ) : GridEmbedding (n+5) 21 (n+25) 21 :=
  GridEmbedding.translate 0 0 (by omega) (by omega)
def flipPlacement (n : ℕ) : GridEmbedding 25 21 (n+25) 21 :=
  GridEmbedding.translate n 0 (by omega) (by omega)

@[simp] theorem chain_x (n : ℕ) (p : Chain.C n) : ((chainPlacement n).cells p).1.val=p.1.val := by change 0+p.1.val=p.1.val; omega
@[simp] theorem chain_y (n : ℕ) (p : Chain.C n) : ((chainPlacement n).cells p).2.val=p.2.val := by change 0+p.2.val=p.2.val; omega
@[simp] theorem flip_x (n : ℕ) (p : Flip.C) : ((flipPlacement n).cells p).1.val=n+p.1.val := rfl
@[simp] theorem flip_y (n : ℕ) (p : Flip.C) : ((flipPlacement n).cells p).2.val=p.2.val := by change 0+p.2.val=p.2.val; omega

/-- Every shared cell in the five-column overlap has precisely the same true protective wall. -/
theorem overlap_walls (n : ℕ) (hn : 2301≤n) (p : Chain.C n) (q : Flip.C)
    (he : (chainPlacement n).cells p=(flipPlacement n).cells q) :
    p∈Chain.walls n hn ↔ q∈Flip.template.walls := by
  have hx:=congrArg (fun p : C n=>p.1.val) he
  have hy:=congrArg (fun p : C n=>p.2.val) he
  simp only [chain_x,flip_x] at hx
  simp only [chain_y,flip_y] at hy
  have hp:=p.1.isLt
  rw [Polyline.chain_right7 n hn p (by omega),Template.mem_walls]
  change _↔Flip.wallTest q=true
  rw [Flip.left_collar q (by omega),decide_eq_true_eq]
  omega

def walls (n : ℕ) (hn : 2301≤n) : Finset (C n) :=
  (Chain.walls n hn).map (chainPlacement n).cells∪Flip.template.walls.map (flipPlacement n).cells

def board (n : ℕ) (hn : 2301≤n) (goals : Finset (C n)) : Board (n+25) 21 := ⟨walls n hn,goals⟩

theorem chain_walls (n : ℕ) (hn : 2301≤n) (goals : Finset (C n)) :
    (chainPlacement n).WallsAgree (Chain.board n hn ∅) (board n hn goals) := by
  intro p
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with hw|hw
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hw
      exact (chainPlacement n).cells.injective he ▸ hq
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hw
      exact (overlap_walls n hn p q he.symm).mpr hq
  · exact fun hp=>Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p,hp,rfl⟩)

theorem flip_walls (n : ℕ) (hn : 2301≤n) (goals : Finset (C n)) :
    (flipPlacement n).WallsAgree (Flip.template.board ∅) (board n hn goals) := by
  intro p
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with hw|hw
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hw
      exact (overlap_walls n hn q p he).mp hq
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hw
      exact (flipPlacement n).cells.injective he ▸ hq
  · exact fun hp=>Finset.mem_union_right _ (Finset.mem_map.mpr ⟨p,hp,rfl⟩)

theorem walls_rows (n : ℕ) (hn : 2301≤n) {p : C n} (hp : p∈walls n hn) :
    p.2.val=8 ∨ p.2.val=9 ∨ p.2.val=11 ∨ p.2.val=12 := by
  rcases Finset.mem_union.mp hp with hp|hp
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    simpa only [chain_y] using Chain.walls_rows n hn q hq
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    have check : ∀q : Flip.C, Flip.wallTest q=true → q.2.val=8 ∨ q.2.val=9 ∨ q.2.val=11 ∨ q.2.val=12 := by decide +kernel
    simpa only [flip_y] using check q ((Flip.template.mem_walls q).mp hq)

theorem flip_bounds (phase : Bool) (i : Fin 9) : (Flip.template.position phase i).2.val=10 ∧
    2+phase.toNat≤(Flip.template.position phase i).1.val ∧ (Flip.template.position phase i).1.val≤20+phase.toNat := by
  have check : ∀(phase : Bool)(i : Fin 9), (Flip.template.position phase i).2.val=10 ∧
      2+phase.toNat≤(Flip.template.position phase i).1.val ∧ (Flip.template.position phase i).1.val≤20+phase.toNat := by decide +kernel
  exact check phase i

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
