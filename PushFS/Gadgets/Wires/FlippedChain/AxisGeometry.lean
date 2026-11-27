/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Statics
public import PushFS.AxisIsometry

/-! Exact protective collar sides and all D4 static classifiers of the actual FlippedChain board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


variable (n : ℕ) (hn : 2301≤n)

/-- The complete five-column near collar has its true south protective wall. -/
theorem left_collar (p : C n) (hp : p.1.val<5) :
    p∈walls n hn ↔p.2.val=11 ∨ p.2.val=12 := by
  let q : Chain.C n := (⟨p.1.val,by omega⟩,p.2)
  have he : (chainPlacement n).cells q=p := by
    apply Prod.ext <;> apply Fin.ext
    · exact chain_x n q
    · exact chain_y n q
  rw [←he,chain_y]
  exact (chain_walls n hn ∅ q).trans (Polyline.chain_left5 n hn q hp)

/-- The complete five-column far collar has its true north protective wall. -/
theorem right_collar (p : C n) (hp : n+20≤p.1.val) :
    p∈walls n hn ↔p.2.val=8 ∨ p.2.val=9 := by
  let q : Flip.C := (⟨p.1.val-n,by have := p.1.isLt; omega⟩,p.2)
  have he : (flipPlacement n).cells q=p := by
    apply Prod.ext <;> apply Fin.ext
    · change n+(p.1.val-n)=p.1.val
      omega
    · exact flip_y n q
  rw [←he,flip_y]
  have hw : q∈Flip.template.walls ↔q.2.val=8 ∨ q.2.val=9 := by
    rw [Template.mem_walls]
    change Flip.wallTest q=true↔_
    rw [Flip.right_collar q (by change 20≤p.1.val-n; omega),decide_eq_true_eq]
  exact (flip_walls n hn ∅ q).trans hw

/-- Every active actual displacement stays on the same physical row, a D4-stable strong relation. -/
theorem strong_displacement (goals : Finset (C n)) {p q : C n} (hp : axisName n p≠.outside)
    (hd : Displacement (board n hn goals) p q) : (axisName n p).Strong (axisName n q) := by
  have hrow : p.2.val=10 := by by_contra he; exact hp (by simp [axisName,he])
  have hq:=displacement_row n hn goals hrow hd
  exact Or.inl (by simp [axisName,hrow,hq])

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
