/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreChartCover
import Mathlib.Tactic.FinCases

/-! Safe interior owners of the finite-core rail stencils. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateStencils

open PushFS FiniteGeometry

attribute [local irreducible] side

/-- An interior chart represents at least the original level at the same physical floor cell. -/
def AndOwner (w : ℕ) (hw : 2 ≤ w) (p : Cell (side w) (side w)) (level : ℕ) : Prop :=
  ∃ c q, 0 < q.1.val ∧ q.1.val+1 < (andChart w hw c).width ∧
    0 < q.2.val ∧ q.2.val+1 < (andChart w hw c).height ∧
    (andChart w hw c).embedding.cells q = p ∧ level ≤ ((andChart w hw c).classifier.name q).level

private theorem owner_self (w : ℕ) (hw : 2 ≤ w) (c : AndChart)
    (p : Cell (andChart w hw c).width (andChart w hw c).height)
    (hx : 0 < p.1.val ∧ p.1.val+1 < (andChart w hw c).width)
    (hy : 0 < p.2.val ∧ p.2.val+1 < (andChart w hw c).height) :
    AndOwner w hw ((andChart w hw c).embedding.cells p) ((andChart w hw c).classifier.name p).level :=
  ⟨c,p,hx.1,hx.2,hy.1,hy.2,rfl,le_rfl⟩

/-- The two endpoints of the vertical flip rail are owned by the actual concave sink charts. -/
private theorem andVertical_owner (w : ℕ) (hw : 2 ≤ w) (p : Cell 3 (6*w+22))
    (hp : (andVertical w hw).classifier.name p ≠ .outside) :
    AndOwner w hw ((andVertical w hw).embedding.cells p) ((andVertical w hw).classifier.name p).level := by
  have hx : p.1.val = 1 := by
    by_contra he
    apply hp
    change (if p.1 = (1 : Fin 3) then AxisTrack.vertical 1 else .outside) = .outside
    exact ite_eq_right (fun h => he (congrArg Fin.val h))
  have hl : ((andVertical w hw).classifier.name p).level = 1 := by
    change (if p.1 = (1 : Fin 3) then AxisTrack.vertical 1 else .outside).level = 1
    rw [ite_eq_left (Fin.ext hx)]
    rfl
  have hy := p.2.isLt
  by_cases h0 : p.2.val = 0
  · refine ⟨.upperCorner,((1,1) : Cell 3 3),by change 0 < 1; decide,by change 2 < 3; decide,
        by change 0 < 1; decide,by change 2 < 3; decide,?_,?_⟩
    · apply Prod.ext <;> apply Fin.ext
      · change origin w-6*w-10+1 = origin w-6*w-10+p.1.val
        omega
      · change origin w-6*w-22+1 = origin w-6*w-21+p.2.val
        unfold origin
        omega
    · rw [hl]
      change 1 ≤ 3
      decide
  · by_cases hlast : p.2.val+1 = 6*w+22
    · refine ⟨.protectionCorner,((1,1) : Cell 3 3),by change 0 < 1; decide,by change 2 < 3; decide,
        by change 0 < 1; decide,by change 2 < 3; decide,?_,?_⟩
      · apply Prod.ext <;> apply Fin.ext
        · change origin w-6*w-10+1 = origin w-6*w-10+p.1.val
          omega
        · change origin w-1+1 = origin w-6*w-21+p.2.val
          unfold origin
          omega
      · rw [hl]
        change 1 ≤ 3
        decide
    · exact owner_self w hw .vertical p ⟨by omega,by change p.1.val+1 < 3; omega⟩
        ⟨by omega,by change p.2.val+1 < 6*w+22; omega⟩

private theorem andUpperCorner_owner (w : ℕ) (hw : 2 ≤ w) (p : Cell 3 3)
    (hp : (andUpperCorner w).classifier.name p ≠ .outside) :
    AndOwner w hw ((andUpperCorner w).embedding.cells p) ((andUpperCorner w).classifier.name p).level := by
  change (GuardStencils.cornerClassifier (1 : Fin 3) (1 : Fin 3)).name p ≠ .outside at hp
  rcases p with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    simp [GuardStencils.cornerClassifier,GuardStencils.cornerName,Fin.ext_iff] at hp
  · refine ⟨.west,(⟨2*w+8,by dsimp [andChart,andWest]; omega⟩,(1 : Fin 3)),?_,?_,?_,?_,?_,?_⟩
    · change 0 < 2*w+8; omega
    · change 2*w+8+1 < 2*w+11; omega
    · change 0 < 1; decide
    · change 2 < 3; decide
    · apply Prod.ext <;> apply Fin.ext
      · change origin w-8*w-18+(2*w+8) = origin w-6*w-10+0
        unfold origin
        omega
      · rfl
    · change 2 ≤ 2; decide
  · exact owner_self w hw .upperCorner ((1,1) : Cell 3 3)
      ⟨by change 0 < 1; decide,by change 2 < 3; decide⟩
      ⟨by change 0 < 1; decide,by change 2 < 3; decide⟩
  · refine ⟨.vertical,((1 : Fin 3),⟨1,by dsimp [andChart,andVertical]; omega⟩),?_,?_,?_,?_,?_,?_⟩
    · change 0 < 1; decide
    · change 2 < 3; decide
    · change 0 < 1; decide
    · change 2 < 6*w+22; omega
    · apply Prod.ext <;> apply Fin.ext
      · rfl
      · change origin w-6*w-21+1 = origin w-6*w-22+2
        unfold origin
        omega
    · change 1 ≤ 1; decide

private theorem protection_name (p : Cell 3 3) :
    protectionClassifier.name p =
      if p.1.val = 1 ∧ p.2.val = 1 then .sink 1 1
      else if p.1.val = 2 ∧ p.2.val = 1 then .horizontal 1
      else if p.1.val = 1 ∧ p.2.val = 0 then .vertical 1 else .outside := by
  rcases p with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide

private theorem andProtectionCorner_owner (w : ℕ) (hw : 2 ≤ w) (p : Cell 3 3)
    (hp : (andProtectionCorner w).classifier.name p ≠ .outside) :
    AndOwner w hw ((andProtectionCorner w).embedding.cells p)
      ((andProtectionCorner w).classifier.name p).level := by
  change protectionClassifier.name p ≠ .outside at hp
  rw [protection_name] at hp
  rcases p with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> simp at hp
  · refine ⟨.vertical,((1 : Fin 3),⟨6*w+20,by dsimp [andChart,andVertical]; omega⟩),?_,?_,?_,?_,?_,?_⟩
    · change 0 < 1; decide
    · change 2 < 3; decide
    · change 0 < 6*w+20; omega
    · change 6*w+20+1 < 6*w+22; omega
    · apply Prod.ext <;> apply Fin.ext
      · rfl
      · change origin w-6*w-21+(6*w+20) = origin w-1+0
        unfold origin
        omega
    · change 1 ≤ 1; decide
  · exact owner_self w hw .protectionCorner ((1,1) : Cell 3 3)
      ⟨by change 0 < 1; decide,by change 2 < 3; decide⟩
      ⟨by change 0 < 1; decide,by change 2 < 3; decide⟩
  · refine ⟨.junction,(⟨w+1,by dsimp [andChart,andJunction]; omega⟩,
        ⟨10*w+41,by dsimp [andChart,andJunction]; omega⟩),?_,?_,?_,?_,?_,?_⟩
    · change 0 < w+1; omega
    · change w+1+1 < 12*w+33; omega
    · change 0 < 10*w+41; omega
    · change 10*w+41+1 < 10*w+43; omega
    · apply Prod.ext <;> apply Fin.ext
      · change origin w-7*w-9+(w+1) = origin w-6*w-10+2
        unfold origin
        omega
      · change origin w-10*w-41+(10*w+41) = origin w-1+1
        unfold origin
        omega
    · change 2 ≤ (GuardStencils.junctionName
        (⟨7*w+12,by omega⟩ : Fin (12*w+33)) (⟨10*w+41,by omega⟩ : Fin (10*w+43))
          (⟨w+1,by omega⟩,⟨10*w+41,by omega⟩)).level
      simp only [GuardStencils.junctionName,ite_true,AxisTrack.level]
      exact le_rfl

/-- The three actual core-chart ends continued by the emitted arm stocks. -/
def AndExit (w : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.1.val = origin w-8*w-18 ∧ p.2.val = origin w-6*w-21) ∨
    (p.1.val = origin w+3 ∧ p.2.val = origin w-10*w-41) ∨
    (p.1.val = origin w+5*w+23 ∧ p.2.val = origin w)

private theorem andWest_owner_or_exit (w : ℕ) (hw : 2 ≤ w) (p : Cell (2*w+11) 3)
    (hp : (andWest w hw).classifier.name p ≠ .outside)
    (hf : (andWest w hw).embedding.cells p ∉ andWalls w) :
    AndExit w ((andWest w hw).embedding.cells p) ∨
      AndOwner w hw ((andWest w hw).embedding.cells p) ((andWest w hw).classifier.name p).level := by
  have hy : p.2.val = 1 := by
    by_contra he
    apply hp
    change (if p.2 = (1 : Fin 3) then AxisTrack.horizontal 1 else .outside) = .outside
    exact ite_eq_right (fun h => he (congrArg Fin.val h))
  have hx := p.1.isLt
  by_cases h0 : p.1.val = 0
  · left
    left
    change origin w-8*w-18+p.1.val = _ ∧ origin w-6*w-22+p.2.val = _
    unfold origin
    omega
  · by_cases hlast : p.1.val+1 = 2*w+11
    · have he : (andUpperCorner w).embedding.cells ((2,1) : Cell 3 3) =
          (andWest w hw).embedding.cells p := by
        apply Prod.ext <;> apply Fin.ext
        · change origin w-6*w-10+2 = origin w-8*w-18+p.1.val
          unfold origin
          omega
        · change origin w-6*w-22+1 = origin w-6*w-22+p.2.val
          omega
      exact False.elim (hf (he ▸ andUpperCorner_walls w hw ((2,1) : Cell 3 3)
        (by change ((2,1) : Cell 3 3) ∈ (GuardStencils.cornerBoard 1 1).walls; decide)))
    · right
      exact owner_self w hw .west p ⟨by omega,by change p.1.val+1 < 2*w+11; omega⟩
        ⟨by omega,by change p.2.val+1 < 3; omega⟩

private theorem junction_interior_or_end {W H : ℕ} (j : Fin W) (row : Fin H)
    (hj : 0 < j.val ∧ j.val+1 < W) (hr : 0 < row.val ∧ row.val+1 < H)
    (p : Cell W H) (hp : GuardStencils.junctionName j row p ≠ .outside) :
    (0 < p.1.val ∧ p.1.val+1 < W ∧ 0 < p.2.val ∧ p.2.val+1 < H) ∨
      (p.2.val = row.val ∧ (p.1.val = 0 ∨ p.1.val+1 = W)) ∨
      (p.1.val = j.val ∧ p.2.val = 0) := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  by_cases hh : p.2 = row
  · have hh' := congrArg Fin.val hh
    by_cases hx0 : p.1.val = 0
    · exact Or.inr (Or.inl ⟨hh',Or.inl hx0⟩)
    · by_cases hxlast : p.1.val+1 = W
      · exact Or.inr (Or.inl ⟨hh',Or.inr hxlast⟩)
      · exact Or.inl ⟨by omega,by omega,by omega,by omega⟩
  · have hv : p.1 = j ∧ p.2.val < row.val := by
      by_contra hn
      exact hp (by simp only [GuardStencils.junctionName,hh,hn,ite_false])
    have hxj := congrArg Fin.val hv.1
    by_cases hy0 : p.2.val = 0
    · exact Or.inr (Or.inr ⟨hxj,hy0⟩)
    · exact Or.inl ⟨by omega,by omega,by omega,by omega⟩

private theorem andJunction_owner_or_exit (w : ℕ) (hw : 2 ≤ w) (p : Cell (12*w+33) (10*w+43))
    (hp : (andJunction w).classifier.name p ≠ .outside)
    (hf : (andJunction w).embedding.cells p ∉ andWalls w) :
    AndExit w ((andJunction w).embedding.cells p) ∨
      AndOwner w hw ((andJunction w).embedding.cells p) ((andJunction w).classifier.name p).level := by
  obtain hi | ⟨hy,hx0 | hxlast⟩ | ⟨hx,hy⟩ := junction_interior_or_end
    (⟨7*w+12,by omega⟩ : Fin (12*w+33)) (⟨10*w+41,by omega⟩ : Fin (10*w+43))
    ⟨by change 0 < 7*w+12; omega,by change 7*w+12+1 < 12*w+33; omega⟩
    ⟨by change 0 < 10*w+41; omega,by change 10*w+41+1 < 10*w+43; omega⟩ p hp
  · exact Or.inr (owner_self w hw .junction p ⟨hi.1,hi.2.1⟩ ⟨hi.2.2.1,hi.2.2.2⟩)
  · change p.2.val = 10*w+41 at hy
    change p.1.val = 0 at hx0
    have hwall : (andJunction w).embedding.cells p ∈ andWalls w := by
      apply Finset.mem_biUnion.mpr
      refine ⟨1,Finset.mem_univ _,?_⟩
      apply (Rectangle.mem_cells (andRectangle w 1) _ _ _).mpr
      have hX : ((andJunction w).embedding.cells p).1.val = origin w-7*w-9+p.1.val := rfl
      have hY : ((andJunction w).embedding.cells p).2.val = origin w-10*w-41+p.2.val := rfl
      rw [hX,hY]
      simp [andRectangle,origin]
      omega
    exact False.elim (hf hwall)
  · change p.2.val = 10*w+41 at hy
    change p.1.val+1 = 12*w+33 at hxlast
    left
    right
    right
    change origin w-7*w-9+p.1.val = _ ∧ origin w-10*w-41+p.2.val = _
    unfold origin
    omega
  · change p.1.val = 7*w+12 at hx
    change p.2.val = 0 at hy
    left
    right
    left
    change origin w-7*w-9+p.1.val = _ ∧ origin w-10*w-41+p.2.val = _
    unfold origin
    omega

/-- Every represented actual AND floor cell has a safe owner or is one of the three routed arm ends. -/
theorem andChart_owner_or_exit (w : ℕ) (hw : 2 ≤ w) (c : AndChart)
    (p : Cell (andChart w hw c).width (andChart w hw c).height)
    (hp : (andChart w hw c).classifier.name p ≠ .outside)
    (hf : (andChart w hw c).embedding.cells p ∉ andWalls w) :
    AndExit w ((andChart w hw c).embedding.cells p) ∨
      AndOwner w hw ((andChart w hw c).embedding.cells p) ((andChart w hw c).classifier.name p).level := by
  cases c with
  | junction => exact andJunction_owner_or_exit w hw p hp hf
  | vertical => exact Or.inr (andVertical_owner w hw p hp)
  | west => exact andWest_owner_or_exit w hw p hp hf
  | upperCorner => exact Or.inr (andUpperCorner_owner w hw p hp)
  | protectionCorner => exact Or.inr (andProtectionCorner_owner w hw p hp)

def OrOwner (w : ℕ) (p : Cell (side w) (side w)) (level : ℕ) : Prop :=
  ∃ q : Cell (9*w+42) (4*w+25), 0 < q.1.val ∧ q.1.val+1 < 9*w+42 ∧
    0 < q.2.val ∧ q.2.val+1 < 4*w+25 ∧ (orJunction w).embedding.cells q = p ∧
    level ≤ ((orJunction w).classifier.name q).level

def OrExit (w : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.1.val = origin w-4*w-17 ∧ p.2.val = origin w) ∨
    (p.1.val = origin w+4 ∧ p.2.val = origin w-4*w-23) ∨
    (p.1.val = origin w+5*w+24 ∧ p.2.val = origin w)

/-- Every represented OR cell is interior or one of the three actual routed arm ends. -/
theorem orJunction_owner_or_exit (w : ℕ) (p : Cell (9*w+42) (4*w+25))
    (hp : (orJunction w).classifier.name p ≠ .outside) :
    OrExit w ((orJunction w).embedding.cells p) ∨
      OrOwner w ((orJunction w).embedding.cells p) ((orJunction w).classifier.name p).level := by
  obtain hi | ⟨hy,hx0 | hxlast⟩ | ⟨hx,hy⟩ := junction_interior_or_end
    (⟨4*w+21,by omega⟩ : Fin (9*w+42)) (⟨4*w+23,by omega⟩ : Fin (4*w+25))
    ⟨by change 0 < 4*w+21; omega,by change 4*w+21+1 < 9*w+42; omega⟩
    ⟨by change 0 < 4*w+23; omega,by change 4*w+23+1 < 4*w+25; omega⟩ p hp
  · exact Or.inr ⟨p,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,rfl,le_rfl⟩
  · change p.2.val = 4*w+23 at hy
    change p.1.val = 0 at hx0
    left
    left
    change origin w-4*w-17+p.1.val = _ ∧ origin w-4*w-23+p.2.val = _
    unfold origin
    omega
  · change p.2.val = 4*w+23 at hy
    change p.1.val+1 = 9*w+42 at hxlast
    left
    right
    right
    change origin w-4*w-17+p.1.val = _ ∧ origin w-4*w-23+p.2.val = _
    unfold origin
    omega
  · change p.1.val = 4*w+21 at hx
    change p.2.val = 0 at hy
    left
    right
    left
    change origin w-4*w-17+p.1.val = _ ∧ origin w-4*w-23+p.2.val = _
    unfold origin
    omega

/-- The B exit is vertical; the A and C exits retain their horizontal level. -/
theorem andChart_exit_level (w : ℕ) (hw : 2 ≤ w) (c : AndChart)
    (p : Cell (andChart w hw c).width (andChart w hw c).height)
    (he : AndExit w ((andChart w hw c).embedding.cells p)) :
    ((andChart w hw c).classifier.name p).level =
      if ((andChart w hw c).embedding.cells p).1.val = origin w+3 then 1 else 2 := by
  have hx : ((andChart w hw c).embedding.cells p).1.val = (andChart w hw c).dx+p.1.val := rfl
  have hy : ((andChart w hw c).embedding.cells p).2.val = (andChart w hw c).dy+p.2.val := rfl
  simp only [AndExit,hx,hy] at he
  rw [hx]
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  cases c <;> dsimp only [andChart,andJunction,andVertical,andWest,andUpperCorner,andProtectionCorner] at he hpx hpy ⊢
  all_goals rcases he with ⟨hAx,hAy⟩ | ⟨hBx,hBy⟩ | ⟨hCx,hCy⟩
  all_goals unfold origin at *
  all_goals try omega
  · change Cell (12*w+33) (10*w+43) at p
    have hj : p.1 = (⟨7*w+12,by omega⟩ : Fin (12*w+33)) := by
      apply Fin.ext
      change p.1.val = 7*w+12
      omega
    have hrow : p.2 ≠ (⟨10*w+41,by omega⟩ : Fin (10*w+43)) := by
      intro hh
      have hv := congrArg Fin.val hh
      change p.2.val = 10*w+41 at hv
      omega
    have hlt : p.2.val < 10*w+41 := by omega
    have hl : (GuardStencils.junctionName (⟨7*w+12,by omega⟩ : Fin (12*w+33))
        (⟨10*w+41,by omega⟩ : Fin (10*w+43)) p).level = 1 := by
      unfold GuardStencils.junctionName
      rw [ite_eq_right hrow,ite_eq_left ⟨hj,hlt⟩]
      rfl
    exact hl.trans (ite_eq_left hBx).symm
  · change Cell (12*w+33) (10*w+43) at p
    have hne : 100*(w+3)-7*w-9+p.1.val ≠ 100*(w+3)+3 := by omega
    have hrow : p.2 = (⟨10*w+41,by omega⟩ : Fin (10*w+43)) := by
      apply Fin.ext
      change p.2.val = 10*w+41
      omega
    have hl : (GuardStencils.junctionName (⟨7*w+12,by omega⟩ : Fin (12*w+33))
        (⟨10*w+41,by omega⟩ : Fin (10*w+43)) p).level = 2 := by
      unfold GuardStencils.junctionName
      rw [ite_eq_left hrow]
      rfl
    exact hl.trans (ite_eq_right hne).symm
  · change Cell (2*w+11) 3 at p
    have hne : 100*(w+3)-8*w-18+p.1.val ≠ 100*(w+3)+3 := by omega
    have hrow : p.2 = (1 : Fin 3) := by
      apply Fin.ext
      change p.2.val = 1
      omega
    have hl : (if p.2 = (1 : Fin 3) then AxisTrack.horizontal 1 else .outside).level = 2 := by
      rw [ite_eq_left hrow]
      rfl
    exact hl.trans (ite_eq_right hne).symm

/-- The OR exit at its B column is vertical; its two side exits are horizontal. -/
theorem orJunction_exit_level (w : ℕ) (p : Cell (9*w+42) (4*w+25))
    (he : OrExit w ((orJunction w).embedding.cells p)) :
    ((orJunction w).classifier.name p).level =
      if ((orJunction w).embedding.cells p).1.val = origin w+4 then 1 else 2 := by
  have hx : ((orJunction w).embedding.cells p).1.val = origin w-4*w-17+p.1.val := rfl
  have hy : ((orJunction w).embedding.cells p).2.val = origin w-4*w-23+p.2.val := rfl
  simp only [OrExit,hx,hy] at he
  rw [hx]
  rcases he with ⟨hAx,hAy⟩ | ⟨hBx,hBy⟩ | ⟨hCx,hCy⟩
  · have hne : origin w-4*w-17+p.1.val ≠ origin w+4 := by unfold origin at *; omega
    have hrow : p.2 = (⟨4*w+23,by omega⟩ : Fin (4*w+25)) := by
      apply Fin.ext
      change p.2.val = 4*w+23
      unfold origin at *
      omega
    have hl : (GuardStencils.junctionName (⟨4*w+21,by omega⟩ : Fin (9*w+42))
        (⟨4*w+23,by omega⟩ : Fin (4*w+25)) p).level = 2 := by
      unfold GuardStencils.junctionName
      rw [ite_eq_left hrow]
      rfl
    exact hl.trans (ite_eq_right hne).symm
  · have hj : p.1 = (⟨4*w+21,by omega⟩ : Fin (9*w+42)) := by
      apply Fin.ext
      change p.1.val = 4*w+21
      unfold origin at *
      omega
    have hrow : p.2 ≠ (⟨4*w+23,by omega⟩ : Fin (4*w+25)) := by
      intro hh
      have hv := congrArg Fin.val hh
      change p.2.val = 4*w+23 at hv
      unfold origin at *
      omega
    have hlt : p.2.val < 4*w+23 := by unfold origin at *; omega
    have hl : (GuardStencils.junctionName (⟨4*w+21,by omega⟩ : Fin (9*w+42))
        (⟨4*w+23,by omega⟩ : Fin (4*w+25)) p).level = 1 := by
      unfold GuardStencils.junctionName
      rw [ite_eq_right hrow,ite_eq_left ⟨hj,hlt⟩]
      rfl
    exact hl.trans (ite_eq_left hBx).symm
  · have hne : origin w-4*w-17+p.1.val ≠ origin w+4 := by unfold origin at *; omega
    have hrow : p.2 = (⟨4*w+23,by omega⟩ : Fin (4*w+25)) := by
      apply Fin.ext
      change p.2.val = 4*w+23
      unfold origin at *
      omega
    have hl : (GuardStencils.junctionName (⟨4*w+21,by omega⟩ : Fin (9*w+42))
        (⟨4*w+23,by omega⟩ : Fin (4*w+25)) p).level = 2 := by
      unfold GuardStencils.junctionName
      rw [ite_eq_left hrow]
      rfl
    exact hl.trans (ite_eq_right hne).symm

end PushPuzzle.PushS.FiniteGateStencils
