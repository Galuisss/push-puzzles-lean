/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.InWalkingGeometry
public import PushFS.Gadgets.Wires.Chain.AxisGeometry
public import PushFS.Gadgets.Wires.Catalog
public import PushFS.StaticPlacement

/-! Actual rail/sink classification of the full physical L connector, including both far boundary ports. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.In

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

def axisName (p : C m n) : AxisTrack :=
  if p.1.val=10 ∧ p.2.val=10 then .sink 10 10
  else if p.2.val=10 ∧ 10<p.1.val then .horizontal 10
  else if p.1.val=10 ∧ 10<p.2.val then .vertical 10
  else .outside

/-- At every actual horizontal rail coordinate a genuine north or south wall blocks transverse motion. -/
private theorem horizontal_guard (goals : Finset (C m n)) (x : Fin (m+63)) (hx : 10<x.val) :
    (x,⟨9,by omega⟩)∈(board m n hm hn goals).walls ∨ (x,⟨11,by omega⟩)∈(board m n hm hn goals).walls := by
  by_cases ht : x.val<45
  · let z : Fin 45 := ⟨x.val,ht⟩
    have check : ∀ z : Fin 45, 10<z.val → Turn.wallTest (z,8)=true ∨ Turn.wallTest (z,10)=true := by decide +kernel
    have he (y : Fin 41) : (turnRect m n hm hn).cells (z,y)=(x,⟨1+y.val,by have := y.isLt; omega⟩) := by
      apply Prod.ext <;> apply Fin.ext
      · change 0+x.val=x.val; omega
      · rfl
    rcases check z hx with hw|hw
    · left
      have hh := (turn_walls_agree m n hm hn goals (z,8)).mpr ((Turn.template.mem_walls _).mpr hw)
      rw [he] at hh
      exact hh
    · right
      have hh := (turn_walls_agree m n hm hn goals (z,10)).mpr ((Turn.template.mem_walls _).mpr hw)
      rw [he] at hh
      exact hh
  · let z : Fin (m+25) := ⟨m+62-x.val,by have := x.isLt; omega⟩
    have he (y : Fin 21) : (inEmbed m n hm hn).cells (z,y)=(x,⟨20-y.val,by have := y.isLt; omega⟩) := by
      apply Prod.ext <;> apply Fin.ext
      · rw [in_x]
        change 38+(m+24-(m+62-x.val))=x.val
        have := x.isLt
        omega
      · exact in_y m n hm hn (z,y)
    rcases Tail.rail_guard m hm z with hw|hw
    · right
      have hh := (in_walls_agree m n hm hn goals (z,9)).mpr hw
      rw [he] at hh
      exact hh
    · left
      have hh := (in_walls_agree m n hm hn goals (z,11)).mpr hw
      rw [he] at hh
      exact hh

/-- The actual vertical arm likewise retains a genuine west or east wall at every rail coordinate. -/
private theorem vertical_guard (goals : Finset (C m n)) (y : Fin (n+44)) (hy : 10<y.val) :
    (⟨9,by omega⟩,y)∈(board m n hm hn goals).walls ∨ (⟨11,by omega⟩,y)∈(board m n hm hn goals).walls := by
  by_cases ht : y.val≤41
  · let z : Fin 41 := ⟨y.val-1,by omega⟩
    have check : ∀ z : Fin 41, 9≤z.val → Turn.wallTest (9,z)=true := by decide +kernel
    have he : (turnRect m n hm hn).cells (9,z)=(⟨9,by omega⟩,y) := by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · change 1+(y.val-1)=y.val
        omega
    left
    have hh := (turn_walls_agree m n hm hn goals (9,z)).mpr ((Turn.template.mem_walls _).mpr (check z (by dsimp [z]; omega)))
    exact he ▸ hh
  · let z : Fin (n+5) := ⟨y.val-39,by have := y.isLt; omega⟩
    have he (x : Fin 21) : (outEmbed m n hm hn).cells (z,x)=(⟨20-x.val,by have := x.isLt; omega⟩,y) := by
      apply Prod.ext <;> apply Fin.ext
      · exact out_x m n hm hn (z,x)
      · change 39+(y.val-39)=y.val
        omega
    rcases Chain.rail_guard n hn z with hw|hw
    · right
      have hh := (out_walls_agree m n hm hn goals (z,9)).mpr hw
      rw [he] at hh
      exact hh
    · left
      have hh := (out_walls_agree m n hm hn goals (z,11)).mpr hw
      rw [he] at hh
      exact hh

/-- A horizontal physical displacement keeps its actual row, even at either exterior port. -/
private theorem horizontal_displacement (goals : Finset (C m n)) {p q : C m n}
    (hy : p.2.val=10) (hx : 10<p.1.val) (hd : Displacement (board m n hm hn goals) p q) :
    q.2.val=10 ∧ 10≤q.1.val := by
  obtain ⟨_,d,rear,hr,hq,hrw,hqw⟩ := hd
  have hg := horizontal_guard m n hm hn goals p.1 hx
  cases d with
  | east => simp only [Adjacent] at hq; constructor <;> omega
  | west => simp only [Adjacent] at hq; constructor <;> omega
  | north =>
    have hdest : q=(p.1,⟨9,by omega⟩) := by apply Prod.ext; exact hq.1; apply Fin.ext; change q.2.val=9; simp only [Adjacent] at hq; omega
    have hrear : rear=(p.1,⟨11,by omega⟩) := by apply Prod.ext; exact hr.1.symm; apply Fin.ext; change rear.2.val=11; simp only [Adjacent] at hr; omega
    rcases hg with hg|hg
    · exact False.elim (hqw (hdest ▸ hg))
    · exact False.elim (hrw (hrear ▸ hg))
  | south =>
    have hdest : q=(p.1,⟨11,by omega⟩) := by apply Prod.ext; exact hq.1; apply Fin.ext; change q.2.val=11; simp only [Adjacent] at hq; omega
    have hrear : rear=(p.1,⟨9,by omega⟩) := by apply Prod.ext; exact hr.1.symm; apply Fin.ext; change rear.2.val=9; simp only [Adjacent] at hr; omega
    rcases hg with hg|hg
    · exact False.elim (hrw (hrear ▸ hg))
    · exact False.elim (hqw (hdest ▸ hg))

private theorem vertical_displacement (goals : Finset (C m n)) {p q : C m n}
    (hx : p.1.val=10) (hy : 10<p.2.val) (hd : Displacement (board m n hm hn goals) p q) :
    q.1.val=10 ∧ 10≤q.2.val := by
  obtain ⟨_,d,rear,hr,hq,hrw,hqw⟩ := hd
  have hg := vertical_guard m n hm hn goals p.2 hy
  cases d with
  | north => simp only [Adjacent] at hq; constructor <;> omega
  | south => simp only [Adjacent] at hq; constructor <;> omega
  | east =>
    have hdest : q=(⟨11,by omega⟩,p.2) := by apply Prod.ext; apply Fin.ext; change q.1.val=11; simp only [Adjacent] at hq; omega; exact hq.2
    have hrear : rear=(⟨9,by omega⟩,p.2) := by apply Prod.ext; apply Fin.ext; change rear.1.val=9; simp only [Adjacent] at hr; omega; exact hr.2.symm
    rcases hg with hg|hg
    · exact False.elim (hrw (hrear ▸ hg))
    · exact False.elim (hqw (hdest ▸ hg))
  | west =>
    have hdest : q=(⟨9,by omega⟩,p.2) := by apply Prod.ext; apply Fin.ext; change q.1.val=9; simp only [Adjacent] at hq; omega; exact hq.2
    have hrear : rear=(⟨11,by omega⟩,p.2) := by apply Prod.ext; apply Fin.ext; change rear.1.val=11; simp only [Adjacent] at hr; omega; exact hr.2.symm
    rcases hg with hg|hg
    · exact False.elim (hqw (hdest ▸ hg))
    · exact False.elim (hrw (hrear ▸ hg))

/-- The actual shared corner is an immobile sink. -/
private theorem corner_immobile (goals : Finset (C m n)) (p : C m n)
    (hp : p.1.val=10 ∧ p.2.val=10) :
    ∀ q, ¬Displacement (board m n hm hn goals) p q := by
  have he : (turnRect m n hm hn).cells ((10,9) : Turn.C)=p := by
    apply Prod.ext <;> apply Fin.ext
    · change 10=p.1.val; omega
    · change 10=p.2.val; omega
  intro q hd
  rw [← he] at hd
  obtain ⟨q',_,hq⟩ := GridEmbedding.displacement_preimage 0 1 (by omega : 0+45≤m+63)
    (by omega : 1+41≤n+44) (turn_walls_agree m n hm hn goals) (by decide : Interior ((10,9) : Turn.C)) hd
  exact Turn.corner_immobile ∅ q' hq

/-- All actual active-source displacements stay on one rail or enter the genuine singleton sink. -/
theorem strong_displacement (goals : Finset (C m n)) {p q : C m n}
    (hp : axisName m n p≠.outside) (hd : Displacement (board m n hm hn goals) p q) :
    (axisName m n p).Strong (axisName m n q) := by
  by_cases hc : p.1.val=10 ∧ p.2.val=10
  · exact False.elim (corner_immobile m n hm hn goals p hc q hd)
  · by_cases hh : p.2.val=10 ∧ 10<p.1.val
    · have hq := horizontal_displacement m n hm hn goals hh.1 hh.2 hd
      have hnp : axisName m n p=.horizontal 10 := by unfold axisName; rw [ite_eq_right hc,ite_eq_left hh]
      by_cases he : q.1.val=10
      · have hnq : axisName m n q=.sink 10 10 := by unfold axisName; rw [ite_eq_left ⟨he,hq.1⟩]
        exact Or.inr ⟨by rw [hnp]; trivial,by rw [hnq]; trivial⟩
      · have hnq : axisName m n q=.horizontal 10 := by
          unfold axisName
          rw [ite_eq_right (by omega),ite_eq_left ⟨hq.1,show 10<q.1.val by omega⟩]
        exact Or.inl (hnp.trans hnq.symm)
    · have hv : p.1.val=10 ∧ 10<p.2.val := by
        by_contra hv
        apply hp
        simp only [axisName,hc,hh,hv,ite_false]
      have hq := vertical_displacement m n hm hn goals hv.1 hv.2 hd
      have hnp : axisName m n p=.vertical 10 := by unfold axisName; rw [ite_eq_right hc,ite_eq_right hh,ite_eq_left hv]
      by_cases he : q.2.val=10
      · have hnq : axisName m n q=.sink 10 10 := by unfold axisName; rw [ite_eq_left ⟨hq.1,he⟩]
        exact Or.inr ⟨by rw [hnp]; trivial,by rw [hnq]; trivial⟩
      · have hnq : axisName m n q=.vertical 10 := by
          unfold axisName
          rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left ⟨hq.1,show 10<q.2.val by omega⟩]
        exact Or.inl (hnp.trans hnq.symm)

/-- Full finite-board rail/sink classification of the true union stencil. -/
def classifier (goals : Finset (C m n)) : AxisClassifier (board m n hm hn goals) where
  name := axisName m n
  supported p := by unfold axisName; split_ifs <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    by_cases hp : axisName m n p=.outside
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside hp)
    · exact of_decide_eq_true (AxisTrack.allowed_of_strong ((AxisTrack.strongAllowed_iff _ _ _).mpr
        (strong_displacement m n hm hn goals hp hd)))

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
