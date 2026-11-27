/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGatePlacedContract

/-! Three literal probe cells distinguish the complete normal inventories of each placed thick gate. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateNormalSeparation

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateMacros FiniteGatePlacedContract

variable {W H : ℕ}

attribute [local irreducible] side

/-- A literal normal slot reads exactly one gate bit from the complete unlabelled inventory. -/
theorem and_probe_a (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    point w 2 0 ∈ andBoxes w a b c ↔ a = true := by
  constructor
  · intro hm
    cases a with
    | true => rfl
    | false =>
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hpx := congrArg (fun p => p.1.val) he
      have hpy := congrArg (fun p => p.2.val) he
      have hb := Bool.toNat_le b
      have hc := Bool.toNat_le c
      cases l <;> simp only [andCell,andPoint,point,Bool.toNat_false] at hpx hpy
      all_goals unfold origin at *; omega
  · intro ha
    subst a
    have he : andCell w true b c .triggerA = point w 2 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell,andPoint,point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA,Finset.mem_univ _,rfl⟩

/-- A literal normal slot reads exactly one gate bit from the complete unlabelled inventory. -/
theorem and_probe_b (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    point w 3 2 ∈ andBoxes w a b c ↔ b = true := by
  constructor
  · intro hm
    cases b with
    | true => rfl
    | false =>
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hpx := congrArg (fun p => p.1.val) he
      have hpy := congrArg (fun p => p.2.val) he
      have ha := Bool.toNat_le a
      have hc := Bool.toNat_le c
      cases l <;> simp only [andCell,andPoint,point,Bool.toNat_false] at hpx hpy
      all_goals unfold origin at *; omega
  · intro hb
    subst b
    have he : andCell w a true c (.branchB 0) = point w 3 2 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell,andPoint,point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨(.branchB 0),Finset.mem_univ _,rfl⟩

/-- A literal normal slot reads exactly one gate bit from the complete unlabelled inventory. -/
theorem and_probe_c (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    point w (w+4) 0 ∈ andBoxes w a b c ↔ c = true := by
  constructor
  · intro hm
    cases c with
    | true => rfl
    | false =>
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hpx := congrArg (fun p => p.1.val) he
      have hpy := congrArg (fun p => p.2.val) he
      have ha := Bool.toNat_le a
      have hb := Bool.toNat_le b
      cases l <;> simp only [andCell,andPoint,point,Bool.toNat_false] at hpx hpy
      all_goals unfold origin at *; omega
  · intro hc
    subst c
    have he : andCell w a b true (.branchC 0) = point w (w+4) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell,andPoint,point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨(.branchC 0),Finset.mem_univ _,rfl⟩

/-- A literal normal slot reads exactly one gate bit from the complete unlabelled inventory. -/
theorem or_probe_a (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    point w 2 0 ∈ orBoxes w a b c ↔ a = true := by
  constructor
  · intro hm
    cases a with
    | true => rfl
    | false =>
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hpx := congrArg (fun p => p.1.val) he
      have hpy := congrArg (fun p => p.2.val) he
      have hb := Bool.toNat_le b
      have hc := Bool.toNat_le c
      cases l <;> simp only [orCell,orPoint,point,Bool.toNat_false] at hpx hpy
      all_goals unfold origin at *; omega
  · intro ha
    subst a
    have he : orCell w true b c .triggerA = point w 2 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell,orPoint,point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA,Finset.mem_univ _,rfl⟩

/-- A literal normal slot reads exactly one gate bit from the complete unlabelled inventory. -/
theorem or_probe_b (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    point w 4 2 ∈ orBoxes w a b c ↔ b = true := by
  constructor
  · intro hm
    cases b with
    | true => rfl
    | false =>
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hpx := congrArg (fun p => p.1.val) he
      have hpy := congrArg (fun p => p.2.val) he
      have ha := Bool.toNat_le a
      have hc := Bool.toNat_le c
      cases l <;> simp only [orCell,orPoint,point,Bool.toNat_false] at hpx hpy
      all_goals unfold origin at *; omega
  · intro hb
    subst b
    have he : orCell w a true c (.branchB 0) = point w 4 2 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell,orPoint,point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨(.branchB 0),Finset.mem_univ _,rfl⟩

/-- A literal normal slot reads exactly one gate bit from the complete unlabelled inventory. -/
theorem or_probe_c (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    point w (w+5) 0 ∈ orBoxes w a b c ↔ c = true := by
  constructor
  · intro hm
    cases c with
    | true => rfl
    | false =>
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hpx := congrArg (fun p => p.1.val) he
      have hpy := congrArg (fun p => p.2.val) he
      have ha := Bool.toNat_le a
      have hb := Bool.toNat_le b
      cases l <;> simp only [orCell,orPoint,point,Bool.toNat_false] at hpx hpy
      all_goals unfold origin at *; omega
  · intro hc
    subst c
    have he : orCell w a b true (.branchC 0) = point w (w+5) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell,orPoint,point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨(.branchC 0),Finset.mem_univ _,rfl⟩

private theorem mapped_probe {N M : ℕ} (e : GridEmbedding N M W H)
    (stock : Finset (Cell N M)) (extra : Finset (Cell W H)) (p : Cell N M)
    (hp : e.cells p ∉ extra) : e.cells p ∈ stock.map e.cells ∪ extra ↔ p ∈ stock := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hm
      exact e.cells.injective he ▸ hq
    · exact False.elim (hp hm)
  · intro hm
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p,hm,rfl⟩)

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The three probe cells distinguish every placed complete normal inventory. -/
private theorem and_normal_injective (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (extra : Finset (Cell W H))
    (ha : e.cells (point w 2 0) ∉ extra) (hb : e.cells (point w 3 2) ∉ extra)
    (hc : e.cells (point w (w+4) 0) ∉ extra) :
    Function.Injective (fun s : Gates.Signals => (andBoxes w s.left s.upper s.right).map e.cells ∪ extra) := by
  intro i f he
  have hA (s : Gates.Signals) : e.cells (point w 2 0) ∈
      (andBoxes w s.left s.upper s.right).map e.cells ∪ extra ↔ s.left = true :=
    (mapped_probe e _ extra _ ha).trans (and_probe_a w hw s.left s.upper s.right)
  have hB (s : Gates.Signals) : e.cells (point w 3 2) ∈
      (andBoxes w s.left s.upper s.right).map e.cells ∪ extra ↔ s.upper = true :=
    (mapped_probe e _ extra _ hb).trans (and_probe_b w hw s.left s.upper s.right)
  have hC (s : Gates.Signals) : e.cells (point w (w+4) 0) ∈
      (andBoxes w s.left s.upper s.right).map e.cells ∪ extra ↔ s.right = true :=
    (mapped_probe e _ extra _ hc).trans (and_probe_c w hw s.left s.upper s.right)
  dsimp only at he
  have ha' : i.left = f.left := bool_eq_of_true_iff (by rw [← hA i,← hA f,he])
  have hb' : i.upper = f.upper := bool_eq_of_true_iff (by rw [← hB i,← hB f,he])
  have hc' : i.right = f.right := bool_eq_of_true_iff (by rw [← hC i,← hC f,he])
  cases i
  cases f
  simp only [Gates.Signals.mk.injEq]
  exact ⟨ha',hb',hc'⟩

/-- The three probe cells distinguish every placed complete normal inventory. -/
private theorem or_normal_injective (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (extra : Finset (Cell W H))
    (ha : e.cells (point w 2 0) ∉ extra) (hb : e.cells (point w 4 2) ∉ extra)
    (hc : e.cells (point w (w+5) 0) ∉ extra) :
    Function.Injective (fun s : Gates.Signals => (orBoxes w s.left s.upper s.right).map e.cells ∪ extra) := by
  intro i f he
  have hA (s : Gates.Signals) : e.cells (point w 2 0) ∈
      (orBoxes w s.left s.upper s.right).map e.cells ∪ extra ↔ s.left = true :=
    (mapped_probe e _ extra _ ha).trans (or_probe_a w hw s.left s.upper s.right)
  have hB (s : Gates.Signals) : e.cells (point w 4 2) ∈
      (orBoxes w s.left s.upper s.right).map e.cells ∪ extra ↔ s.upper = true :=
    (mapped_probe e _ extra _ hb).trans (or_probe_b w hw s.left s.upper s.right)
  have hC (s : Gates.Signals) : e.cells (point w (w+5) 0) ∈
      (orBoxes w s.left s.upper s.right).map e.cells ∪ extra ↔ s.right = true :=
    (mapped_probe e _ extra _ hc).trans (or_probe_c w hw s.left s.upper s.right)
  dsimp only at he
  have ha' : i.left = f.left := bool_eq_of_true_iff (by rw [← hA i,← hA f,he])
  have hb' : i.upper = f.upper := bool_eq_of_true_iff (by rw [← hB i,← hB f,he])
  have hc' : i.right = f.right := bool_eq_of_true_iff (by rw [← hC i,← hC f,he])
  cases i
  cases f
  simp only [Gates.Signals.mk.injEq]
  exact ⟨ha',hb',hc'⟩

/-- The actual trigger frames already exclude every outside box from the three distinguishing slots. -/
theorem and_frames_probes_avoid (w : ℕ)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : AndFrames w e B extra) :
    e.cells (point w 2 0) ∉ extra ∧ e.cells (point w 3 2) ∉ extra ∧
      e.cells (point w (w+4) 0) ∉ extra := by
  have hA : point w 2 0 ∈ FiniteGateAAmbient.triggerBackwardActive w := by
    dsimp [FiniteGateAAmbient.triggerBackwardActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp [point]
  have hB : point w 3 2 ∈ FiniteGateBAmbient.backwardActive w 3 (by omega) := by
    apply Finset.mem_map.mpr
    refine ⟨((point w 0 2).2,(point w 3 0).1),?_,rfl⟩
    dsimp [FiniteGateBAmbient.downLocalActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp
  have hC : point w (w+4) 0 ∈ FiniteGateCAmbient.forwardActive w 6 (by omega) := by
    dsimp [FiniteGateCAmbient.forwardActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp [point]
  exact ⟨fun hp => (F.a_backward false false).fixed_avoids _ hA (Finset.mem_union_right _ hp),
    fun hp => (F.b_backward false false).fixed_avoids _ hB (Finset.mem_union_right _ hp),
    fun hp => (F.c_forward false false).fixed_avoids _ hC (Finset.mem_union_right _ hp)⟩

/-- Every normal signal vector has a distinct physical inventory under the existing narrow frames. -/
theorem and_frames_normal_injective (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : AndFrames w e B extra) :
    Function.Injective (fun s : Gates.Signals => (andBoxes w s.left s.upper s.right).map e.cells ∪ extra) := by
  obtain ⟨ha,hb,hc⟩ := and_frames_probes_avoid w e F
  exact and_normal_injective w hw e extra ha hb hc

/-- The actual trigger frames already exclude every outside box from the three distinguishing slots. -/
private theorem or_frames_probes_avoid (w : ℕ)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : OrFrames w e B extra) :
    e.cells (point w 2 0) ∉ extra ∧ e.cells (point w 4 2) ∉ extra ∧
      e.cells (point w (w+5) 0) ∉ extra := by
  have hA : point w 2 0 ∈ FiniteGateOrAAmbient.backwardActive w := by
    dsimp [FiniteGateOrAAmbient.backwardActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp [point]
  have hB : point w 4 2 ∈ FiniteGateBAmbient.backwardActive w 4 (by omega) := by
    apply Finset.mem_map.mpr
    refine ⟨((point w 0 2).2,(point w 4 0).1),?_,rfl⟩
    dsimp [FiniteGateBAmbient.downLocalActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp
  have hC : point w (w+5) 0 ∈ FiniteGateCAmbient.forwardActive w 7 (by omega) := by
    dsimp [FiniteGateCAmbient.forwardActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp [point]
  exact ⟨fun hp => (F.a_backward false false).fixed_avoids _ hA (Finset.mem_union_right _ hp),
    fun hp => (F.b_backward false false).fixed_avoids _ hB (Finset.mem_union_right _ hp),
    fun hp => (F.c_forward false false).fixed_avoids _ hC (Finset.mem_union_right _ hp)⟩

/-- Every normal signal vector has a distinct physical inventory under the existing narrow frames. -/
theorem or_frames_normal_injective (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : OrFrames w e B extra) :
    Function.Injective (fun s : Gates.Signals => (orBoxes w s.left s.upper s.right).map e.cells ∪ extra) := by
  obtain ⟨ha,hb,hc⟩ := or_frames_probes_avoid w e F
  exact or_normal_injective w hw e extra ha hb hc

end PushPuzzle.PushS.FiniteGateNormalSeparation
