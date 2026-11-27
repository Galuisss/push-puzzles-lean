/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateOutputReturn
public import PushS.FiniteFrameComposition

/-! Narrow ambient frames for entering a roofed mouth, pushing its boundary, and returning. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteMouthFrames

open PushFS FiniteGateOutputReturn

variable {w h W H : ℕ}

/-- The used horizontal row interval and the single cell above its left mouth. -/
def rightActive (mouth dst : Fin w) (upper row : Fin h) : Finset (Cell w h) :=
  Finset.univ.filter fun p =>
    (p.2 = row ∧ mouth.val ≤ p.1.val ∧ p.1.val ≤ dst.val) ∨ p = (mouth, upper)

@[simp] theorem mem_rightActive (mouth dst : Fin w) (upper row : Fin h) (p : Cell w h) :
    p ∈ rightActive mouth dst upper row ↔
      (p.2 = row ∧ mouth.val ≤ p.1.val ∧ p.1.val ≤ dst.val) ∨ p = (mouth, upper) := by
  simp only [rightActive, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Enter the real left mouth, push a single boundary box right, and return to the same mouth. -/
private theorem right_ambient (mouth support src dst : Fin w) (upper row : Fin h)
    (hentry : Adjacent .south (mouth, upper) (mouth, row))
    (hax : Adjacent .east (support, row) (src, row))
    (hxd : Adjacent .east (src, row) (dst, row)) (hmouth : mouth.val ≤ support.val)
    (e : GridEmbedding w h W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (rightActive mouth dst upper row) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨(mouth, upper), {(src, row)}⟩)
      (e.extend fixed ⟨(mouth, upper), {(dst, row)}⟩) := by
  let A := FiniteWireFrame.board (rightActive mouth dst upper row) ∅
  have hax' := hax
  have hxd' := hxd
  simp only [Adjacent] at hax' hxd'
  have hfloor (x : Fin w) (hx : mouth.val ≤ x.val) (hx' : x.val ≤ dst.val) : (x, row) ∉ A.walls := by
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    exact (mem_rightActive _ _ _ _ _).mpr (Or.inl ⟨rfl, hx, hx'⟩)
  have hsrc : (src, row) ∉ A.walls := hfloor src (by omega) (by omega)
  have hdest : Free A {(src, row)} (dst, row) :=
    ⟨hfloor dst (by omega) (by omega), by simpa only [Finset.mem_singleton] using hxd.ne.symm⟩
  have hupper : Free A {(src, row)} (mouth, upper) := by
    constructor
    · apply (FiniteWireFrame.floor_iff _ _ _).mpr
      exact (mem_rightActive _ _ _ _ _).mpr (Or.inr rfl)
    · intro hm
      have he := Finset.mem_singleton.mp hm
      have hy : upper = row := congrArg Prod.snd he
      exact hentry.ne (by rw [hy])
  have hrow : ∀ x : Fin w, mouth.val ≤ x.val → x.val < src.val → Free A {(src, row)} (x, row) := by
    intro x hx hx'
    refine ⟨hfloor x hx (by omega), ?_⟩
    intro hm
    have he := Finset.mem_singleton.mp hm
    have hxe : x.val = src.val := congrArg (fun p : Cell w h => p.1.val) he
    omega
  have hr := push_right_via_mouth (Finset.disjoint_singleton_left.mpr hsrc)
    mouth support src dst upper row hentry hentry.reverse hax hxd hmouth
    (Finset.mem_singleton_self _) hdest hupper hrow
  have hlocal : Reachable A (some 1) ⟨(mouth, upper), {(src, row)}⟩ ⟨(mouth, upper), {(dst, row)}⟩ := by
    simpa only [Finset.erase_singleton, Finset.insert_empty] using hr
  exact F.replay hlocal

/-- A prepared single trigger restores the entire target inventory through the narrow mouth frame. -/
theorem right_restore_ambient (mouth support src dst : Fin w) (upper row : Fin h)
    (hentry : Adjacent .south (mouth, upper) (mouth, row))
    (hax : Adjacent .east (support, row) (src, row))
    (hxd : Adjacent .east (src, row) (dst, row)) (hmouth : mouth.val ≤ support.val)
    (target : Finset (Cell w h)) (htarget : (dst, row) ∈ target)
    (e : GridEmbedding w h W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (rightActive mouth dst upper row) e B
      ((target.erase (dst, row)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(mouth, upper), insert (src, row) (target.erase (dst, row))⟩)
      (e.extend extra ⟨(mouth, upper), target⟩) := by
  have hr := right_ambient mouth support src dst upper row hentry hax hxd hmouth e F
  simpa only [FiniteWireFrame.extend_insert, Finset.insert_erase htarget] using hr

end PushPuzzle.PushS.FiniteMouthFrames
