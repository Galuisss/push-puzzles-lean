/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineFrame
public import PushS.FiniteAtomFrames
import Mathlib.Tactic.FinCases

/-! Real same-stock outer-lane and flip-mouth walks use only literal ambient free cells. -/

public section
namespace PushPuzzle.PushS.FiniteRouting.Line.NormalWalking

open PushFS

variable {w W H : ℕ} {atoms : List Atom} {B : Board W H} {stock : Finset (Cell W H)}

attribute [local irreducible] width height

private theorem rectangle_walk (e : GridEmbedding (width w atoms) (height w) W H)
    (hstock : Disjoint stock B.walls) (p q : Cell (width w atoms) (height w))
    (hf : ∀ r, min p.1.val q.1.val ≤ r.1.val → r.1.val ≤ max p.1.val q.1.val →
      min p.2.val q.2.val ≤ r.2.val → r.2.val ≤ max p.2.val q.2.val → Free B stock (e.cells r)) :
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells q,stock⟩ := by
  apply FiniteAtomFrames.walk_ambient p q e
  refine ⟨?_,?_,hstock⟩
  · intro r hr
    obtain ⟨hx,hx',hy,hy'⟩ := (FiniteAtomFrames.mem_walkActive p q r).mp hr
    exact (hf r hx hx' hy hy').1
  · intro r hr
    obtain ⟨hx,hx',hy,hy'⟩ := (FiniteAtomFrames.mem_walkActive p q r).mp hr
    exact (hf r hx hx' hy hy').2

theorem outer_walk (e : GridEmbedding (width w atoms) (height w) W H)
    (hstock : Disjoint stock B.walls)
    (hf : ∀ (north : Bool) (x : Fin (width w atoms)), FiniteTools.radius w+1 ≤ x.val →
      x.val ≤ FiniteTools.radius w+span w atoms → Free B stock (e.cells (outerCell w atoms north x)))
    (north : Bool) (x y : Fin (width w atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+span w atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w atoms) :
    Reachable B (some 1) ⟨e.cells (outerCell w atoms north x),stock⟩
      ⟨e.cells (outerCell w atoms north y),stock⟩ := by
  apply rectangle_walk e hstock
  intro r hrx hrx' hry hry'
  have he : r = outerCell w atoms north r.1 := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp [outerCell] at hry hry' ⊢
      omega
  rw [he]
  apply hf north r.1
  · dsimp [outerCell] at hrx hrx'
    omega
  · dsimp [outerCell] at hrx hrx'
    omega

variable {pre post : List Atom} {above : Bool}

private def MouthFree (e : GridEmbedding (width w (pre++ .flip::post)) (height w) W H)
    (B : Board W H) (stock : Finset (Cell W H)) (above : Bool) : Prop :=
  ∀ (j : Fin 2) (p : Cell (width w (pre++ .flip::post)) (height w)), p.1 = flipMouthX w pre post j →
    FiniteTools.radius w-w-1 ≤ p.2.val → p.2.val ≤ FiniteTools.radius w+w+1 →
    (if flipMouthNorth above pre j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) →
    Free B stock (e.cells p)

private theorem mouth_walk (e : GridEmbedding (width w (pre++ .flip::post)) (height w) W H)
    (hstock : Disjoint stock B.walls) (hf : MouthFree e B stock above) (j : Fin 2) :
    Reachable B (some 1)
      ⟨e.cells (outerCell w _ (flipMouthNorth above pre j) (flipMouthX w pre post j)),stock⟩
      ⟨e.cells (flipMouthX w pre post j,workY w),stock⟩ ∧
    Reachable B (some 1)
      ⟨e.cells (flipMouthX w pre post j,workY w),stock⟩
      ⟨e.cells (outerCell w _ (flipMouthNorth above pre j) (flipMouthX w pre post j)),stock⟩ := by
  have hfree (p : Cell (width w (pre++ .flip::post)) (height w))
      (hx : min (flipMouthX w pre post j).val (flipMouthX w pre post j).val ≤ p.1.val)
      (hx' : p.1.val ≤ max (flipMouthX w pre post j).val (flipMouthX w pre post j).val)
      (hy : min (laneY w (flipMouthNorth above pre j)).val (workY w).val ≤ p.2.val)
      (hy' : p.2.val ≤ max (laneY w (flipMouthNorth above pre j)).val (workY w).val) :
      Free B stock (e.cells p) := by
    apply hf j p (Fin.ext (by omega))
    all_goals cases hs : flipMouthNorth above pre j <;>
      simp only [hs] at hy hy' ⊢ <;> dsimp [laneY,workY] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  constructor
  · apply rectangle_walk e hstock
    exact hfree
  · apply rectangle_walk e hstock
    intro p hx hx' hy hy'
    exact hfree p hx hx' (by simpa only [outerCell,min_comm] using hy) (by simpa only [outerCell,max_comm] using hy')

private theorem mouth_cross (e : GridEmbedding (width w (pre++ .flip::post)) (height w) W H)
    (hstock : Disjoint stock B.walls) (hf : MouthFree e B stock above) (j : Fin 2) :
    Reachable B (some 1)
      ⟨e.cells (outerCell w _ (flipMouthNorth above pre j) (flipMouthX w pre post j)),stock⟩
      ⟨e.cells (outerCell w _ (flipMouthNorth above pre j.rev) (flipMouthX w pre post j.rev)),stock⟩ := by
  have hmid : Reachable B (some 1)
      ⟨e.cells (flipMouthX w pre post j,workY w),stock⟩
      ⟨e.cells (flipMouthX w pre post j.rev,workY w),stock⟩ := by
    apply rectangle_walk e hstock
    intro p hx hx' hy hy'
    dsimp only at hx hx' hy hy'
    have hrow : p.2 = workY w := Fin.ext (by omega)
    have hchoice : p.1 = flipMouthX w pre post 0 ∨ p.1 = flipMouthX w pre post 1 := by
      by_cases h0 : p.1.val = FiniteTools.radius w+span w pre+w+1
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext (by fin_cases j <;> simp [flipMouthX,Fin.rev] at hx hx' ⊢ <;> omega))
    rcases hchoice with h | h
    all_goals apply hf _ p h
    all_goals rw [hrow]
    all_goals dsimp [workY]
    all_goals first | omega | (split <;> omega)
  exact (mouth_walk e hstock hf j).1.trans (hmid.trans (mouth_walk e hstock hf j.rev).2)

private theorem connected (e : GridEmbedding (width w (pre++ .flip::post)) (height w) W H)
    (hstock : Disjoint stock B.walls)
    (ho : ∀ (north : Bool) (x : Fin (width w (pre++ .flip::post))), FiniteTools.radius w+1 ≤ x.val →
      x.val ≤ FiniteTools.radius w+span w (pre++ .flip::post) → Free B stock (e.cells (outerCell w _ north x)))
    (hm : MouthFree e B stock above) (north north' : Bool) (x y : Fin (width w (pre++ .flip::post)))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+span w (pre++ .flip::post))
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w (pre++ .flip::post)) :
    Reachable B (some 1) ⟨e.cells (outerCell w _ north x),stock⟩ ⟨e.cells (outerCell w _ north' y),stock⟩ := by
  by_cases hn : north = north'
  · subst north'
    exact outer_walk e hstock ho north x y hx hx' hy hy'
  · let j : Fin 2 := if north = exitSide above pre then 0 else 1
    have hj : flipMouthNorth above pre j = north := by
      cases north <;> cases hs : exitSide above pre <;> simp [j,flipMouthNorth,hs]
    have hj' : flipMouthNorth above pre j.rev = north' := by
      rw [flipMouthNorth_rev,hj]
      cases north <;> cases north' <;> simp_all
    have hcross := mouth_cross e hstock hm j
    rw [hj,hj'] at hcross
    have hmouth (a : Fin 2) : FiniteTools.radius w+1 ≤ (flipMouthX w pre post a).val ∧
        (flipMouthX w pre post a).val ≤ FiniteTools.radius w+span w (pre++ .flip::post) := by
      have ha := a.isLt
      dsimp [flipMouthX]
      simp only [span_append,span_cons,Atom.span]
      omega
    exact (outer_walk e hstock ho north x _ hx hx' (hmouth j).1 (hmouth j).2).trans
      (hcross.trans (outer_walk e hstock ho north' _ y (hmouth j.rev).1 (hmouth j.rev).2 hy hy'))

private theorem connected_of_eq (e : GridEmbedding (width w atoms) (height w) W H)
    (h : atoms = pre++ .flip::post) (hstock : Disjoint stock B.walls)
    (ho : ∀ (north : Bool) (x : Fin (width w atoms)), FiniteTools.radius w+1 ≤ x.val →
      x.val ≤ FiniteTools.radius w+span w atoms → Free B stock (e.cells (outerCell w atoms north x)))
    (hm : ∀ (j : Fin 2) (p : Cell (width w atoms) (height w)),
      p.1.val = FiniteTools.radius w+span w pre+w+1+j.val →
      FiniteTools.radius w-w-1 ≤ p.2.val → p.2.val ≤ FiniteTools.radius w+w+1 →
      (if flipMouthNorth above pre j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) →
      Free B stock (e.cells p)) (north north' : Bool) (x y : Fin (width w atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+span w atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w atoms) :
    Reachable B (some 1) ⟨e.cells (outerCell w atoms north x),stock⟩ ⟨e.cells (outerCell w atoms north' y),stock⟩ := by
  subst atoms
  apply connected (above := above) e hstock ho _ north north' x y hx hx' hy hy'
  intro j p he hp hp' hside
  apply hm j p _ hp hp' hside
  exact congrArg Fin.val he

theorem program_connected (length : ℕ) (switch above : Bool)
    (e : GridEmbedding (width w (program w length switch)) (height w) W H)
    (hstock : Disjoint stock B.walls)
    (ho : ∀ (north : Bool) (x : Fin (width w (program w length switch))), FiniteTools.radius w+1 ≤ x.val →
      x.val ≤ FiniteTools.radius w+span w (program w length switch) → Free B stock (e.cells (outerCell w _ north x)))
    (hm : ∀ (j : Fin 2) (p : Cell (width w (program w length switch)) (height w)),
      p.1.val = FiniteTools.radius w+2*buffer w+w+1+j.val →
      FiniteTools.radius w-w-1 ≤ p.2.val → p.2.val ≤ FiniteTools.radius w+w+1 →
      (if flipMouthNorth above [.line (buffer w)] j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) →
      Free B stock (e.cells p)) (north north' : Bool) (x y : Fin (width w (program w length switch)))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+span w (program w length switch))
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+span w (program w length switch)) :
    Reachable B (some 1) ⟨e.cells (outerCell w _ north x),stock⟩ ⟨e.cells (outerCell w _ north' y),stock⟩ := by
  obtain ⟨post,hpost⟩ := program_contains_flip w length switch
  apply connected_of_eq (pre := [.line (buffer w)]) (above := above) e hpost hstock ho _ north north' x y hx hx' hy hy'
  intro j p he hp hp' hs
  apply hm j p _ hp hp' hs
  simpa only [span_cons,span_nil,Atom.span,Nat.add_zero] using he

end PushPuzzle.PushS.FiniteRouting.Line.NormalWalking
