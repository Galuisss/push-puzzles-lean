/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionProgram

/-! Owned terminal preparation uses only its exposed end cap in the trimmed action arena. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Action.Terminal
open PushFS Line.Terminal
open FiniteTools (radius)
attribute [local irreducible] width height

private theorem end_floor (w : ℕ) (atoms : List Atom) (above : Bool) (hspan : 0 < span w atoms)
    (d : Fin 4) :
    endCell w atoms d ∉ (macroBoard (last:=true) w atoms above).walls := by
  have hd := d.isLt
  have hp := Line.Terminal.end_floor w atoms above d
  apply (FiniteWireFrame.floor_iff _ _ _).mpr
  refine Finset.mem_filter.mpr ⟨(FiniteWireFrame.floor_iff _ _ _).mp hp,?_⟩
  by_cases hd' : d.val ≤ 2
  · apply Or.inl
    refine ⟨rfl,?_⟩
    dsimp [endCell]
    unfold FiniteTools.radius
    omega
  · apply Or.inr; apply Or.inr
    refine ⟨rfl,?_,?_⟩
    · dsimp [endCell]; unfold FiniteTools.radius; omega
    · cases hs : exitSide above atoms <;> simp [Exposed,endCell,workY]

private theorem push (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (hspan : 0 < span w atoms)
    (above q : Bool) :
    Move (macroBoard (last:=true) w atoms above) (some 1) (if q then .west else .east)
      ⟨endCell w atoms (if q then 3 else 0), cutBoxes w hw (cut w atoms q) atoms⟩
      ⟨endCell w atoms ⟨1+q.toNat, by have := Bool.toNat_le q; omega⟩,
        cutBoxes w hw (cut w atoms (!q)) atoms⟩ := by
  have hmove := FiniteWireFrame.push_named (cutCell w hw (cut w atoms q) atoms)
    (cutCell w hw (cut w atoms (!q)) atoms) (cutCell_injective w hw _ atoms)
    (cutLastLabel w atoms) (by intro l hl; rw [other w hw atoms q l hl, other w hw atoms (!q) l hl])
    (support := endCell w atoms (if q then 3 else 0)) (d := if q then .west else .east)
    ⟨end_floor w atoms above hspan _, cutBoxes_macro_floor w hw _ atoms above,
      no_box w hw atoms q (if q then 3 else 0) (by cases q <;> simp) _ rfl⟩
    (by rw [slot]; cases q <;> simp [Adjacent, endCell, radius])
    (by rw [slot, slot]; cases q <;> simp [Adjacent, endCell, radius])
    (by rw [slot]; exact end_floor w atoms above hspan _)
    (by rw [slot]; exact no_box w hw atoms q ⟨1+(!q).toNat, by have := Bool.toNat_le (!q); omega⟩ (by cases q <;> simp) _ rfl)
  rw [slot] at hmove
  exact hmove

private theorem column_free (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w) (y : Fin (height w))
    (hy : min (workY w).val (laneY w (!(exitSide above pre))).val ≤ y.val)
    (hy' : y.val ≤ max (workY w).val (laneY w (!(exitSide above pre))).val) :
    Free (macroBoard (last:=true) w (pre++[.line n]) above)
      (cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])) ((endCell w (pre++[.line n]) d).1,y) := by
  apply lift_free w _ above _ _ (Line.Terminal.column_free w hw pre n hn above q d hd ha y hy hy')
  have hn' := hn
  unfold buffer at hn'
  have hd' := d.isLt
  by_cases hdx : d.val ≤ 1
  · apply Or.inr; apply Or.inl
    dsimp [endCell]
    simp only [span_append,span_cons,span_nil,Atom.span,Nat.add_zero]
    unfold FiniteTools.radius
    omega
  · apply Or.inr; apply Or.inr
    refine ⟨rfl,?_,?_⟩
    · dsimp [endCell]; unfold FiniteTools.radius; omega
    · have hex : Exposed w (exitSide above pre) y.val := by
        cases hs : exitSide above pre <;> simp [laneY,workY,Exposed,hs] at hy hy' ⊢ <;>
          unfold FiniteTools.radius at * <;> omega
      simpa only [exitSide_append,exitSide,Atom.nextSide] using hex

private theorem end_to_outer (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w) :
    Reachable (macroBoard (last:=true) w (pre++[.line n]) above) (some 1)
      ⟨endCell w (pre++[.line n]) d, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerCell w _ (!(exitSide above pre)) (endCell w (pre++[.line n]) d).1,
        cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw _ _ above)
  exact column_free w hw pre n hn above q d hd ha

private theorem outer_to_end (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w) :
    Reachable (macroBoard (last:=true) w (pre++[.line n]) above) (some 1)
      ⟨outerCell w _ (!(exitSide above pre)) (endCell w (pre++[.line n]) d).1,
        cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨endCell w (pre++[.line n]) d, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw _ _ above)
  intro y hy hy'
  exact column_free w hw pre n hn above q d hd ha y (by simpa only [min_comm] using hy)
    (by simpa only [max_comm] using hy')

private theorem outer_tail_free (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (x : Fin (width w (pre++[.line n])))
    (hx : radius w+span w (pre++[.line n])-1 ≤ x.val)
    (hx' : x.val ≤ radius w+span w (pre++[.line n])+2) :
    Free (macroBoard (last:=true) w (pre++[.line n]) above)
      (cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n]))
      (outerCell w _ (!(exitSide above pre)) x) := by
  have hn' := hn
  unfold buffer at hn'
  have hspan : 2 ≤ span w (pre++[.line n]) := by simp only [span_append,span_cons,span_nil,Atom.span,Nat.add_zero]; omega
  apply lift_free w _ above _ _ (Line.outer_macro_free w hw _ _ above _ x (by omega) hx')
  dsimp only [UsedPoint,outerCell]
  by_cases hxend : x.val ≤ radius w+span w (pre++[.line n])
  · exact Or.inr (Or.inl ⟨by omega,hxend⟩)
  · apply Or.inr; apply Or.inr
    refine ⟨rfl,by omega,?_⟩
    simp only [exitSide_append,exitSide,Atom.nextSide]
    cases hs : exitSide above pre <;> simp [Exposed,laneY,radius] <;> omega

private theorem outer_tail_walk (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (x y : Fin (width w (pre++[.line n])))
    (hx : radius w+span w (pre++[.line n])-1 ≤ x.val) (hx' : x.val ≤ radius w+span w (pre++[.line n])+2)
    (hy : radius w+span w (pre++[.line n])-1 ≤ y.val) (hy' : y.val ≤ radius w+span w (pre++[.line n])+2) :
    Reachable (macroBoard (last:=true) w (pre++[.line n]) above) (some 1)
      ⟨outerCell w _ (!(exitSide above pre)) x,cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerCell w _ (!(exitSide above pre)) y,cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  apply walk_horizontal (cutBoxes_macro_floor w hw _ _ above)
  intro z hz hz'
  exact outer_tail_free w hw pre n hn above q z (by omega) (by omega)

private theorem hub_to_end (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w)
    (hflip : ∃ left right, pre++[.line n] = left++ .flip::right) :
    Reachable (macroBoard (last:=true) w (pre++[.line n]) above) (some 1)
      ⟨outerHub w _,cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨endCell w (pre++[.line n]) d,cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  have hd' := d.isLt
  have hn' := hn
  unfold buffer at hn'
  have hspan : 2 ≤ span w (pre++[.line n]) := by simp only [span_append,span_cons,span_nil,Atom.span,Nat.add_zero]; omega
  have he := Action.outer_reachable (last:=true) w hw (cut w (pre++[.line n]) q) (pre++[.line n]) above hflip (!(exitSide above pre))
    (outerCell w _ (!(exitSide above pre)) (endCell w (pre++[.line n]) 1).1)
    (by dsimp [outerCell,endCell]; unfold radius; omega)
    (by dsimp [outerCell,endCell]; unfold radius; omega) rfl
  have ht := outer_tail_walk w hw pre n hn above q (endCell w (pre++[.line n]) 1).1 (endCell w (pre++[.line n]) d).1
    (by dsimp [endCell]; omega) (by dsimp [endCell]; omega)
    (by dsimp [endCell]; omega) (by dsimp [endCell]; omega)
  exact he.trans (ht.trans (outer_to_end w hw pre n hn above q d hd ha))

private theorem hub_return (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w)
    (hflip : ∃ left right, pre++[.line n] = left++ .flip::right) :
    Reachable (macroBoard (last:=true) w (pre++[.line n]) above) (some 1)
      ⟨endCell w (pre++[.line n]) d,cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerHub w _,cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  have hd' := d.isLt
  have hn' := hn
  unfold buffer at hn'
  have hspan : 2 ≤ span w (pre++[.line n]) := by simp only [span_append,span_cons,span_nil,Atom.span,Nat.add_zero]; omega
  have he := Action.outer_return (last:=true) w hw (cut w (pre++[.line n]) q) (pre++[.line n]) above hflip (!(exitSide above pre))
    (outerCell w _ (!(exitSide above pre)) (endCell w (pre++[.line n]) 1).1)
    (by dsimp [outerCell,endCell]; unfold radius; omega)
    (by dsimp [outerCell,endCell]; unfold radius; omega) rfl
  have ht := outer_tail_walk w hw pre n hn above q (endCell w (pre++[.line n]) d).1 (endCell w (pre++[.line n]) 1).1
    (by dsimp [endCell]; omega) (by dsimp [endCell]; omega)
    (by dsimp [endCell]; omega) (by dsimp [endCell]; omega)
  exact (end_to_outer w hw pre n hn above q d hd ha).trans (ht.trans he)

/-- The final box has a real support walk, one push, and a return to the global line hub. -/
private theorem prepare (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (ha : ∀ a ∈ pre++[.line n], a.Valid w)
    (hflip : ∃ left right, pre++[.line n] = left++ .flip::right) :
    Reachable (macroBoard (last:=true) w (pre++[.line n]) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerHub w _, cutBoxes w hw (cut w (pre++[.line n]) (!q)) (pre++[.line n])⟩ := by
  have he := hub_to_end w hw pre n hn above q (if q then 3 else 0) (by cases q <;> simp) ha hflip
  have hx := hub_return w hw pre n hn above (!q) ⟨1+q.toNat, by have := Bool.toNat_le q; omega⟩
    (by cases q <;> simp) ha hflip
  exact (he.tail ⟨if q then .west else .east, push w hw _ (by have hb := hn; unfold buffer at hb; simp only [span_append,span_cons,span_nil,Atom.span,Nat.add_zero]; omega) above q⟩).trans hx

theorem program_prepare (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above q : Bool) :
    Reachable (macroBoard (last:=true) w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (cut w (program w length switch) q) (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw (cut w (program w length switch) (!q)) (program w length switch)⟩ := by
  obtain ⟨post, hp⟩ := program_contains_flip w length switch
  exact prepare w hw (initialAtoms w switch (decide (length % 2 = 1))) _ (by omega) above q
    (program_valid w length switch) ⟨[.line (buffer w)], post, hp⟩

end PushPuzzle.PushS.FiniteRouting.Line.Action.Terminal
