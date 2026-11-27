/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineNeighbors

/-! The actual first and last stock rectangles guard every routed program's endpoint strips. -/

public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

private theorem rectangles_append (w offset : ℕ) (above : Bool) (a b : List Atom) :
    rectangles w offset above (a++b) = rectangles w offset above a ++
      rectangles w (offset+span w a) (exitSide above a) b := by
  induction a generalizing offset above with
  | nil => simp [rectangles,span,exitSide]
  | cons c a ih => simp only [List.cons_append,rectangles,ih,span_cons,exitSide,Nat.add_assoc,List.append_assoc]

/-- The width-`w` stock guard on the selected side of a working row. -/
@[expose] def StockBand (w : ℕ) (above : Bool) (y : ℕ) : Prop :=
  if above then FiniteTools.radius w-w ≤ y ∧ y < FiniteTools.radius w
  else FiniteTools.radius w+1 ≤ y ∧ y < FiniteTools.radius w+w+1

attribute [local irreducible] width height walls rectangles Rectangle.cells

theorem program_first_stock_wall (w length : ℕ) (switch above : Bool)
    (p : Cell (width w (program w length switch)) (height w))
    (hx : FiniteTools.radius w ≤ p.1.val) (hx' : p.1.val < FiniteTools.radius w+2*buffer w+2)
    (hy : StockBand w above p.2.val) : p ∈ walls w (program w length switch) above := by
  let r : Rectangle := ⟨FiniteTools.radius w,if above then FiniteTools.radius w-w else FiniteTools.radius w+1,
    2*buffer w+2,w⟩
  have hr : r ∈ rectangles w 0 above (program w length switch) := by
    obtain ⟨post,hp⟩ := program_contains_flip w length switch
    rw [hp,List.singleton_append,rectangles]
    apply List.mem_append_left
    exact List.mem_singleton.mpr rfl
  have hb : p ∈ r.cells (width w (program w length switch)) (height w) := by
    rw [Rectangle.mem_cells]
    cases above <;> dsimp [StockBand,r] at hy ⊢ <;> unfold FiniteTools.radius at * <;> omega
  unfold walls
  exact Finset.mem_biUnion.mpr ⟨r,List.mem_toFinset.mpr hr,hb⟩

theorem program_last_stock_wall (w length : ℕ) (switch above : Bool)
    (p : Cell (width w (program w length switch)) (height w))
    (hx : FiniteTools.radius w+span w (program w length switch) ≤ p.1.val+2*buffer w)
    (hx' : p.1.val < FiniteTools.radius w+span w (program w length switch)+2)
    (hy : StockBand w (exitSide above (program w length switch)) p.2.val) :
    p ∈ walls w (program w length switch) above := by
  let pre := lastStockPrefix w length switch
  let n := lastStockCount w length switch
  let side := exitSide above pre
  let r : Rectangle := ⟨FiniteTools.radius w+span w pre,if side then FiniteTools.radius w-w else FiniteTools.radius w+1,
    2*n+2,w⟩
  have hn := lastStockCount_bound w length switch
  change buffer w ≤ n at hn
  have hspan : span w (program w length switch) = span w pre+2*n := by
    rw [program_last_stock,span_append]
    simp only [span_cons,Atom.span,span_nil,Nat.add_zero]
    rfl
  have hside : exitSide above (program w length switch) = side := by
    rw [program_last_stock,exitSide_append]
    rfl
  have hr : r ∈ rectangles w 0 above (program w length switch) := by
    rw [program_last_stock,rectangles_append]
    apply List.mem_append_right
    rw [rectangles]
    apply List.mem_append_left
    apply List.mem_singleton.mpr
    dsimp [r,side,pre,n]
    simp only [Nat.zero_add]
  have hb : p ∈ r.cells (width w (program w length switch)) (height w) := by
    rw [Rectangle.mem_cells]
    rw [hside] at hy
    cases hs : side <;> simp [StockBand,r,hs] at hy ⊢
    all_goals unfold buffer FiniteTools.radius at *; omega
  unfold walls
  exact Finset.mem_biUnion.mpr ⟨r,List.mem_toFinset.mpr hr,hb⟩

theorem program_first_wall_band (w length : ℕ) (switch above : Bool)
    (p : Cell (width w (program w length switch)) (height w))
    (hp : p ∈ walls w (program w length switch) above)
    (hx : p.1.val < FiniteTools.radius w+2*buffer w) : StockBand w above p.2.val := by
  unfold walls at hp
  obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp hp
  have hr' := List.mem_toFinset.mp hr
  have hb := (r.mem_cells _ _ p).mp hp
  obtain ⟨post,he⟩ := program_contains_flip w length switch
  rw [he,List.singleton_append,rectangles] at hr'
  rcases List.mem_append.mp hr' with hr' | hr'
  · have heq : r = ⟨FiniteTools.radius w,if above then FiniteTools.radius w-w else FiniteTools.radius w+1,
        2*buffer w+2,w⟩ := by simpa only [Atom.rectangles,Nat.add_zero,List.mem_singleton] using hr'
    rw [heq] at hb
    cases above <;> dsimp [StockBand] at * <;> unfold FiniteTools.radius at * <;> omega
  · have hh := rectangles_bounds w _ _ _ hr'
    simp only [Atom.span,Nat.zero_add] at hh
    omega

theorem program_end_wall_band (w length : ℕ) (switch above : Bool)
    (p : Cell (width w (program w length switch)) (height w))
    (hp : p ∈ walls w (program w length switch) above)
    (hx : FiniteTools.radius w+span w (program w length switch) ≤ p.1.val+(w+1)) :
    StockBand w (exitSide above (program w length switch)) p.2.val := by
  unfold walls at hp
  obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp hp
  have hr' := List.mem_toFinset.mp hr
  have hb := (r.mem_cells _ _ p).mp hp
  let pre := lastStockPrefix w length switch
  let n := lastStockCount w length switch
  have hn := lastStockCount_bound w length switch
  have hspan : span w (program w length switch) = span w pre+2*n := by
    rw [program_last_stock,span_append]
    simp only [span_cons,Atom.span,span_nil,Nat.add_zero]
    rfl
  have hside : exitSide above (program w length switch) = exitSide above pre := by
    rw [program_last_stock,exitSide_append]
    rfl
  rw [program_last_stock,rectangles_append] at hr'
  rcases List.mem_append.mp hr' with hr' | hr'
  · have hh := rectangles_bounds w _ _ _ hr'
    rw [hspan] at hx
    change buffer w ≤ n at hn
    have hbound : r.x+r.width ≤ FiniteTools.radius w+span w pre+2 := by
      simpa only [Nat.add_zero] using hh.2.1
    unfold buffer at hn
    omega
  · have heq : r = ⟨FiniteTools.radius w+span w pre,
        if exitSide above pre then FiniteTools.radius w-w else FiniteTools.radius w+1,2*n+2,w⟩ := by
      simpa only [rectangles,Atom.rectangles,List.append_nil,Nat.zero_add,List.mem_singleton] using hr'
    rw [heq] at hb
    rw [hside]
    cases hs : exitSide above pre <;> simp only [hs,StockBand,Bool.false_eq_true,↓reduceIte] at *
    all_goals unfold FiniteTools.radius at *; omega

theorem program_last_wall_band (w length : ℕ) (switch above : Bool)
    (p : Cell (width w (program w length switch)) (height w))
    (hp : p ∈ walls w (program w length switch) above)
    (hx : FiniteTools.radius w+span w (program w length switch) ≤ p.1.val) :
    StockBand w (exitSide above (program w length switch)) p.2.val := by
  exact program_end_wall_band w length switch above p hp (by omega)

end PushPuzzle.PushS.FiniteRouting.Line
