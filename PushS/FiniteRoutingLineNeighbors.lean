/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionContract

/-! The actual endpoint-adjacent stock labels prepare the real P/Q boxes of each neighboring turn. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

def lastStockPrefix (w length : ℕ) (switch : Bool) : List Atom :=
  initialAtoms w switch (decide (length % 2 = 1))

def lastStockCount (w length : ℕ) (switch : Bool) : ℕ :=
  buffer w+(length-budget w switch (decide (length % 2 = 1)))/2

theorem lastStockCount_bound (w length : ℕ) (switch : Bool) : buffer w ≤ lastStockCount w length switch := by
  unfold lastStockCount
  omega

theorem program_last_stock (w length : ℕ) (switch : Bool) :
    program w length switch = lastStockPrefix w length switch++[.line (lastStockCount w length switch)] := rfl

theorem program_length_ge_six (w length : ℕ) (switch : Bool) :
    6 ≤ (positions w false (program w length switch)).length := by
  rw [program_last_stock,positions_split_length]
  have hn := lastStockCount_bound w length switch
  unfold buffer at hn
  simp only [positions,Atom.positions,List.length_append,List.length_map,List.length_range,List.length_singleton]
  omega

def secondLabel (w length : ℕ) (switch : Bool) : Label w (program w length switch) :=
  ⟨1,by have := program_length_ge_six w length switch; omega⟩

theorem second_position (w length : ℕ) (switch q : Bool) :
    position w (program w length switch) q (secondLabel w length switch) = 2+q.toNat := by
  obtain ⟨post,hp⟩ := program_contains_flip w length switch
  have hb : 1 < buffer w := by unfold buffer; omega
  have hh := congrArg (fun xs : List ℕ => xs[1]?)
    (congrArg (positions w q) hp)
  simp [positions,Atom.positions,List.getElem?_append,hb] at hh
  have hi : 1 < (positions w q (program w length switch)).length := by
    have := program_length_ge_six w length switch
    simpa only [positions_length] using (show 1 < (positions w false (program w length switch)).length by omega)
  simpa only [position,secondLabel,List.get_eq_getElem,List.getElem?_eq_getElem hi,Option.some.injEq] using hh

def penultimateLabel (w length : ℕ) (switch : Bool) : Label w (program w length switch) :=
  tailLabel w (lastStockPrefix w length switch) [.line (lastStockCount w length switch)]
    (lineLabel w (lastStockCount w length switch) [] ⟨lastStockCount w length switch-1,by
      have hb := lastStockCount_bound w length switch
      unfold buffer at hb
      omega⟩)

theorem penultimate_val (w length : ℕ) (switch : Bool) :
    (penultimateLabel w length switch).val = (positions w false (program w length switch)).length-2 := by
  have hb := lastStockCount_bound w length switch
  unfold buffer at hb
  have hh := positions_split_length w (lastStockPrefix w length switch) [.line (lastStockCount w length switch)]
  simp only [positions,Atom.positions,List.length_append,List.length_map,List.length_range,List.length_singleton] at hh
  change ownedCount w (lastStockPrefix w length switch)+(lastStockCount w length switch-1) = _
  rw [program_last_stock,hh]
  omega

theorem penultimate_position (w length : ℕ) (switch q : Bool) :
    position w (program w length switch) q (penultimateLabel w length switch) = span w (program w length switch)-2+q.toNat := by
  have hb := lastStockCount_bound w length switch
  unfold buffer at hb
  change position w (lastStockPrefix w length switch++[.line (lastStockCount w length switch)]) q
    (tailLabel w _ _ (lineLabel w _ [] _)) = _
  rw [tail_position,line_position,program_last_stock]
  simp only [span_append,span_cons,span_nil,Atom.span,Nat.add_zero]
  omega

def secondOwned (w length : ℕ) (switch last : Bool) : OwnedLabel w (program w length switch) false last :=
  ⟨secondLabel w length switch,Or.inr (by change 0 < 1; omega),Or.inr (by
    have := program_length_ge_six w length switch
    change 1+1 < _
    omega)⟩

end PushPuzzle.PushS.FiniteRouting.Line
