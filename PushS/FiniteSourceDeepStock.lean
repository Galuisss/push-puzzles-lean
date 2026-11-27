/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingDeepRows
public import PushS.FiniteSourceSideStock

/-! Deep literal working-row gaps stay empty in every normal whole-board primitive profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem inner_axis_owner_eq (w x y a b : ℕ)
    (ha : padding w+2 ≤ a ∧ a+2 ≤ tileStride w+padding w)
    (hb : padding w ≤ b+1 ∧ b ≤ tileStride w+padding w+1)
    (he : tileStride w*x+a = tileStride w*y+b) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have hm := Nat.mul_le_mul_left (tileStride w) (show x+1 ≤ y by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    omega
  · exact h
  · have hm := Nat.mul_le_mul_left (tileStride w) (show y+1 ≤ x by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    omega

private theorem primitive_deep_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,.line c) ∈ codes w v)
    (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment)
    (hown : ∀ goal l, Line.along w (segmentDirection c.segment) c.segment.start n ≠
      (PrimitiveCode.line c).actor w hw goal l)
    (t : GridRouting.Point × PrimitiveCode) (ht : t ∈ codes w v) (goal : Bool) (l : t.2.Labels w) :
    macroShift w pos (Line.along w (segmentDirection c.segment) c.segment.start n) ≠
      macroShift w t.1 (t.2.actor w hw goal l) := by
  have hcl := code_local w v (pos,.line c) hc
  have htl := code_local w v t ht
  have hg := (local_line_good w _ c hcl).1
  have ha := c.deep_row_inner_bounds w hw _ hcl hg n hn hn'
  have hb := local_actor_inner_bounds w hw _ t.2 htl goal l
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*pos.1+_ = tileStride w*t.1.1+_ at hx
  change tileStride w*pos.2+_ = tileStride w*t.1.2+_ at hy
  have hpos : pos = t.1 := Prod.ext
    (inner_axis_owner_eq w _ _ _ _ ⟨ha.1,ha.2.1⟩ ⟨hb.1,hb.2.1⟩ hx)
    (inner_axis_owner_eq w _ _ _ _ ha.2.2 hb.2.2 hy)
  have hlocal : t.2 ∈ localCodes w (CellPlan.cell (v,pos)) := by simpa only [hpos] using htl
  apply local_deep_row_actor_ne w hw (CellPlan.cell (v,pos)) c hcl hg n hn hn' hown t.2 hlocal goal l
  apply Prod.ext
  · rw [hpos] at hx
    omega
  · rw [hpos] at hy
    omega

theorem deep_stock_empty (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool)
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,.line c) ∈ codes w v)
    (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment)
    (hown : ∀ goal l, Line.along w (segmentDirection c.segment) c.segment.start n ≠
      (PrimitiveCode.line c).actor w hw goal l)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (Line.along w (segmentDirection c.segment) c.segment.start n)) :
    q ∉ PrimitiveProfile.boxes w hw v phase := by
  apply PrimitiveProfile.not_mem_of_actor_ne w hw v phase q
  intro i l
  rw [hq]
  exact primitive_deep_actor_ne w hw v pos c hc n hn hn' hown _ (List.get_mem _ _) (phase i) l

end PushPuzzle.PushS.FiniteSourceInventory
