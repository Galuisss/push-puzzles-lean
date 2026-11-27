/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceConnectivity
public import PushS.FiniteSourceCoreTracks

/-! Each actual primitive's normal source and target slots are sparse on their named axes. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

private theorem and_normal_actual {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    (s : CoreSite w hw v) (hg : s.gate.core.isAND = true) (goal : Bool) (l : AndLabel w) :
    (if goal then (inventory w hw v).target (s.andLabel hg l) else (inventory w hw v).source (s.andLabel hg l)) =
      s.embedding.cells (andCell w (if goal then s.gate.core.target else s.gate.core.initial).left
        (if goal then s.gate.core.target else s.gate.core.initial).upper
        (if goal then s.gate.core.target else s.gate.core.initial).right l) := by
  cases goal
  · exact s.and_source_actual hg l
  · exact s.and_target_actual hg l

private theorem or_normal_actual {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    (s : CoreSite w hw v) (hg : s.gate.core.isAND = false) (goal : Bool) (l : OrLabel w) :
    (if goal then (inventory w hw v).target (s.orLabel hg l) else (inventory w hw v).source (s.orLabel hg l)) =
      s.embedding.cells (orCell w (if goal then s.gate.core.target else s.gate.core.initial).left
        (if goal then s.gate.core.target else s.gate.core.initial).upper
        (if goal then s.gate.core.target else s.gate.core.initial).right l) := by
  cases goal
  · exact s.or_source_actual hg l
  · exact s.or_target_actual hg l

private theorem core_normal_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (codes w v).length) (g : GateTileState) (hc : ((codes w v).get i).2 = .core g)
    (goal : Bool) (l r : (PrimitiveCode.core g).Labels w)
    (he : (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (primitiveLabel w hw v i (.core g) hc l)
        else (inventory w hw v).source (primitiveLabel w hw v i (.core g) hc l)) =
      (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (primitiveLabel w hw v i (.core g) hc r)
        else (inventory w hw v).source (primitiveLabel w hw v i (.core g) hc r))) (d : Direction) :
    ¬Adjacent d (if goal then (inventory w hw v).target (primitiveLabel w hw v i (.core g) hc l)
        else (inventory w hw v).source (primitiveLabel w hw v i (.core g) hc l))
      (if goal then (inventory w hw v).target (primitiveLabel w hw v i (.core g) hc r)
        else (inventory w hw v).source (primitiveLabel w hw v i (.core g) hc r)) := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · let s : CoreSite w hw v := ⟨i,⟨⟨false,initial,target⟩,incoming,pattern,rotation⟩,hc⟩
    change OrLabel w at l r
    change (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (s.orLabel rfl l) else (inventory w hw v).source (s.orLabel rfl l)) =
      (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (s.orLabel rfl r) else (inventory w hw v).source (s.orLabel rfl r)) at he
    change ¬Adjacent d (if goal then (inventory w hw v).target (s.orLabel rfl l) else (inventory w hw v).source (s.orLabel rfl l))
      (if goal then (inventory w hw v).target (s.orLabel rfl r) else (inventory w hw v).source (s.orLabel rfl r))
    rw [or_normal_actual s rfl goal l,or_normal_actual s rfl goal r] at he ⊢
    exact s.or_axis_sparse rfl hP hT _ _ _ l r he d
  · let s : CoreSite w hw v := ⟨i,⟨⟨true,initial,target⟩,incoming,pattern,rotation⟩,hc⟩
    change AndLabel w at l r
    change (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (s.andLabel rfl l) else (inventory w hw v).source (s.andLabel rfl l)) =
      (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (s.andLabel rfl r) else (inventory w hw v).source (s.andLabel rfl r)) at he
    change ¬Adjacent d (if goal then (inventory w hw v).target (s.andLabel rfl l) else (inventory w hw v).source (s.andLabel rfl l))
      (if goal then (inventory w hw v).target (s.andLabel rfl r) else (inventory w hw v).source (s.andLabel rfl r))
    rw [and_normal_actual s rfl goal l,and_normal_actual s rfl goal r] at he ⊢
    exact s.and_axis_sparse rfl hP hT _ _ _ l r he d

private theorem primitive_normal_adjacent_actor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c)
    (goal : Bool) (l r : c.Labels w) (d : Direction)
    (ha : Adjacent d (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc l)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc l))
      (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc r)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc r))) :
    Travels d (c.actor w hw goal l) (c.actor w hw goal r) 1 := by
  have hh := adjacent_coordinates ha
  have coordinates_normal (l : c.Labels w) :
      coordinates (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc l)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc l)) =
      macroShift w ((codes w v).get i).1 (c.actor w hw goal l) := by
    cases goal
    · exact source_primitiveLabel_coordinates w hw v i c hc l
    · exact target_primitiveLabel_coordinates w hw v i c hc l
  rw [coordinates_normal l,coordinates_normal r] at hh
  exact (shift_travels_iff (tileStride w*((codes w v).get i).1.1,tileStride w*((codes w v).get i).1.2) d _ _).mp hh

/-- Equal axis names forbid adjacent normal slots owned by one actual emitted primitive, in either phase. -/
theorem primitive_normal_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c)
    (goal : Bool) (l r : c.Labels w)
    (he : (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc l)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc l)) =
      (axisClassifier w hw v hP hT).name (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc r)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc r))) (d : Direction) :
    ¬Adjacent d (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc l)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc l))
      (if goal then (inventory w hw v).target (primitiveLabel w hw v i c hc r)
        else (inventory w hw v).source (primitiveLabel w hw v i c hc r)) := by
  cases c with
  | core g => exact core_normal_sparse w hw v hP hT i g hc goal l r he d
  | line c =>
    have hm : (((codes w v).get i).1,PrimitiveCode.line c) ∈ codes w v := by
      have hh : (codes w v).get i = (((codes w v).get i).1,PrimitiveCode.line c) := Prod.ext rfl hc
      exact hh ▸ List.get_mem (codes w v) i
    have hgood := (local_line_good w _ c (code_local w v _ hm)).1
    exact fun ha => line_actor_sparse w hw c hgood goal l r d
      (primitive_normal_adjacent_actor w hw v i (.line c) hc goal l r d ha)
  | turn c =>
    exact fun ha => turn_actor_sparse w hw c (turnCode_perpendicular w v i c hc) goal l r d
      (primitive_normal_adjacent_actor w hw v i (.turn c) hc goal l r d ha)

end PushPuzzle.PushS.FiniteSourceInventory
