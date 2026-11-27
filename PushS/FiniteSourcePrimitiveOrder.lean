/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingNormalOrder
public import PushS.FiniteSourceCoreTracks
public import PushS.FiniteSourceConnectivity
public import PushS.FiniteGateOrder

/-! Actual normal source and target slots preserve both coordinate orders within each emitted primitive. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateTracks

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem actor_order_lift (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c) (l r : c.Labels w)
    (ho : ((c.actor w hw false l).1 < (c.actor w hw false r).1 → (c.actor w hw true l).1 < (c.actor w hw true r).1) ∧
      ((c.actor w hw false l).2 < (c.actor w hw false r).2 → (c.actor w hw true l).2 < (c.actor w hw true r).2)) :
    (((inventory w hw v).source (primitiveLabel w hw v i c hc l)).1.val <
        ((inventory w hw v).source (primitiveLabel w hw v i c hc r)).1.val →
      ((inventory w hw v).target (primitiveLabel w hw v i c hc l)).1.val <
        ((inventory w hw v).target (primitiveLabel w hw v i c hc r)).1.val) ∧
    (((inventory w hw v).source (primitiveLabel w hw v i c hc l)).2.val <
        ((inventory w hw v).source (primitiveLabel w hw v i c hc r)).2.val →
      ((inventory w hw v).target (primitiveLabel w hw v i c hc l)).2.val <
        ((inventory w hw v).target (primitiveLabel w hw v i c hc r)).2.val) := by
  have hsl := source_primitiveLabel_coordinates w hw v i c hc l
  have hsr := source_primitiveLabel_coordinates w hw v i c hc r
  have htl := target_primitiveLabel_coordinates w hw v i c hc l
  have htr := target_primitiveLabel_coordinates w hw v i c hc r
  constructor
  · intro h
    have a := congrArg Prod.fst hsl
    have b := congrArg Prod.fst hsr
    have e := congrArg Prod.fst htl
    have f := congrArg Prod.fst htr
    dsimp [coordinates,shiftPoint] at a b e f
    have hh := ho.1 (by omega)
    omega
  · intro h
    have a := congrArg Prod.snd hsl
    have b := congrArg Prod.snd hsr
    have e := congrArg Prod.snd htl
    have f := congrArg Prod.snd htr
    dsimp [coordinates,shiftPoint] at a b e f
    have hh := ho.2 (by omega)
    omega

namespace CoreSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)

private theorem and_slot_order (hg : s.gate.core.isAND = true) (hP : v.1.checkPlane = true)
    (hT : v.1.WellTyped [] [])
    (l r : AndLabel w)
    (hc : component (inventory w hw v).board ((inventory w hw v).source (s.andLabel hg l)) =
      component (inventory w hw v).board ((inventory w hw v).source (s.andLabel hg r))) :
    (((inventory w hw v).source (s.andLabel hg l)).1.val < ((inventory w hw v).source (s.andLabel hg r)).1.val →
      ((inventory w hw v).target (s.andLabel hg l)).1.val < ((inventory w hw v).target (s.andLabel hg r)).1.val) ∧
    (((inventory w hw v).source (s.andLabel hg l)).2.val < ((inventory w hw v).source (s.andLabel hg r)).2.val →
      ((inventory w hw v).target (s.andLabel hg l)).2.val < ((inventory w hw v).target (s.andLabel hg r)).2.val) := by
  have he := (axisClassifier w hw v hP hT).name_eq_of_sameComponent (component_eq_iff.mp hc)
  rw [s.and_source_actual,s.and_source_actual,s.and_axis_name hg hP hT,s.and_axis_name hg hP hT] at he
  have ht := AxisTrack.shift_injective s.offsetX s.offsetY he
  have ho := andTrack_order w hw s.gate.core.initial s.gate.core.target l r ht
  constructor <;> intro h
  · rw [s.and_source_actual,s.and_source_actual,s.embedding_x,s.embedding_x] at h
    rw [s.and_target_actual,s.and_target_actual,s.embedding_x,s.embedding_x]
    have hh := ho.1 (by omega)
    omega
  · rw [s.and_source_actual,s.and_source_actual,s.embedding_y,s.embedding_y] at h
    rw [s.and_target_actual,s.and_target_actual,s.embedding_y,s.embedding_y]
    have hh := ho.2 (by omega)
    omega

private theorem or_slot_order (hg : s.gate.core.isAND = false) (hP : v.1.checkPlane = true)
    (hT : v.1.WellTyped [] [])
    (l r : OrLabel w)
    (hc : component (inventory w hw v).board ((inventory w hw v).source (s.orLabel hg l)) =
      component (inventory w hw v).board ((inventory w hw v).source (s.orLabel hg r))) :
    (((inventory w hw v).source (s.orLabel hg l)).1.val < ((inventory w hw v).source (s.orLabel hg r)).1.val →
      ((inventory w hw v).target (s.orLabel hg l)).1.val < ((inventory w hw v).target (s.orLabel hg r)).1.val) ∧
    (((inventory w hw v).source (s.orLabel hg l)).2.val < ((inventory w hw v).source (s.orLabel hg r)).2.val →
      ((inventory w hw v).target (s.orLabel hg l)).2.val < ((inventory w hw v).target (s.orLabel hg r)).2.val) := by
  have he := (axisClassifier w hw v hP hT).name_eq_of_sameComponent (component_eq_iff.mp hc)
  rw [s.or_source_actual,s.or_source_actual,s.or_axis_name hg hP hT,s.or_axis_name hg hP hT] at he
  have ht := AxisTrack.shift_injective s.offsetX s.offsetY he
  have ho := orTrack_order w hw s.gate.core.initial s.gate.core.target l r ht
  constructor <;> intro h
  · rw [s.or_source_actual,s.or_source_actual,s.embedding_x,s.embedding_x] at h
    rw [s.or_target_actual,s.or_target_actual,s.embedding_x,s.embedding_x]
    have hh := ho.1 (by omega)
    omega
  · rw [s.or_source_actual,s.or_source_actual,s.embedding_y,s.embedding_y] at h
    rw [s.or_target_actual,s.or_target_actual,s.embedding_y,s.embedding_y]
    have hh := ho.2 (by omega)
    omega

end CoreSite

theorem primitive_slot_order (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c) (l r : c.Labels w)
    (he : component (inventory w hw v).board ((inventory w hw v).source (primitiveLabel w hw v i c hc l)) =
      component (inventory w hw v).board ((inventory w hw v).source (primitiveLabel w hw v i c hc r))) :
    (((inventory w hw v).source (primitiveLabel w hw v i c hc l)).1.val < ((inventory w hw v).source (primitiveLabel w hw v i c hc r)).1.val →
      ((inventory w hw v).target (primitiveLabel w hw v i c hc l)).1.val < ((inventory w hw v).target (primitiveLabel w hw v i c hc r)).1.val) ∧
    (((inventory w hw v).source (primitiveLabel w hw v i c hc l)).2.val < ((inventory w hw v).source (primitiveLabel w hw v i c hc r)).2.val →
      ((inventory w hw v).target (primitiveLabel w hw v i c hc l)).2.val < ((inventory w hw v).target (primitiveLabel w hw v i c hc r)).2.val) := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
    cases kind
    · exact (⟨i,⟨⟨false,initial,target⟩,incoming,pattern,rotation⟩,hc⟩ : CoreSite w hw v).or_slot_order rfl hP hT l r he
    · exact (⟨i,⟨⟨true,initial,target⟩,incoming,pattern,rotation⟩,hc⟩ : CoreSite w hw v).and_slot_order rfl hP hT l r he
  | line c =>
    let s : LineSite w hw v := ⟨i,c,hc⟩
    exact actor_order_lift w hw v i (.line c) hc l r (line_actor_order w hw c s.good l r)
  | turn c =>
    exact actor_order_lift w hw v i (.turn c) hc l r (turn_actor_order w hw c (turnCode_perpendicular w v i c hc) l r)

end PushPuzzle.PushS.FiniteSourceInventory
