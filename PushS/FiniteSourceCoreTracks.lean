/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreConnectivity
public import PushS.FiniteGateTracks
public import PushS.FiniteRoutingSpacing
public import PushS.FiniteSourceAxisMosaic
public import PushFS.RailTags

/-! Actual core normal rails force their literal global row and column names. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateMatching FiniteGateTracks

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)

attribute [local irreducible] codes width height FiniteGeometry.side InventoryAssembly.board InventoryAssembly.walls

def offsetX : ℕ := tileStride w*((codes w v).get s.index).1.1+padding w+coreOffset w
def offsetY : ℕ := tileStride w*((codes w v).get s.index).1.2+padding w+coreOffset w

theorem embedding_x (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    (s.embedding.cells p).1.val = s.offsetX+p.1.val := by
  have h := congrArg Prod.fst (s.embedding_coordinates p)
  simpa only [coordinates,macroShift,coreWorld,offsetX,Nat.add_assoc] using h

theorem embedding_y (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    (s.embedding.cells p).2.val = s.offsetY+p.2.val := by
  have h := congrArg Prod.snd (s.embedding_coordinates p)
  simpa only [coordinates,macroShift,coreWorld,offsetY,Nat.add_assoc] using h

private theorem andTrack_at (l : AndLabel w) :
    andTrack w l = if andVertical l then .vertical (andCell w false false false l).1.val
      else .horizontal (andCell w false false false l).2.val := by cases l <;> rfl

private theorem orTrack_at (l : OrLabel w) :
    orTrack w l = if orVertical l then .vertical (orCell w false false false l).1.val
      else .horizontal (orCell w false false false l).2.val := by cases l <;> rfl

private theorem and_native_name (C : AxisClassifier (inventory w hw v).board)
    (hg : s.gate.core.isAND = true)
    (ha : ∀ l, C.name (s.embedding.cells (andCell w false false false l)) ≠ .outside)
    (a b c : Bool) (l : AndLabel w) :
    C.name (s.embedding.cells (andCell w a b c l)) = AxisTrack.shift s.offsetX s.offsetY (andTrack w l) := by
  have hn : C.name (s.embedding.cells (andCell w false false false l)) =
      AxisTrack.shift s.offsetX s.offsetY (andTrack w l) := by
    have hh := s.and_normal_connected hg false false false true true true l
    rw [andTrack_at]
    cases hv : andVertical l
    · have hne : (s.embedding.cells (andCell w false false false l)).1.val ≠
          (s.embedding.cells (andCell w true true true l)).1.val := by
        rw [s.embedding_x,s.embedding_x]
        cases l <;> simp [andVertical] at hv <;> simp only [andCell,andPoint,origin,Bool.toNat_false,Bool.toNat_true] <;> omega
      simpa only [hv,Bool.false_eq_true,↓reduceIte,AxisTrack.shift,s.embedding_y] using
        C.horizontal_of_active_component hh hne (ha l)
    · have hne : (s.embedding.cells (andCell w false false false l)).2.val ≠
          (s.embedding.cells (andCell w true true true l)).2.val := by
        rw [s.embedding_y,s.embedding_y]
        cases l <;> simp [andVertical] at hv <;> simp only [andCell,andPoint,origin,Bool.toNat_false,Bool.toNat_true] <;> omega
      simpa only [hv,↓reduceIte,AxisTrack.shift,s.embedding_x] using
        C.vertical_of_active_component hh hne (ha l)
  exact (C.name_eq_of_sameComponent (s.and_normal_connected hg a b c false false false l)).trans hn

private theorem or_native_name (C : AxisClassifier (inventory w hw v).board)
    (hg : s.gate.core.isAND = false)
    (ha : ∀ l, C.name (s.embedding.cells (orCell w false false false l)) ≠ .outside)
    (a b c : Bool) (l : OrLabel w) :
    C.name (s.embedding.cells (orCell w a b c l)) = AxisTrack.shift s.offsetX s.offsetY (orTrack w l) := by
  have hn : C.name (s.embedding.cells (orCell w false false false l)) =
      AxisTrack.shift s.offsetX s.offsetY (orTrack w l) := by
    have hh := s.or_normal_connected hg false false false true true true l
    rw [orTrack_at]
    cases hv : orVertical l
    · have hne : (s.embedding.cells (orCell w false false false l)).1.val ≠
          (s.embedding.cells (orCell w true true true l)).1.val := by
        rw [s.embedding_x,s.embedding_x]
        cases l <;> simp [orVertical] at hv <;> simp only [orCell,orPoint,origin,Bool.toNat_false,Bool.toNat_true] <;> omega
      simpa only [hv,Bool.false_eq_true,↓reduceIte,AxisTrack.shift,s.embedding_y] using
        C.horizontal_of_active_component hh hne (ha l)
    · have hne : (s.embedding.cells (orCell w false false false l)).2.val ≠
          (s.embedding.cells (orCell w true true true l)).2.val := by
        rw [s.embedding_y,s.embedding_y]
        cases l <;> simp [orVertical] at hv
        simp only [orCell,orPoint,origin,Bool.toNat_false,Bool.toNat_true]
        omega
      simpa only [hv,↓reduceIte,AxisTrack.shift,s.embedding_x] using
        C.vertical_of_active_component hh hne (ha l)
  exact (C.name_eq_of_sameComponent (s.or_normal_connected hg a b c false false false l)).trans hn

private theorem adjacent_local (d : Direction) (p q : Cell (FiniteGeometry.side w)
    (FiniteGeometry.side w))
    (h : Adjacent d (s.embedding.cells p) (s.embedding.cells q)) : Adjacent d p q := by
  have ha := adjacent_coordinates h
  have hx := s.embedding_x p
  have hy := s.embedding_y p
  have hx' := s.embedding_x q
  have hy' := s.embedding_y q
  cases d <;> simp only [Travels,coordinates,Adjacent,Fin.ext_iff] at * <;> constructor <;> omega

theorem and_axis_name (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (a b c : Bool) (l : AndLabel w) :
    (axisClassifier w hw v hP hT).name (s.embedding.cells (andCell w a b c l)) =
      AxisTrack.shift s.offsetX s.offsetY (andTrack w l) := by
  apply s.and_native_name (axisClassifier w hw v hP hT) hg _ a b c l
  intro r
  have ha := axis_actor_active w hw v hP hT false (s.andLabel hg r)
  rw [s.and_source_actual] at ha
  have he := (axisClassifier w hw v hP hT).name_eq_of_sameComponent
    (s.and_normal_connected hg false false false s.gate.core.initial.left s.gate.core.initial.upper
      s.gate.core.initial.right r)
  exact he.symm ▸ ha

theorem or_axis_name (hg : s.gate.core.isAND = false)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (a b c : Bool) (l : OrLabel w) :
    (axisClassifier w hw v hP hT).name (s.embedding.cells (orCell w a b c l)) =
      AxisTrack.shift s.offsetX s.offsetY (orTrack w l) := by
  apply s.or_native_name (axisClassifier w hw v hP hT) hg _ a b c l
  intro r
  have ha := axis_actor_active w hw v hP hT false (s.orLabel hg r)
  rw [s.or_source_actual] at ha
  have he := (axisClassifier w hw v hP hT).name_eq_of_sameComponent
    (s.or_normal_connected hg false false false s.gate.core.initial.left s.gate.core.initial.upper
      s.gate.core.initial.right r)
  exact he.symm ▸ ha

theorem and_axis_sparse (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (a b c : Bool) (l r : AndLabel w)
    (he : (axisClassifier w hw v hP hT).name (s.embedding.cells (andCell w a b c l)) =
      (axisClassifier w hw v hP hT).name (s.embedding.cells (andCell w a b c r))) (d : Direction) :
    ¬Adjacent d (s.embedding.cells (andCell w a b c l)) (s.embedding.cells (andCell w a b c r)) := by
  rw [s.and_axis_name hg hP hT,s.and_axis_name hg hP hT] at he
  exact fun ha => andTrack_sparse w hw a b c l r (AxisTrack.shift_injective _ _ he) d
    (s.adjacent_local d _ _ ha)

theorem or_axis_sparse (hg : s.gate.core.isAND = false)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (a b c : Bool) (l r : OrLabel w)
    (he : (axisClassifier w hw v hP hT).name (s.embedding.cells (orCell w a b c l)) =
      (axisClassifier w hw v hP hT).name (s.embedding.cells (orCell w a b c r))) (d : Direction) :
    ¬Adjacent d (s.embedding.cells (orCell w a b c l)) (s.embedding.cells (orCell w a b c r)) := by
  rw [s.or_axis_name hg hP hT,s.or_axis_name hg hP hT] at he
  exact fun ha => orTrack_sparse w hw a b c l r (AxisTrack.shift_injective _ _ he) d
    (s.adjacent_local d _ _ ha)

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
