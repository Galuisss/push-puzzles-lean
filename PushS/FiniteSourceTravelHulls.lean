/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingHullCollars
public import PushS.FiniteSourcePorts
public import PushS.FiniteSourceOwnership

/-! Normal-travel intervals of distinct actual global primitive owners never intersect. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem outerDirection_injective (pattern rotation : Fin 3) :
    Function.Injective (fun role : Fin 3 => PortAnnulus.outerDirection (pattern,rotation,role)) := by
  fin_cases pattern <;> fin_cases rotation <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide

theorem local_port_unique (code : CellPlan.Code) (face : Direction) (a b : Bool)
    (ha : LocalPort code face a) (hb : LocalPort code face b) : a = b := by
  cases code with
  | none => exact ha.elim
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨i,hi,hai⟩ := ha
      obtain ⟨j,hj,hbj⟩ := hb
      have he := outerDirection_injective g.2.pattern g.2.rotation (hi.trans hj.symm)
      subst j
      exact hai.symm.trans hbj
    | inr q => exact wire_port_unique q.1 q.2 face a b ha hb

private theorem localCodes_hulls_pairwise (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) :
    (localCodes w code).Pairwise (HullsApart w hw) := by
  cases code with
  | none => simp [localCodes]
  | some code =>
    cases code with
    | inl g => exact gateCodes_hulls_pairwise w hw g.2
    | inr q => exact (wireSpec w q.2).codes_hulls_pairwise w hw (wireSpec_geometry w q.2)

def PlacedHullsApart (w : ℕ) (hw : 2 ≤ w) (q t : (ℕ × ℕ) × PrimitiveCode) : Prop :=
  ∀ (l : q.2.Labels w) (r : t.2.Labels w) (a b : ℕ × ℕ),
    ActorHull w hw q.2 l a → ActorHull w hw t.2 r b → macroShift w q.1 a ≠ macroShift w t.1 b

private theorem foreign_hulls_apart (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (q t : GridRouting.Point × PrimitiveCode) (hq : q ∈ codes w v) (ht : t ∈ codes w v) (hne : q.1 ≠ t.1) :
    PlacedHullsApart w hw q t := by
  intro l r a b ha hb he
  have hcl := code_local w v q hq
  have htl := code_local w v t ht
  obtain ⟨p,hpa⟩ := actor_hull_cell w hw q.2 l a ha
  obtain ⟨s,hsb⟩ := actor_hull_cell w hw t.2 r b hb
  have hab : a.1 < tileSide w ∧ a.2 < tileSide w := hpa ▸ local_world_bounds w hw q.2 (localCodes_fits w hw _ hcl) p
  have hbb : b.1 < tileSide w ∧ b.2 < tileSide w := hsb ▸ local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) s
  obtain ⟨face,hn,hfa,hfb⟩ := macro_contact w q.1 t.1 a b hab hbb (local_hull_collar_lane w hw _ q.2 hcl l a ha) hne he
  obtain ⟨incoming,hport,hbound⟩ := local_hull_collar w hw _ q.2 hcl l a ha face hfa
  obtain ⟨out,hport',hbound'⟩ := local_hull_collar w hw _ t.2 htl r b hb face.opposite hfb
  have hrec := local_port_reciprocal v hP hT q.1 t.1 face hn incoming hport
  have hout := local_port_unique (CellPlan.cell (v,t.1)) face.opposite out (!incoming) hport' hrec
  rw [hout] at hbound'
  exact macro_port_owned_ne w face q.1 t.1 a b incoming hn hbound hbound' he

private theorem codes_hulls_pairwise (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (codes w v).Pairwise (PlacedHullsApart w hw) := by
  unfold codes
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro entry _
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ (localCodes_hulls_pairwise w hw entry.2)
    intro c d hcd l r a b ha hb he
    have ha' := congrArg Prod.fst he
    have hb' := congrArg Prod.snd he
    apply hcd l r a b ha hb
    apply Prod.ext <;> dsimp [macroShift] at ha' hb' <;> omega
  · apply List.Pairwise.imp_of_mem _ (cells_positions_pairwise v)
    intro entry other he ho hpos q hq t ht
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ht
    apply foreign_hulls_apart w hw v hP hT (entry.1,c) (other.1,d) _ _ hpos
    · unfold codes
      exact List.mem_flatMap.mpr ⟨entry,he,List.mem_map.mpr ⟨c,hc,rfl⟩⟩
    · unfold codes
      exact List.mem_flatMap.mpr ⟨other,ho,List.mem_map.mpr ⟨d,hd,rfl⟩⟩

private theorem primitive_hulls_apart (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i j : Fin (codes w v).length) (hne : i ≠ j) :
    PlacedHullsApart w hw ((codes w v).get i) ((codes w v).get j) := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with h | h
  · exact List.pairwise_iff_getElem.mp (codes_hulls_pairwise w hw v hP hT) i.val j.val i.isLt j.isLt h
  · intro l r a b ha hb
    exact Ne.symm (List.pairwise_iff_getElem.mp (codes_hulls_pairwise w hw v hP hT) j.val i.val j.isLt i.isLt h r l b a hb ha)

private theorem macro_hull_pullback (w : ℕ) (pos a b p : ℕ × ℕ)
    (hp : Hull (macroShift w pos a) (macroShift w pos b) p) :
    ∃ q, Hull a b q ∧ macroShift w pos q = p := by
  let q := (p.1-tileStride w*pos.1,p.2-tileStride w*pos.2)
  refine ⟨q,?_,?_⟩
  · dsimp [Hull,macroShift,q] at *
    omega
  · apply Prod.ext <;> dsimp [Hull,macroShift,q] at * <;> omega

theorem normal_travel_hulls_disjoint (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i j : (inventory w hw v).PhysicalLabel) (hne : i.1 ≠ j.1) (a : ℕ × ℕ)
    (hi : Hull (coordinates ((inventory w hw v).source i)) (coordinates ((inventory w hw v).target i)) a)
    (hj : Hull (coordinates ((inventory w hw v).source j)) (coordinates ((inventory w hw v).target j)) a) : False := by
  rcases i with ⟨i,l⟩
  rcases j with ⟨j,r⟩
  rw [placed_source_coordinates,placed_target_coordinates] at hi hj
  obtain ⟨p,hp,hpa⟩ := macro_hull_pullback w ((codes w v).get i).1 _ _ a hi
  obtain ⟨q,hq,hqa⟩ := macro_hull_pullback w ((codes w v).get j).1 _ _ a hj
  exact primitive_hulls_apart w hw v hP hT i j hne l r p q hp hq (hpa.trans hqa.symm)

end PushPuzzle.PushS.FiniteSourceInventory
