/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathSpacing
public import PushS.FiniteRoutingGateGeometry
public import PushS.FiniteRoutingWireCollars

/-! Distinct emitted primitives have sparse normal actors throughout each actual gate and wire. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem core_tail_actor_sparse (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (margin : ℕ) (hm : margin+1 ≤ FiniteGeometry.origin w) {u a : ℕ × ℕ}
    (hu : ∃ s ∈ (armRoute w g role).tail, s.Contains u)
    (ha : Nearby margin a (padding w+u.1,padding w+u.2))
    (goal : Bool) (l : (PrimitiveCode.core g).Labels w) (d : Direction) :
    ¬Travels d a ((PrimitiveCode.core g).actor w hw goal l) 1 := by
  intro he
  have hn := travels_one_nearby he
  have hb : Nearby (margin+1) ((PrimitiveCode.core g).actor w hw goal l)
      (padding w+u.1,padding w+u.2) := by unfold Nearby at *; omega
  exact core_tail_ne w hw g role (margin+1) hm hu hb
    (if goal then (PrimitiveCode.matching w hw (.core g)).target l else
      (PrimitiveCode.matching w hw (.core g)).source l) rfl

private theorem core_first_line_sparse (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    ActorsSparse w hw (.core g) (.line ((armSpec w g role).line 0)) := by
  intro goal l r d ha
  let c := (armSpec w g role).line 0
  let phase := portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role
  let r' : Line.OwnedLabel w
      (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) false c.last :=
    ⟨r.val,r.property⟩
  have hpos := Line.owned_position_after_first w (segmentLength c.segment) hw
    (c.above != c.desiredSide) phase c.last r'
  have hsep := core_ray_actor_separated w hw g role goal _ hpos l
  rw [first_line_actor_formula] at ha
  exact hsep (travels_one_nearby (travels_one_reverse ha))

private theorem core_arm_sparse (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes) : ActorsSparse w hw (.core g) c := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  change c ∈ P.codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      exact core_first_line_sparse w hw g role
    · intro goal l r d hadj
      obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi' goal r
      exact core_tail_actor_sparse w hw g role 1 (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ ha goal l d.opposite (travels_one_reverse hadj)
  · intro goal l r d hadj
    have ha := P.turn_actor_at w hw G i ht goal r
    rw [P.join_eq w G i ht.1] at ha
    exact core_tail_actor_sparse w hw g role 2 (by unfold FiniteGeometry.origin; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ ha
      goal l d.opposite (travels_one_reverse hadj)

private theorem different_arms_sparse (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (i j : Fin 3) (hij : i ≠ j) (c e : PrimitiveCode)
    (hc : c ∈ (armSpec w g i).codes) (he : e ∈ (armSpec w g j).codes) : ActorsSparse w hw c e := by
  intro goal l r d hadj
  obtain ⟨u,hu,ha⟩ := (armSpec w g i).code_actor_trace w hw (armSpec_geometry w g i) c hc goal l
  obtain ⟨v,hv,hb⟩ := (armSpec w g j).code_actor_trace w hw (armSpec_geometry w g j) e he goal r
  have hsep : ¬Nearby 1 (c.actor w hw goal l) (e.actor w hw goal r) :=
    footprint_not_nearby (w := w) (m := 2) (n := 2)
      (fun hn => armRoutes_separated_wide w g hij hu hv (nearby_of_le (by omega) hn)) ha hb
  exact hsep (travels_one_nearby hadj)

theorem gateCodes_sparse (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    (gateCodes w g).Pairwise (ActorsSparse w hw) := by
  rw [gateCodes_eq_specs,List.pairwise_cons]
  refine ⟨?_,?_⟩
  · intro c hc
    obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact core_arm_sparse w hw g role c hc
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun role _ => (armSpec w g role).codes_sparse w hw (armSpec_geometry w g role),?_⟩
    apply List.Pairwise.imp _ (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange 3))
    intro i j hij c hc e he
    exact different_arms_sparse w hw g i j hij c e hc he

theorem wireCodes_sparse (w : ℕ) (hw : 2 ≤ w) (q : Gadgets.Wires.Catalog.Bitmap.Args) :
    (wireCodes w q).Pairwise (ActorsSparse w hw) :=
  (wireSpec w q).codes_sparse w hw (wireSpec_geometry w q)

end PushPuzzle.PushS.FiniteRouting
