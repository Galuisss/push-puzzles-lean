/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateMixedSeparation
public import PushS.FiniteSourceCoreCorridors
public import PushS.FiniteSourceMouthFree
public import PushS.FiniteSourceDockGeometry

/-! Actual first-arm crossings retain every mixed core box and every global outside identity. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateFaceGeometry FiniteGateOuterAccess
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- Every mixed AND stock is actual global floor, independently of the current outside phase. -/
private theorem and_mixed_stock_floor (hg : c.gate.core.isAND = true)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool) (X : AndPhases w) :
    Disjoint ((andMixedBoxes w X).map c.embedding.cells ∪ c.remaining phase) (inventory w hw v).walls := by
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp ha
    apply c.envelope_floor
    · simpa only [hg] using and_mixed_envelope w hw X l
    · simpa [hg,FiniteCoreGuardCoverage.walls] using andMixedCell_floor w hw X l
  · exact PrimitiveProfile.outside_floor ha phase _

/-- Every mixed OR stock is actual global floor. -/
private theorem or_mixed_stock_floor (hg : c.gate.core.isAND = false)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool) (X : OrPhases w) :
    Disjoint ((orMixedBoxes w X).map c.embedding.cells ∪ c.remaining phase) (inventory w hw v).walls := by
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp ha
    apply c.envelope_floor
    · simpa only [hg] using or_mixed_envelope w hw X l
    · simp only [hg,FiniteCoreGuardCoverage.walls,Bool.false_eq_true,ite_false]
      cases l <;> exact orCell_not_wall w hw _ _ _ _
  · exact PrimitiveProfile.outside_floor ha phase _

private theorem outside_subset (phase : Fin (codes w v).length → Bool) :
    c.remaining phase ⊆ PrimitiveProfile.boxes w hw v phase := by
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩

/-- The emitted first arm's exact direction and anchor, with its actual line-site index. -/
private theorem first_arm_parameters (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0) :
    segmentDirection (p.line i).code.segment = PortAnnulus.innerDirection role ∧
      (p.line i).code.segment.start = corePort w c.gate.core.isAND role := by
  change segmentDirection ((armSpec w c.gate role).line i.val).segment = _ ∧
    ((armSpec w c.gate role).line i.val).segment.start = _
  rw [hi,armSpec_first_direction,armSpec_first_start]
  exact ⟨rfl,rfl⟩

private theorem first_arm_world_eq (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1) (i : Fin (armSpec w c.gate role).segments.length)
    (a : Cell (Line.width w (p.line i).atoms) (Line.height w))
    (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (he : c.embedding.cells q = (p.line i).actualEmbedding.cells a) :
    coreWorld w q = (p.line i).code.actionWorld w hw a := by
  have hh := congrArg coordinates he
  rw [c.embedding_coordinates,(p.line i).actual_cell_coordinates,p.line_location,hloc] at hh
  exact (macroShift_injective w _) hh

private theorem first_arm_stock_empty (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1) (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0)
    (stock : Finset (Cell (FiniteGeometry.side w) (FiniteGeometry.side w)))
    (henv : ∀ q ∈ stock,Envelope w c.gate.core.isAND (coordinates q))
    (hside : ∀ q ∈ stock,Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w c.gate.core.isAND role) 0) (coreWorld w q) →
      SameLane (PortAnnulus.innerDirection role)
        (Line.along w (PortAnnulus.innerDirection role) (corePort w c.gate.core.isAND role) 0) (coreWorld w q))
    (a : Cell (Line.width w (p.line i).atoms) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ a.1.val) (hx' : a.1.val ≤ FiniteTools.radius w+Line.span w (p.line i).atoms)
    (hs : a.2.val ≠ FiniteTools.radius w ∨ 2 < a.1.val-FiniteTools.radius w) :
    (p.line i).actualEmbedding.cells a ∉ stock.map c.embedding.cells := by
  intro hm
  obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hm
  have heq := c.first_arm_world_eq role p hloc i a q he
  obtain ⟨hd,hstart⟩ := c.first_arm_parameters role p i hi
  by_cases hrow : a.2.val = FiniteTools.radius w
  · have hn : 2 < a.1.val-FiniteTools.radius w := hs.resolve_left (not_not.mpr hrow)
    have hr := (p.line i).code.actionWorld_on_row w hw (p.line i).good a (by omega) (Nat.le_trans hx' (Nat.le_succ _)) hrow
    rw [hd,hstart] at hr
    have hb := envelope_ray_bound w c.gate.core.isAND role _ q (henv q hq) (hr.symm.trans heq.symm)
    omega
  · have hb := (p.line i).code.sideBand_of_interior w hw (p.line i).good a hx hx' hrow
    have ho := hb.1
    have hn := hb.2.2
    rw [hd,hstart,←heq] at ho hn
    exact hn (hside q hq (outward_one_zero w c.gate.core.isAND role _ ho))

/-- Off-axis cells and all deeper row cells miss every actual mixed AND identity. -/
private theorem and_first_arm_empty (hg : c.gate.core.isAND = true) (role : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate role)) (hloc : p.location = ((codes w v).get c.index).1)
    (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0) (X : AndPhases w)
    (a : Cell (Line.width w (p.line i).atoms) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ a.1.val) (hx' : a.1.val ≤ FiniteTools.radius w+Line.span w (p.line i).atoms)
    (hs : a.2.val ≠ FiniteTools.radius w ∨ 2 < a.1.val-FiniteTools.radius w) :
    (p.line i).actualEmbedding.cells a ∉ (andMixedBoxes w X).map c.embedding.cells := by
  apply c.first_arm_stock_empty role p hloc i hi (andMixedBoxes w X) _ _ a hx hx' hs
  · intro q hq
    simpa only [hg] using and_mixed_image_envelope w hw X _ q hq
  · intro q hq ho
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    rw [hg] at ho ⊢
    exact andMixed_outward_lane w hw X role l ho

/-- The same real first-arm separation for arbitrary mixed OR stocks. -/
private theorem or_first_arm_empty (hg : c.gate.core.isAND = false) (role : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate role)) (hloc : p.location = ((codes w v).get c.index).1)
    (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0) (X : OrPhases w)
    (a : Cell (Line.width w (p.line i).atoms) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ a.1.val) (hx' : a.1.val ≤ FiniteTools.radius w+Line.span w (p.line i).atoms)
    (hs : a.2.val ≠ FiniteTools.radius w ∨ 2 < a.1.val-FiniteTools.radius w) :
    (p.line i).actualEmbedding.cells a ∉ (orMixedBoxes w X).map c.embedding.cells := by
  apply c.first_arm_stock_empty role p hloc i hi (orMixedBoxes w X) _ _ a hx hx' hs
  · intro q hq
    simpa only [hg] using or_mixed_image_envelope w hw X _ q hq
  · intro q hq ho
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    rw [hg] at ho ⊢
    exact orMixed_outward_lane w hw X role l ho

private def EmptyOnFaces (s : LineSite w hw v) (extra : Finset (Cell (width w v) (height w v))) : Prop :=
  ∀ a : Cell (Line.width w s.atoms) (Line.height w),
    FiniteTools.radius w+1 ≤ a.1.val → a.1.val ≤ FiniteTools.radius w+Line.span w s.atoms →
    (a.2.val ≠ FiniteTools.radius w ∨ 2 < a.1.val-FiniteTools.radius w) → s.actualEmbedding.cells a ∉ extra

private theorem outer_free_with_extra (s : LineSite w hw v) (phase : Fin (codes w v).length → Bool)
    (extra fixed : Finset (Cell (width w v) (height w v)))
    (hfixed : fixed ⊆ PrimitiveProfile.boxes w hw v phase) (hextra : EmptyOnFaces s extra)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls)
    (north : Bool) (x : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    Free B (extra ∪ fixed) (s.actualEmbedding.cells (Line.outerCell w s.atoms north x)) := by
  have hf := s.normal_outer_free phase north x hx hx'
  constructor
  · rw [hB]; exact hf.1
  · intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · apply hextra _ hx hx' _ hm
      apply Or.inl
      cases north <;> dsimp [Line.outerCell,Line.laneY,FiniteTools.radius] <;> omega
    · exact hf.2 (hfixed hm)

private theorem mouth_free_with_extra (s : LineSite w hw v)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (extra fixed : Finset (Cell (width w v) (height w v)))
    (hfixed : fixed ⊆ PrimitiveProfile.boxes w hw v phase) (hextra : EmptyOnFaces s extra)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    ∀ (j : Fin 2) (a : Cell (Line.width w s.atoms) (Line.height w)),
      a.1.val = FiniteTools.radius w+2*Line.buffer w+w+1+j.val →
      FiniteTools.radius w-w-1 ≤ a.2.val → a.2.val ≤ FiniteTools.radius w+w+1 →
      (if Line.flipMouthNorth s.code.above [.line (Line.buffer w)] j then a.2.val ≤ FiniteTools.radius w
        else FiniteTools.radius w ≤ a.2.val) → Free B (extra ∪ fixed) (s.actualEmbedding.cells a) := by
  intro j a hx hy hy' hs
  have hf := s.normal_mouths_free hP hT phase j a hx hy hy' hs
  constructor
  · rw [hB]; exact hf.1
  · intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have hlen := s.good.2.1
      have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ hlen
      have hj := j.isLt
      apply hextra a _ _ (Or.inr (by unfold Line.buffer at hx; omega)) hm
      all_goals unfold Line.buffer at hx; omega
    · exact hf.2 (hfixed hm)

private theorem first_arm_faces_of_empty (s : LineSite w hw v)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (extra fixed : Finset (Cell (width w v) (height w v)))
    (hfixed : fixed ⊆ PrimitiveProfile.boxes w hw v phase) (hextra : EmptyOnFaces s extra)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls)
    (hstock : Disjoint (extra ∪ fixed) B.walls) (north north' : Bool) :
    Reachable B (some 1)
      ⟨s.actualEmbedding.cells (Line.outerCell w s.atoms north (Line.outerHubX w s.atoms)),extra ∪ fixed⟩
      ⟨s.actualEmbedding.cells (Line.outerCell w s.atoms north' (Line.outerHubX w s.atoms)),extra ∪ fixed⟩ := by
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have hpos : 1 ≤ Line.span w s.atoms := by rw [hspan]; have hh := s.good.2.1; omega
  exact Line.NormalWalking.program_connected (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)
    s.code.above s.actualEmbedding hstock (outer_free_with_extra s phase extra fixed hfixed hextra B hB)
    (mouth_free_with_extra s hP hT phase extra fixed hfixed hextra B hB) north north' _ _
    (le_refl _) (Nat.add_le_add_left hpos _) (le_refl _) (Nat.add_le_add_left hpos _)

/-- Both real faces of a first arm are connected with an arbitrary actual mixed And inventory fixed. -/
theorem and_first_arm_faces (hg : c.gate.core.isAND = true) (role : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate role)) (hloc : p.location = ((codes w v).get c.index).1)
    (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool) (X : AndPhases w)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls)
    (north north' : Bool) :
    Reachable B (some 1)
      ⟨(p.line i).actualEmbedding.cells (Line.outerCell w (p.line i).atoms north (Line.outerHubX w (p.line i).atoms)),
        (andMixedBoxes w X).map c.embedding.cells ∪ c.remaining phase⟩
      ⟨(p.line i).actualEmbedding.cells (Line.outerCell w (p.line i).atoms north' (Line.outerHubX w (p.line i).atoms)),
        (andMixedBoxes w X).map c.embedding.cells ∪ c.remaining phase⟩ := by
  exact first_arm_faces_of_empty (p.line i) hP hT phase _ _ (c.outside_subset phase)
    (c.and_first_arm_empty hg role p hloc i hi X) B hB
    (by rw [hB]; exact c.and_mixed_stock_floor hg ha phase X) north north'

/-- Both real faces of a first arm are connected with an arbitrary actual mixed Or inventory fixed. -/
theorem or_first_arm_faces (hg : c.gate.core.isAND = false) (role : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate role)) (hloc : p.location = ((codes w v).get c.index).1)
    (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool) (X : OrPhases w)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls)
    (north north' : Bool) :
    Reachable B (some 1)
      ⟨(p.line i).actualEmbedding.cells (Line.outerCell w (p.line i).atoms north (Line.outerHubX w (p.line i).atoms)),
        (orMixedBoxes w X).map c.embedding.cells ∪ c.remaining phase⟩
      ⟨(p.line i).actualEmbedding.cells (Line.outerCell w (p.line i).atoms north' (Line.outerHubX w (p.line i).atoms)),
        (orMixedBoxes w X).map c.embedding.cells ∪ c.remaining phase⟩ := by
  exact first_arm_faces_of_empty (p.line i) hP hT phase _ _ (c.outside_subset phase)
    (c.or_first_arm_empty hg role p hloc i hi X) B hB
    (by rw [hB]; exact c.or_mixed_stock_floor hg ha phase X) north north'

/-- A literal core-side exterior anchor equals its actual first-arm outer hub. -/
theorem first_arm_anchor_eq (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1)
    (i : Fin (armSpec w c.gate role).segments.length) (hi : i.val = 0)
    (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (north : Bool)
    (hq : coreWorld w q = Line.outerStart w (PortAnnulus.innerDirection role) (corePort w c.gate.core.isAND role) north) :
    c.embedding.cells q = (p.line i).actualEmbedding.cells
      (Line.outerCell w (p.line i).atoms north (Line.outerHubX w (p.line i).atoms)) := by
  have hl := c.embedding_coordinates q
  have hr := (p.line i).actual_outerStart_coordinates north
  obtain ⟨hd,hs⟩ := c.first_arm_parameters role p i hi
  rw [p.line_location,hloc,hd,hs,←hq] at hr
  have he := hl.trans hr.symm
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
