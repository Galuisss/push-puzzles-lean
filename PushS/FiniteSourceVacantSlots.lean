/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceOutsideRows

/-! An unoccupied endpoint of an actual one-step slot pair contains no normal foreign box. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace PrimitiveProfile

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

private theorem vacant_endpoint_empty (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (l : (inventory w hw v).PhysicalLabel)
    (d : Direction) (hs : Adjacent d ((inventory w hw v).source l) ((inventory w hw v).target l))
    (p : Cell (width w v) (height w v))
    (hp : p = (inventory w hw v).source l ∨ p = (inventory w hw v).target l)
    (hcurrent : position w hw v phase l ≠ p) : p ∉ boxes w hw v phase := by
  intro hm
  obtain ⟨r,_,he⟩ := Finset.mem_image.mp hm
  have hr_eq := endpoint_label_unique (admissible w hw v hP hT) hP hT phase l d hs p hp r he
  rw [hr_eq] at he
  exact hcurrent he

end PrimitiveProfile

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

/-- The actual owned second box of this emitted line. -/
private def secondIdentity : (inventory w hw v).PhysicalLabel :=
  s.ownedLabel s.first_false (Line.secondOwned w (segmentLength s.code.segment)
    (s.code.above != s.code.desiredSide) s.code.last)

private theorem second_identity_owner : s.secondIdentity.1 = s.index := s.owned_index s.first_false _

private theorem second_identity_source : (inventory w hw v).source s.secondIdentity = s.actualEmbedding.cells
    (Line.cell w hw s.atoms s.code.initial (Line.secondLabel w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide))) :=
  s.source_owned_actual s.first_false _

private theorem second_identity_target : (inventory w hw v).target s.secondIdentity = s.actualEmbedding.cells
    (Line.cell w hw s.atoms s.code.target (Line.secondLabel w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide))) :=
  s.target_owned_actual s.first_false _

theorem second_low_empty (hb : s.code.target = !s.code.initial)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hhigh : phase s.index = !s.code.initial) :
    s.actualEmbedding.cells (Line.cell w hw s.atoms false
      (Line.secondLabel w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide))) ∉ PrimitiveProfile.boxes w hw v phase := by
  let l : Line.Label w s.atoms := Line.secondLabel w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)
  have hpos (q : Bool) : Line.position w s.atoms q l = 2+q.toNat := Line.second_position w _ _ q
  have hadj := Line.normal_adjacent_of_position w hw s.atoms l 2 hpos
  have hstep : ∃ d, Adjacent d ((inventory w hw v).source s.secondIdentity) ((inventory w hw v).target s.secondIdentity) := by
    rw [s.second_identity_source,s.second_identity_target,hb]
    cases hi : s.code.initial
    · exact ⟨s.actualEmbedding.direction .east,s.actualEmbedding.adjacent _ _ _ hadj⟩
    · exact ⟨s.actualEmbedding.direction .west,s.actualEmbedding.adjacent _ _ _ hadj.reverse⟩
  obtain ⟨d,hd⟩ := hstep
  apply PrimitiveProfile.vacant_endpoint_empty hP hT phase s.secondIdentity d hd
  · cases hi : s.code.initial
    · left
      rw [s.second_identity_source,hi]
    · right
      rw [s.second_identity_target,hb,hi]
      rfl
  · have hcur : PrimitiveProfile.position w hw v phase s.secondIdentity =
        s.actualEmbedding.cells (Line.cell w hw s.atoms true l) := by
      unfold PrimitiveProfile.position
      rw [s.second_identity_owner,hhigh]
      cases hi : s.code.initial <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false]
      · rw [s.second_identity_target,hb,hi]
        rfl
      · rw [s.second_identity_source,hi]
    rw [hcur]
    intro he
    have hx := congrArg (fun p => p.1.val) (s.actualEmbedding.cells.injective he)
    change FiniteTools.radius w+Line.position w s.atoms true l = FiniteTools.radius w+Line.position w s.atoms false l at hx
    rw [hpos false,hpos true] at hx
    simp at hx

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
