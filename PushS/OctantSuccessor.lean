/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PreparedRayOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Sectors
import all PushS.PreparedRayOrder

/-! The first occupied actual clockwise octant is the genuine geometric rotation successor. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The eight actual compass rays have distinct clockwise angles. -/
theorem octantAngle_injective : Function.Injective (fun rank : Fin 8 => octantAngle rank.val) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro left right he
  have hl := octant_lift_mem left.val left.isLt
  have hr := octant_lift_mem right.val right.isLt
  have hreal := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (Set.Ioo_subset_Ico_self hl) (Set.Ioo_subset_Ico_self hr)).mp he
  apply Fin.ext
  by_contra hne
  exact octant_lift_ne left.val right.val hne hreal

/-- A single actual dart at a vertex is its own genuine rotation successor. -/
theorem rotate_eq_self_of_vertex_unique {G : Graph} (rotation : Graph.RotationSystem G) (dart : Graph.Dart G)
    (hunique : ∀ other : Graph.Dart G, other.vertex = dart.vertex → other = dart) : rotation.rotate dart = dart :=
  hunique _ (rotation.vertex_rotate dart)

private theorem octant_rank_injective {G : Graph} {drawing : Graph.PolygonalDrawing G} {rotation : Graph.RotationSystem G}
    (hR : drawing.Realizes rotation) (origin : Graph.Dart G) (rank : Graph.Dart G → Fin 8)
    (hdir : ∀ dart, dart.vertex = origin.vertex → drawing.direction dart = octantAngle (rank dart).val)
    (left right : Graph.Dart G) (hl : left.vertex = origin.vertex) (hr : right.vertex = origin.vertex)
    (he : (rank left).val = (rank right).val) : left = right := by
  apply hR.directions_injective left right (hl.trans hr.symm)
  rw [hdir left hl, hdir right hr, he]

/-- The first occupied positive clockwise rank gives the actual native geometric successor. -/
theorem rotate_eq_of_octant_next {G : Graph} {drawing : Graph.PolygonalDrawing G} {rotation : Graph.RotationSystem G}
    (hR : drawing.Realizes rotation) (origin next : Graph.Dart G) (hnext : next.vertex = origin.vertex)
    (hne : origin ≠ next) (rank : Graph.Dart G → Fin 8)
    (hdir : ∀ dart, dart.vertex = origin.vertex → drawing.direction dart = octantAngle (rank dart).val)
    (hfirst : ∀ dart : Graph.Dart G, dart.vertex = origin.vertex → dart ≠ origin →
      ((rank next).val + 7 - (rank origin).val) % 8 ≤ ((rank dart).val + 7 - (rank origin).val) % 8) :
    rotation.rotate origin = next := by
  let actual := rotation.rotate origin
  have hv : actual.vertex = origin.vertex := rotation.vertex_rotate origin
  have hactual : actual ≠ origin := by
    intro he
    exact hne (((rotation.sameCycle_iff origin next).mpr hnext.symm).eq_of_left he)
  by_contra hnot
  have hneq : actual ≠ next := hnot
  have hon : (rank origin).val ≠ (rank next).val :=
    fun h => hne (octant_rank_injective hR origin rank hdir origin next rfl hnext h)
  have hna : (rank next).val ≠ (rank actual).val :=
    fun h => hneq (octant_rank_injective hR origin rank hdir next actual hnext hv h).symm
  have hoa : (rank origin).val ≠ (rank actual).val :=
    fun h => hactual (octant_rank_injective hR origin rank hdir origin actual rfl hv h).symm
  have hbefore := hfirst actual hv hactual
  have ho := (rank origin).isLt
  have hn := (rank next).isLt
  have ha := (rank actual).isLt
  have hstep : ((rank next).val + 7 - (rank origin).val) % 8 < ((rank actual).val + 7 - (rank origin).val) % 8 := by omega
  have hprev : rotation.rotate.symm actual = origin := rotation.rotate.symm_apply_apply origin
  have hno := hR.not_sbtw_inverse_rotate actual next (hnext.trans hv.symm) hneq.symm (by rw [hprev]; exact hne.symm)
  rw [hprev, hdir actual hv, hdir next hnext, hdir origin rfl] at hno
  apply hno
  exact (sbtw_octants_iff ho hn ha hon hna hoa).mpr (by omega)

/-- A complete genuine vertex catalog may compute its actual successor entirely in its own occupied octants. -/
theorem rotate_eq_of_octant_catalog {G : Graph} {drawing : Graph.PolygonalDrawing G} {rotation : Graph.RotationSystem G}
    {ι : Type} (hR : drawing.Realizes rotation) (catalog : ι → Graph.Dart G) (hinj : Function.Injective catalog)
    (origin next : ι) (hne : origin ≠ next)
    (hsame : ∀ index, (catalog index).vertex = (catalog origin).vertex)
    (hcover : ∀ dart : Graph.Dart G, dart.vertex = (catalog origin).vertex → ∃ index, catalog index = dart)
    (rank : ι → Fin 8) (hdir : ∀ index, drawing.direction (catalog index) = octantAngle (rank index).val)
    (hfirst : ∀ index, index ≠ origin →
      ((rank next).val + 7 - (rank origin).val) % 8 ≤ ((rank index).val + 7 - (rank origin).val) % 8) :
    rotation.rotate (catalog origin) = catalog next := by
  let extended := Function.extend catalog rank (fun _ => (0 : Fin 8))
  have hrank (index : ι) : extended (catalog index) = rank index := hinj.extend_apply _ _ index
  apply rotate_eq_of_octant_next hR (catalog origin) (catalog next) (hsame next) (fun h => hne (hinj h)) extended
  · intro dart hv
    obtain ⟨index, rfl⟩ := hcover dart hv
    rw [hrank]
    exact hdir index
  · intro dart hv hnot
    obtain ⟨index, rfl⟩ := hcover dart hv
    rw [hrank, hrank, hrank]
    exact hfirst index (fun h => hnot (h ▸ rfl))

/-- A complete list of occupied ray witnesses identifies the genuine first clockwise successor. -/
theorem rotate_eq_of_octant_minimum {G : Graph} {drawing : Graph.PolygonalDrawing G} {rotation : Graph.RotationSystem G}
    (hR : drawing.Realizes rotation) (origin next : Graph.Dart G) (hnext : next.vertex = origin.vertex)
    (originRank nextRank : Fin 8) (hne : originRank ≠ nextRank)
    (horigin : drawing.direction origin = octantAngle originRank.val)
    (hnextdir : drawing.direction next = octantAngle nextRank.val)
    (hcover : ∀ dart : Graph.Dart G, dart.vertex = origin.vertex → ∃ rank : Fin 8,
      drawing.direction dart = octantAngle rank.val ∧
        (rank = originRank ∨ (nextRank.val + 7 - originRank.val) % 8 ≤ (rank.val + 7 - originRank.val) % 8)) :
    rotation.rotate origin = next := by
  classical
  let rank (dart : Graph.Dart G) : Fin 8 := if hv : dart.vertex = origin.vertex then (hcover dart hv).choose else 0
  have hdir (dart : Graph.Dart G) (hv : dart.vertex = origin.vertex) :
      drawing.direction dart = octantAngle (rank dart).val := by
    simpa only [rank, dite_eq_left hv] using (hcover dart hv).choose_spec.1
  have hrankOrigin : rank origin = originRank := octantAngle_injective ((hdir origin rfl).symm.trans horigin)
  have hrankNext : rank next = nextRank := octantAngle_injective ((hdir next hnext).symm.trans hnextdir)
  apply rotate_eq_of_octant_next hR origin next hnext (fun he => hne (by rw [← hrankOrigin, ← hrankNext, he])) rank hdir
  intro dart hv hnot
  have h : rank dart = originRank ∨
      (nextRank.val + 7 - originRank.val) % 8 ≤ ((rank dart).val + 7 - originRank.val) % 8 := by
    simpa only [rank, dite_eq_left hv] using (hcover dart hv).choose_spec.2
  rw [hrankNext, hrankOrigin]
  rcases h with he | hle
  · exact False.elim (hnot (hR.directions_injective dart origin hv (by rw [hdir dart hv, he, horigin])))
  · exact hle

end PushPuzzle.PushS.Comb
