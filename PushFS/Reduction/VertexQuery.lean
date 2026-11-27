/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Raster

/-! Executable, unique lookup of the real source gate occupying a refined anchor. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction PushPuzzle.PushFS.Reduction.Plan

theorem refinePoint_injective : Function.Injective refinePoint := by
  intro p q hh
  have hx := congrArg Prod.fst hh
  have hy := congrArg Prod.snd hh
  dsimp [refinePoint] at hx hy
  apply Prod.ext <;> omega

namespace Plan

/-- Geometric source records at the same point are the same complete record. -/
private theorem verticesFrom_point_injective (w : Word) (st : Word.State) (y : ℕ)
    {u v : VertexData} (hu : u ∈ verticesFrom w st y) (hv : v ∈ verticesFrom w st y)
    (hp : u.point = v.point) : u = v := by
  induction w generalizing st y with
  | nil => cases hu
  | cons sl w ih =>
    rw [verticesFrom_cons] at hu hv
    rcases List.mem_cons.mp hu with rfl | hu
    · rcases List.mem_cons.mp hv with rfl | hv
      · rfl
      · have hv' : VertexPointFrom w (sl.run st) (y + (Layer.mk sl st).height) v.point :=
          (mem_vertexPoints_iff _ _ _ _).mp (List.mem_map.mpr ⟨v, hv, rfl⟩)
        have hrow := hv'.row_lower
        have he := congrArg Prod.snd hp
        dsimp only [Layer.vertexData] at he
        have hm : (Layer.mk sl st).vertexPoint.2 + 3 ≤ (Layer.mk sl st).height := by
          unfold Layer.vertexPoint Layer.height Layer.middleY
          omega
        omega
    · rcases List.mem_cons.mp hv with rfl | hv
      · have hu' : VertexPointFrom w (sl.run st) (y + (Layer.mk sl st).height) u.point :=
          (mem_vertexPoints_iff _ _ _ _).mp (List.mem_map.mpr ⟨u, hu, rfl⟩)
        have hrow := hu'.row_lower
        have he := congrArg Prod.snd hp
        dsimp only [Layer.vertexData] at he
        have hm : (Layer.mk sl st).vertexPoint.2 + 3 ≤ (Layer.mk sl st).height := by
          unfold Layer.vertexPoint Layer.height Layer.middleY
          omega
        omega
      · exact ih _ _ hu hv

theorem vertexRecords_point_injective {w : Word} {u v : VertexData}
    (hu : u ∈ vertexRecords w) (hv : v ∈ vertexRecords w) (hp : u.point = v.point) : u = v :=
  verticesFrom_point_injective w ⟨[], 0, []⟩ 0 hu hv hp

end Plan

namespace Raster

/-- Find the actual source gate at this refined point, retaining all source indices and ports. -/
def vertexAt (q : Word × GridRouting.Point) : Option VertexData :=
  (vertexRecords q.1).find? fun v => refinePoint v.point == q.2

/-- The found record really occurs in the source table and at exactly the requested point. -/
theorem vertexAt_sound {w : Word} {p : GridRouting.Point} {v : VertexData}
    (hv : vertexAt (w, p) = some v) : v ∈ vertexRecords w ∧ refinePoint v.point = p := by
  exact ⟨List.mem_of_find?_eq_some hv,
    beq_iff_eq.mp (List.find?_some (p := fun v : VertexData => refinePoint v.point == p) hv)⟩

/-- Every record is found at its own anchor; the lookup uses no arbitrary tie-breaking. -/
theorem vertexAt_eq_some_iff (w : Word) (p : GridRouting.Point) (v : VertexData) :
    vertexAt (w, p) = some v ↔ v ∈ vertexRecords w ∧ refinePoint v.point = p := by
  constructor
  · exact vertexAt_sound
  · rintro ⟨hv, hp⟩
    cases hh : vertexAt (w, p) with
    | none =>
      have hn := List.find?_eq_none.mp hh v hv
      exact False.elim (hn (by simp only [hp, beq_self_eq_true]))
    | some u =>
      obtain ⟨hu, huP⟩ := vertexAt_sound hh
      have huv := vertexRecords_point_injective hu hv (refinePoint_injective (huP.trans hp.symm))
      simp only [huv]

/-- Absence of a gate is exactly absence of an actual refined source vertex. -/
theorem vertexAt_none_iff (w : Word) (p : GridRouting.Point) :
    vertexAt (w, p) = none ↔
      ¬∃ q, VertexPointFrom w ⟨[], 0, []⟩ 0 q ∧ p = refinePoint q := by
  constructor
  · intro hn
    rintro ⟨q, hq, hp⟩
    obtain ⟨v, hv, he⟩ := List.mem_map.mp ((mem_vertexPoints_iff _ _ _ _).mpr hq)
    have hh := (vertexAt_eq_some_iff w p v).mpr ⟨hv, by rw [he, hp]⟩
    rw [hn] at hh
    contradiction
  · intro hn
    cases hh : vertexAt (w, p) with
    | none => rfl
    | some v =>
      obtain ⟨hv, hp⟩ := vertexAt_sound hh
      exact False.elim (hn ⟨v.point,
        (mem_vertexPoints_iff _ _ _ _).mp (List.mem_map.mpr ⟨v, hv, rfl⟩), hp.symm⟩)

/-- Standard encoded search over the actual polynomial-time source table. -/
theorem vertexAt_polyTime :
    ComputableInPolyTime vertexAt (encPair encWord Bitmap.encPoint) (encOption encVertexData) := by
  have hv : ComputableInPolyTime (fun q : Word × GridRouting.Point => vertexRecords q.1)
      (encPair encWord Bitmap.encPoint) (encList encVertexData) :=
    vertexRecords_polyTime.comp (ComputableInPolyTime.fst encWord Bitmap.encPoint)
  have ht : ComputableInPolyTime (fun q : GridRouting.Point × VertexData => refinePoint q.2.point == q.1)
      (encPair Bitmap.encPoint encVertexData) encBool := by
    unfold Bitmap.encPoint
    fun_prop
  exact ComputableInPolyTime.findWith ht (ComputableInPolyTime.snd encWord Bitmap.encPoint) hv

end Raster
end PushPuzzle.PushFS.Reduction
