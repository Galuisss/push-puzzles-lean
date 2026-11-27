/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.UnitGraph

/-!
# Actual interior joints of the strip carriers

An old edge's joint positions are precisely the interior sites of its actual unit path. Distinct
joint indices identify distinct grid sites, and none of those sites is any original source center.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.unitPoint_joint_get`: the actual joint site is the actual next unit-path entry.
* `PushPuzzle.NCL.Strip.Sweep.joint_point_injective`: joint sites on one original carrier are distinct.
* `PushPuzzle.NCL.Strip.Sweep.joint_not_center`: every interior joint avoids all original source centers.
* `PushPuzzle.NCL.Strip.Sweep.existsUnique_joint`: every noncenter carrier grid site is its unique actual joint.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal ConstraintGraph

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

private theorem pair_count (e : E) :
    (R.unitRoute e).consecutivePairs.length = (R.unitRoute e).length - 1 := by
  simp [List.consecutivePairs]

private theorem joint_bound (e : E) (j : Fin (jointCount R e)) :
    j.val + 2 < (R.unitRoute e).length := by
  have hj := j.isLt
  have hc := jointCount_succ R e
  have hp := pair_count R e
  omega

/-- The actual joint site is the actual unit-path entry one after its zero-based joint index. -/
theorem unitPoint_joint_get (e : E) (j : Fin (jointCount R e)) :
    unitPoint R (.inr ⟨e, j⟩) =
      (R.unitRoute e)[j.val + 1]'(by have := joint_bound R e j; omega) := by
  rw [unitPoint, PushPuzzle.NCL.Strip.Sweep.Arc.pair_at_index]
  rfl

/-- Joint indices on one original carrier identify distinct actual grid sites. -/
theorem joint_point_injective (e : E) :
    Function.Injective (fun j : Fin (jointCount R e) => unitPoint R (.inr ⟨e, j⟩)) := by
  intro j k h
  simp only [unitPoint_joint_get] at h
  have hi := (R.unitRoute_nodup e).getElem_inj_iff.mp h
  exact Fin.ext (by omega)

private theorem unitRoute_head (e : E) :
    (R.unitRoute e).head? = some (R.center (R.endpoint e false)) := by
  rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_head]
  rfl

private theorem unitRoute_last (e : E) :
    (R.unitRoute e).getLast? = some (R.center (R.endpoint e true)) := by
  rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_last (R.route_orthogonal e)]
  rfl

/-- An actual interior joint avoids every original source center. -/
theorem joint_not_center (j : Subdivision.Joint (jointCount R)) (v : V) :
    unitPoint R (.inr j) ≠ R.center v := by
  rcases j with ⟨e, j⟩
  intro h
  have hm : unitPoint R (.inr ⟨e, j⟩) ∈ R.unitRoute e := by
    rw [unitPoint_joint_get]
    exact List.getElem_mem _
  have hv := (R.center_mem_support_iff e v).mp
    ((R.mem_unitRoute e _).mp (h ▸ hm))
  have hb := joint_bound R e j
  have hidx : (R.unitRoute e)[j.val + 1]'(by omega) = R.center v := by
    simpa only [unitPoint_joint_get] using h
  rcases hv with hv | hv
  · have hh := unitRoute_head R e
    rw [List.head?_eq_getElem?] at hh
    obtain ⟨_, hh⟩ := List.getElem_of_getElem? hh
    have hi := (R.unitRoute_nodup e).getElem_inj_iff.mp
      ((hidx.trans (by simpa only [hv] using hh.symm)))
    omega
  · have hh := unitRoute_last R e
    rw [List.getLast?_eq_getElem?] at hh
    obtain ⟨_, hh⟩ := List.getElem_of_getElem? hh
    have hi := (R.unitRoute_nodup e).getElem_inj_iff.mp
      ((hidx.trans (by simpa only [hv] using hh.symm)))
    omega

/-- Every noncenter grid site of an actual carrier is one unique actual interior joint. -/
theorem existsUnique_joint (e : E) {p : Point} (hp : p ∈ R.unitRoute e)
    (hc : ∀ v, p ≠ R.center v) :
    ∃! j : Fin (jointCount R e), unitPoint R (.inr ⟨e, j⟩) = p := by
  obtain ⟨k, hk⟩ := List.get_of_mem hp
  have hk' : (R.unitRoute e)[k.val] = p := hk
  have hzero : 0 < k.val := by
    by_contra hz
    have he : k.val = 0 := by omega
    have hh := unitRoute_head R e
    rw [List.head?_eq_getElem?] at hh
    obtain ⟨_, hh⟩ := List.getElem_of_getElem? hh
    simp only [he] at hk'
    exact hc (R.endpoint e false) (hk'.symm.trans hh)
  have hlast : k.val + 1 < (R.unitRoute e).length := by
    by_contra hn
    have he : k.val = (R.unitRoute e).length - 1 := by have := k.isLt; omega
    have hh := unitRoute_last R e
    rw [List.getLast?_eq_getElem?] at hh
    obtain ⟨_, hh⟩ := List.getElem_of_getElem? hh
    simp only [he] at hk'
    exact hc (R.endpoint e true) (hk'.symm.trans hh)
  let j : Fin (jointCount R e) := ⟨k.val - 1, by
    have hs := jointCount_succ R e
    have hl := pair_count R e
    omega⟩
  have hj : unitPoint R (.inr ⟨e, j⟩) = p := by
    rw [unitPoint_joint_get]
    have hi : j.val + 1 = k.val := by dsimp only [j]; omega
    simpa only [hi] using hk'
  exact ⟨j, hj, fun j' hj' => joint_point_injective R e (hj'.trans hj.symm)⟩

end PushPuzzle.NCL.Strip.Sweep
