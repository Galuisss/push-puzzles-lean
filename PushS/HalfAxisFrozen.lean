/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.HalfAxis
public import PushS.FrozenLabels

/-! A physically frozen back neighbour excludes northward box import into the lower half-axis. -/

public section
namespace PushPuzzle.PushS.HalfAxis

open PushFS Labels

variable {w h n : ℕ} {ι : Type} [Fintype ι] {B : Board w h} {cap : Option ℕ}
  {S T : LabelledState ι w h} {C : Finset (Cell w h)}

private theorem north_endpoint_fixed (A : Rail w h) (work : Fin h)
    (r : Run B .north S.state n) (hv : S.state.Valid B)
    (hpositions : T.position = shiftMap r ∘ S.position) (i : ι)
    (hfixed : T.position i = S.position i)
    (hback : Adjacent .south (A.column, work) (S.position i))
    (hx : S.state.player.1 = A.column) (hq : work.val ≤ (r.cell 1).2.val) :
    work.val ≤ (r.cell ⟨n + 1, by omega⟩).2.val := by
  by_contra hz
  have hbackx := hback.1
  have hbacky := hback.2
  change (S.position i).1 = A.column at hbackx
  change (S.position i).2.val = work.val + 1 at hbacky
  have hfirst := r.position 1
  simp only [Direction.position, Fin.val_one] at hfirst
  have hstrict : work.val < (r.cell 1).2.val := by
    by_contra h
    have he : S.state.player = S.position i :=
      Prod.ext (hx.trans hbackx.symm) (Fin.ext (by omega))
    exact hv.2.2 (he.symm ▸ S.position_mem i)
  obtain ⟨j, hj⟩ := north_index r (S.position i).2.val (by omega) (by omega)
  have he : r.cell ⟨j.val + 1, by omega⟩ = S.position i := by
    have hl := r.lane ⟨j.val + 1, by omega⟩
    simp only [Direction.lane] at hl
    exact Prod.ext (Fin.ext (by rw [hbackx]; simpa only [hx] using hl)) (Fin.ext hj)
  have hshift : shiftMap r (S.position i) = S.position i :=
    (congrFun hpositions i).symm.trans hfixed
  rw [← he, shiftMap_on] at hshift
  have hidx := congrArg Fin.val (r.injective hshift)
  change j.val + 2 = j.val + 1 at hidx
  omega

/-- The frozen physical box immediately below the work row supplies the exact north-push
endpoint condition, including pushes whose continuous run passes through that neighbour. -/
theorem noNorthInput_of_frozen (A : Rail w h) (work : Fin h)
    (hm : MultiStep B cap S T) (hfrozen : Freeze.Frozen C S T)
    (i : ι) (hi : S.position i ∈ C)
    (hback : Adjacent .south (A.column, work) (S.position i)) :
    NoNorthInput B A work S.state T.state := by
  intro k r hk hp hb hx hq
  obtain ⟨d, hm⟩ := hm
  have hadj := players_adjacent hm.forget
  have hnorth : Adjacent .north S.state.player T.state.player := by
    simpa only [r.start, hp, Fin.castSucc_zero, Fin.succ_zero_eq_one] using r.adjacent 0
  have hy : T.state.player.2.val + 1 = S.state.player.2.val := hnorth.2
  have hd : d = .north := by
    cases d with
    | north => rfl
    | east => have he := congrArg Fin.val hadj.2; omega
    | south => have he := hadj.2; omega
    | west => have he := congrArg Fin.val hadj.2; omega
  subst d
  cases hm with
  | walk _ _ _ he _ _ => exact False.elim (he (hp.symm ▸ r.first_occupied hk))
  | @push m hv _ _ run hp' hb' hpositions =>
    have hfirst : run.cell 1 = r.cell 1 := hp'.symm.trans hp
    have hlast : r.cell ⟨k + 1, by omega⟩ = run.cell ⟨m + 1, by omega⟩ := by
      have hh : r.cell ⟨k + 1, by omega⟩ ∈ T.state.boxes := hb ▸ Finset.mem_insert_self _ _
      rw [hb', Finset.mem_insert, Finset.mem_erase] at hh
      exact hh.elim id (fun h => False.elim (r.empty h.2))
    rw [hlast]
    exact north_endpoint_fixed A work run hv hpositions i (hfrozen.position i hi) hback hx
      (hfirst.symm ▸ hq)

end PushPuzzle.PushS.HalfAxis
