/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Init
public import CslibFrontier.Foundations.Geometry.Orthogonal.UnitSegments
public import CslibFrontier.Foundations.Geometry.Orthogonal.Neighborhood
public import CslibFrontier.Foundations.Geometry.Orthogonal.Separation
public import CslibFrontier.Foundations.Geometry.Orthogonal.Reverse
import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-!
# End segments of simple lattice routes

The strip sweep identifies the unique segment touching a route endpoint.
-/

public section

namespace PushPuzzle.Orthogonal

open Cslib Cslib.Orthogonal

private theorem pair_eq_of_touch_head {r : Route} (hn : r.Nodup) {p : Point}
    (hh : r.head? = some p) {e f : Point × Point}
    (he : e ∈ r.consecutivePairs) (hf : f ∈ r.consecutivePairs)
    (hep : e.1 = p ∨ e.2 = p) (hfp : f.1 = p ∨ f.2 = p) : e = f := by
  cases r with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons a r =>
    have ha : a = p := Option.some.inj hh
    subst p
    cases r with
    | nil => exact False.elim (List.not_mem_nil he)
    | cons b r =>
      have only (q : Point × Point) (hq : q ∈ (a :: b :: r).consecutivePairs)
          (hp : q.1 = a ∨ q.2 = a) : q = (a, b) := by
        rcases List.mem_cons.mp hq with hq | hq
        · exact hq
        · have hm := List.of_mem_zip hq
          have hm' : a ∈ b :: r := hp.elim (fun h => h ▸ hm.1)
            (fun h => h ▸ List.mem_of_mem_tail hm.2)
          exact False.elim ((List.nodup_cons.mp hn).1 hm')
      exact (only e he hep).trans (only f hf hfp).symm

/-- Any segment touching the first point of a route with distinct points starts there. -/
theorem fst_eq_of_touch_head {r : Route} (hn : r.Nodup) {p : Point}
    (hh : r.head? = some p) {e : Point × Point} (he : e ∈ r.consecutivePairs)
    (hp : e.1 = p ∨ e.2 = p) : e.1 = p := by
  rcases hp with hp | hp
  · exact hp
  · cases r with
    | nil => exact False.elim (List.not_mem_nil he)
    | cons a r =>
      have ha : a = p := Option.some.inj hh
      obtain ⟨i, hi, _, hy⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp he
      have hy' : (a :: r)[i + 1] = (a :: r)[0] := hy.trans (hp.trans ha.symm)
      have hidx := hn.getElem_inj_iff.mp hy'
      omega

/-- Any segment touching the final point of a route with distinct points ends there. -/
theorem snd_eq_of_touch_last {r : Route} (hn : r.Nodup) {p : Point}
    (hh : r.getLast? = some p) {e : Point × Point} (he : e ∈ r.consecutivePairs)
    (hp : e.1 = p ∨ e.2 = p) : e.2 = p := by
  have hre : Prod.swap e ∈ r.reverse.consecutivePairs := by
    rw [consecutivePairs_reverse]
    exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, rfl⟩
  exact fst_eq_of_touch_head (List.nodup_reverse.mpr hn)
    (by simpa only [List.head?_reverse] using hh) hre hp.symm

/-- At either endpoint of a route with distinct points, there is only one incident segment. -/
theorem pair_eq_of_touch_endpoint {r : Route} (hn : r.Nodup) {p : Point}
    (hp : r.head? = some p ∨ r.getLast? = some p) {e f : Point × Point}
    (he : e ∈ r.consecutivePairs) (hf : f ∈ r.consecutivePairs)
    (hep : e.1 = p ∨ e.2 = p) (hfp : f.1 = p ∨ f.2 = p) : e = f := by
  rcases hp with hp | hp
  · exact pair_eq_of_touch_head hn hp he hf hep hfp
  · have hre : Prod.swap e ∈ r.reverse.consecutivePairs := by
      rw [consecutivePairs_reverse]
      exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, rfl⟩
    have hrf : Prod.swap f ∈ r.reverse.consecutivePairs := by
      rw [consecutivePairs_reverse]
      exact List.mem_map.mpr ⟨f, List.mem_reverse.mpr hf, rfl⟩
    have h := pair_eq_of_touch_head (List.nodup_reverse.mpr hn)
      (by simpa only [List.head?_reverse] using hp)
      hre hrf hep.symm hfp.symm
    simpa only [Prod.swap_swap] using congrArg Prod.swap h

end PushPuzzle.Orthogonal
