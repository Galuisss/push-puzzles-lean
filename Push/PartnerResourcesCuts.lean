/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResources
import all Push.PartnerCutsValidity

/-! Actual interval loads before, inside, and after a common-cut block. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS PageLevels

private theorem countP_flatMap_single {α β : Type} (xs : List α) (f : α → List β)
    (p : β → Bool) (q : α → Bool) (h : ∀ a ∈ xs, (f a).countP p = if q a = true then 1 else 0) :
    (xs.flatMap f).countP p = xs.countP q := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    omega

private theorem countP_flatMap_le {α β : Type} (xs : List α) (f : α → List β) (p : β → Bool)
    (h : ∀ a ∈ xs, (f a).countP p ≤ 1) : (xs.flatMap f).countP p ≤ xs.length := by
  induction xs with
  | nil => exact le_rfl
  | cons a rest ih =>
    have ha := h a List.mem_cons_self
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    omega

private theorem gapTest_shift_before (cut count gap : ℕ) (hg : gap < cut) (ab : ℕ × ℕ) :
    gapTest gap (Cuts.mapPair cut count ab) = gapTest gap ab := by
  apply Bool.eq_iff_iff.mpr
  simp only [gapTest, Cuts.mapPair, decide_eq_true_eq]
  unfold Cuts.shift
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

private theorem gapTest_shift_after (cut count gap : ℕ) (hg : cut + 2 * count ≤ gap) (ab : ℕ × ℕ) :
    gapTest gap (Cuts.mapPair cut count ab) = gapTest (gap - 2 * count) ab := by
  apply Bool.eq_iff_iff.mpr
  simp only [gapTest, Cuts.mapPair, decide_eq_true_eq]
  unfold Cuts.shift
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

private theorem upperPiece_before {l : PortLayout} {cut gap : ℕ} (hg : gap < cut)
    {p : (ℕ × ℕ) × ℕ} (hp : p ∈ (Cuts.active l cut).zipIdx) :
    (Cuts.upperPiece cut (Cuts.active l cut).length p).countP (gapTest gap) =
      if gapTest gap p.1 = true then 1 else 0 := by
  obtain ⟨_, hpa, hpb⟩ := (Cuts.mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
  have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hl := Cuts.left_bounds (cut := cut) hj
  have hr := Cuts.right_bounds (cut := cut) hj
  have hleft : gapTest gap (Cuts.shift cut (Cuts.active l cut).length p.1.1, Cuts.left cut (Cuts.active l cut).length p.2) =
      gapTest gap p.1 := by
    apply Bool.eq_iff_iff.mpr
    simp only [gapTest, decide_eq_true_eq, Cuts.shift, ite_eq_left hpa]
    omega
  have hright : gapTest gap (Cuts.right cut (Cuts.active l cut).length p.2, Cuts.shift cut (Cuts.active l cut).length p.1.2) = false := by
    simp only [gapTest, decide_eq_false_iff_not]
    omega
  simp only [Cuts.upperPiece, List.countP_cons, List.countP_nil, hleft, hright, Bool.false_eq_true,
    ite_false, Nat.zero_add, Nat.add_zero]

private theorem upperPiece_after {l : PortLayout} {cut gap : ℕ}
    (hg : cut + 2 * (Cuts.active l cut).length ≤ gap) {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ (Cuts.active l cut).zipIdx) :
    (Cuts.upperPiece cut (Cuts.active l cut).length p).countP (gapTest gap) =
      if gapTest (gap - 2 * (Cuts.active l cut).length) p.1 = true then 1 else 0 := by
  obtain ⟨_, hpa, hpb⟩ := (Cuts.mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
  have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hl := Cuts.left_bounds (cut := cut) hj
  have hr := Cuts.right_bounds (cut := cut) hj
  have hleft : gapTest gap (Cuts.shift cut (Cuts.active l cut).length p.1.1, Cuts.left cut (Cuts.active l cut).length p.2) = false := by
    simp only [gapTest, decide_eq_false_iff_not]
    omega
  have hright : gapTest gap (Cuts.right cut (Cuts.active l cut).length p.2, Cuts.shift cut (Cuts.active l cut).length p.1.2) =
      gapTest (gap - 2 * (Cuts.active l cut).length) p.1 := by
    apply Bool.eq_iff_iff.mpr
    simp only [gapTest, decide_eq_true_eq, Cuts.shift, ite_eq_right (show ¬p.1.2 < cut by omega)]
    omega
  simp only [Cuts.upperPiece, List.countP_cons, List.countP_nil, hleft, hright, Bool.false_eq_true,
    ite_false, Nat.zero_add, Nat.add_zero]

private theorem active_countP_zip (l : PortLayout) (cut gap : ℕ) :
    ((Cuts.active l cut).zipIdx.countP (fun p => gapTest gap p.1)) = (Cuts.active l cut).countP (gapTest gap) := by
  change (Cuts.active l cut).zipIdx.countP ((gapTest gap) ∘ Prod.fst) = _
  rw [← List.countP_map, List.zipIdx_map_fst]

/-- Every old gap strictly before a cut retains its exact upper active count, on arbitrary raw inputs. -/
private theorem cut_upperLoad_before (l : PortLayout) {cut gap : ℕ} (hg : gap < cut) :
    upperLoad (Cuts.compile l cut) gap = upperLoad l gap := by
  have hp := List.Perm.countP_eq (gapTest gap) (Cuts.active_passive_perm l cut)
  rw [List.countP_append] at hp
  unfold upperLoad
  change ((Cuts.active l cut).zipIdx.flatMap (Cuts.upperPiece cut (Cuts.active l cut).length) ++
    (Cuts.passive l cut).map (Cuts.mapPair cut (Cuts.active l cut).length)).countP _ = _
  rw [List.countP_append, countP_flatMap_single _ _ _ (fun p => gapTest gap p.1) (fun _ hp => upperPiece_before hg hp),
    active_countP_zip, List.countP_map]
  have he : (Cuts.passive l cut).countP ((gapTest gap) ∘ Cuts.mapPair cut (Cuts.active l cut).length) =
      (Cuts.passive l cut).countP (gapTest gap) := by
    apply List.countP_congr
    intro ab _
    rw [Function.comp_apply, gapTest_shift_before cut _ gap hg ab]
  rw [he]
  exact hp

/-- Every old gap beyond the inserted block retains its original upper active count. -/
private theorem cut_upperLoad_after (l : PortLayout) {cut gap : ℕ}
    (hg : cut + 2 * (Cuts.active l cut).length ≤ gap) :
    upperLoad (Cuts.compile l cut) gap = upperLoad l (gap - 2 * (Cuts.active l cut).length) := by
  have hp := List.Perm.countP_eq (gapTest (gap - 2 * (Cuts.active l cut).length)) (Cuts.active_passive_perm l cut)
  rw [List.countP_append] at hp
  unfold upperLoad
  change ((Cuts.active l cut).zipIdx.flatMap (Cuts.upperPiece cut (Cuts.active l cut).length) ++
    (Cuts.passive l cut).map (Cuts.mapPair cut (Cuts.active l cut).length)).countP _ = _
  rw [List.countP_append, countP_flatMap_single _ _ _
    (fun p => gapTest (gap - 2 * (Cuts.active l cut).length) p.1) (fun _ hp => upperPiece_after hg hp),
    active_countP_zip, List.countP_map]
  have he : (Cuts.passive l cut).countP ((gapTest gap) ∘ Cuts.mapPair cut (Cuts.active l cut).length) =
      (Cuts.passive l cut).countP (gapTest (gap - 2 * (Cuts.active l cut).length)) := by
    apply List.countP_congr
    intro ab _
    rw [Function.comp_apply, gapTest_shift_after cut _ gap hg ab]
  rw [he]
  exact hp

/-- At most one of a source arc's two upper fragments crosses any one gap. -/
private theorem upperPiece_load_le_one {l : PortLayout} {cut gap : ℕ} {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ (Cuts.active l cut).zipIdx) : (Cuts.upperPiece cut (Cuts.active l cut).length p).countP (gapTest gap) ≤ 1 := by
  have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hsep := Cuts.left_lt_right (cut := cut) hj
  simp only [Cuts.upperPiece, List.countP_cons, List.countP_nil, gapTest, decide_eq_true_eq]
  split_ifs <;> omega

/-- Every upper gap inside a fresh block fits the original cut's active-arc count. -/
private theorem cut_upperLoad_inside (l : PortLayout) {cut gap : ℕ}
    (hg : cut ≤ gap ∧ gap < cut + 2 * (Cuts.active l cut).length) :
    upperLoad (Cuts.compile l cut) gap ≤ (Cuts.active l cut).length := by
  have hnew := countP_flatMap_le (Cuts.active l cut).zipIdx (Cuts.upperPiece cut (Cuts.active l cut).length)
    (gapTest gap) (fun _ hp => upperPiece_load_le_one hp)
  have hold : ((Cuts.passive l cut).map (Cuts.mapPair cut (Cuts.active l cut).length)).countP (gapTest gap) = 0 := by
    apply List.countP_eq_zero.mpr
    intro ab hab
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hab
    have hnot := ((Cuts.mem_passive l cut old).mp hold).2
    simp only [gapTest, Cuts.mapPair]
    unfold Cuts.shift
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  unfold upperLoad
  change ((Cuts.active l cut).zipIdx.flatMap (Cuts.upperPiece cut (Cuts.active l cut).length) ++
    (Cuts.passive l cut).map (Cuts.mapPair cut (Cuts.active l cut).length)).countP (gapTest gap) ≤ _
  rw [List.countP_append, hold, Nat.add_zero]
  simpa only [List.length_zipIdx] using hnew

/-- A real common cut never increases the upper page's constant active-arc budget. -/
theorem cut_upperLoad_le {l : PortLayout} {bound : ℕ} (hbound : ∀ gap, upperLoad l gap ≤ bound) (cut gap : ℕ) :
    upperLoad (Cuts.compile l cut) gap ≤ bound := by
  by_cases hbefore : gap < cut
  · rw [cut_upperLoad_before l hbefore]
    exact hbound gap
  by_cases hafter : cut + 2 * (Cuts.active l cut).length ≤ gap
  · rw [cut_upperLoad_after l hafter]
    exact hbound _
  have hc : 0 < cut := by
    by_contra hc
    have he : cut = 0 := by omega
    rw [he, cut_active_zero] at hafter
    omega
  exact (cut_upperLoad_inside l ⟨by omega, by omega⟩).trans
    (by rw [cut_active_length l hc]; exact hbound _)

end PushPuzzle.Push.Partner.Resources
