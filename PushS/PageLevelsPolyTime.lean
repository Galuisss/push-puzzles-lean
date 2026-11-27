/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEncoding
import Mathlib.Data.List.Fold
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Fin

/-!
# Finite-list computation of the actual page levels

Count active and ancestor groups in the supplied lists, preserving repeated positions.
A maximum fold over the actual gaps computes the same active bound as the finite-set
definition. The two resulting arrays agree exactly with `PageLevels.Pages.levels` on all
raw pages.

## Main results

* `Pages.computedLevels_eq`: the finite-list algorithm gives the actual level arrays.
-/

public section

namespace PushPuzzle.PushS.PageLevels


open _root_.Turing.MultiTapeTM

private def activeCount (p : Page) (k : ℕ) : ℕ :=
  p.groups.countP fun g => decide (g.left ≤ k ∧ k < g.right)

private def ancestorCount (p : Page) (g : Group) : ℕ :=
  p.groups.countP fun outer => decide (outer.Contains g)

private def maximumActive (p : Page) : ℕ :=
  ((List.range (p.portCount - 1)).map (activeCount p)).foldl max 0

private def groupDepth (p : Page) (g : Group) : ℕ := maximumActive p - ancestorCount p g

private def groupPorts : Group → List ℕ
  | .wire a b => [a, b]
  | .triple a => [a, a + 1, a + 2]

private def middleTest : Group × ℕ → Bool
  | (.wire .., _) => false
  | (.triple a, k) => decide (k = a + 1)

private def middleUsed (p : Pages) (g : Group) : Bool :=
  p.lower.any fun lower => (groupPorts g).any fun k => middleTest (lower, k)

private def computedUpper (p : Pages) (g : Group) : ℕ :=
  let d := groupDepth p.upperPage g
  if middleUsed p g then 2 * d else 2 * d - 1

private def computedLower (p : Page) (g : Group) : ℕ :=
  match g with
  | .wire .. => groupDepth p g + 1
  | .triple _ => 1

/-- Count, fold and map the actual input lists to obtain both working-level arrays. -/
def Pages.computedLevels (p : Pages) : List ℕ × List ℕ :=
  (p.upper.map (computedUpper p), p.lower.map (computedLower p.lowerPage))

private theorem ofFn_group (p : Page) : List.ofFn p.group = p.groups :=
  List.ofFn_get p.groups

private theorem activeCount_eq (p : Page) (k : ℕ) : activeCount p k = (p.active k).card := by
  unfold activeCount
  rw [← ofFn_group p, List.countP_ofFn]
  simp only [Page.active, decide_eq_true_eq]

private theorem ancestorCount_eq (p : Page) (i : p.Index) :
    ancestorCount p (p.group i) = (p.ancestors i).card := by
  unfold ancestorCount
  rw [← ofFn_group p, List.countP_ofFn]
  simp only [Page.ancestors, decide_eq_true_eq]

private theorem maximumActive_eq (p : Page) : maximumActive p = p.maxActive := by
  have hr : (List.range (p.portCount - 1)).toFinset = Finset.range (p.portCount - 1) := by
    ext k
    simp
  have hm : ((List.range (p.portCount - 1)).map (activeCount p)).toFinset =
      (List.range (p.portCount - 1)).toFinset.image (activeCount p) := by
    ext k
    simp
  unfold maximumActive Page.maxActive
  rw [List.foldl_eq_foldr]
  change (List.map (activeCount p) _).foldr (· ⊔ ·) ⊥ = _
  rw [List.foldr_sup_eq_sup_toFinset]
  simp only [hm, Finset.sup_image, hr, Function.comp_def, id_eq, activeCount_eq]

private theorem groupDepth_eq (p : Page) (i : p.Index) :
    groupDepth p (p.group i) = p.depth i := by
  simp only [groupDepth, Page.depth, maximumActive_eq, ancestorCount_eq]

private theorem mem_groupPorts (g : Group) (k : ℕ) : k ∈ groupPorts g ↔ k ∈ g.ports := by
  cases g <;> simp [groupPorts, Group.ports]

private theorem middleTest_eq_true (g : Group) (k : ℕ) :
    middleTest (g, k) = true ↔ k ∈ g.middles := by
  cases g <;> simp [middleTest, Group.middles]

private theorem mem_middlePorts (p : Page) (k : ℕ) :
    k ∈ p.middlePorts ↔ ∃ g ∈ p.groups, k ∈ g.middles := by
  simp only [Page.middlePorts, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨p.group i, List.get_mem _ _, hi⟩
  · rintro ⟨g, hg, hk⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    exact ⟨i, hk⟩

private theorem middleUsed_eq (p : Pages) (i : p.upperPage.Index) :
    middleUsed p (p.upperPage.group i) = decide (p.UsesMiddle i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [middleUsed, List.any_eq_true, middleTest_eq_true, mem_groupPorts,
    decide_eq_true_eq, Pages.UsesMiddle, Finset.Nonempty, Finset.mem_inter,
    mem_middlePorts, Pages.lowerPage]
  constructor
  · rintro ⟨g, hg, k, hk, hm⟩
    exact ⟨k, hk, g, hg, hm⟩
  · rintro ⟨k, hk, g, hg, hm⟩
    exact ⟨g, hg, k, hk, hm⟩

private theorem computedUpper_eq (p : Pages) (i : p.upperPage.Index) :
    computedUpper p (p.upperPage.group i) = p.upperLevel i := by
  simp only [computedUpper, Pages.upperLevel, groupDepth_eq, middleUsed_eq,
    decide_eq_true_eq]

private theorem computedLower_eq (p : Pages) (i : p.lowerPage.Index) :
    computedLower p.lowerPage (p.lowerPage.group i) = p.lowerLevel i := by
  unfold computedLower Pages.lowerLevel
  rw [groupDepth_eq]
  cases p.lowerPage.group i <;> rfl

/-- Both concrete list arrays are exactly the finite-set-defined page levels. -/
private theorem Pages.computedLevels_eq (p : Pages) : p.computedLevels = p.levels := by
  apply Prod.ext
  · change p.upper.map (computedUpper p) = List.ofFn p.upperLevel
    rw [← List.ofFn_get p.upper, List.map_ofFn]
    exact List.ofFn_inj.mpr (funext fun i => computedUpper_eq p i)
  · change p.lower.map (computedLower p.lowerPage) = List.ofFn p.lowerLevel
    rw [← List.ofFn_get p.lower, List.map_ofFn]
    exact List.ofFn_inj.mpr (funext fun i => computedLower_eq p i)

open scoped PushPuzzle.PushS.PageLevels

@[local fun_prop] private theorem left_polyTime :
    ComputableInPolyTime Group.left encGroup encUnary := by
  have h := encGroup_elim_polyTime (encP := encUnit) (encE := encUnary)
    (g0 := fun p => p.2.1) (g1 := fun p => p.2) (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun g : Group => ((), g))
    encGroup (encPair encUnit encGroup) from by fun_prop)
  exact hh.of_enc_eq (by intro g; cases g <;> rfl)

@[local fun_prop] private theorem right_polyTime :
    ComputableInPolyTime Group.right encGroup encUnary := by
  have h := encGroup_elim_polyTime (encP := encUnit) (encE := encUnary)
    (g0 := fun p => p.2.2) (g1 := fun p => p.2 + 2) (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun g : Group => ((), g))
    encGroup (encPair encUnit encGroup) from by fun_prop)
  exact hh.of_enc_eq (by intro g; cases g <;> rfl)

@[local fun_prop] private theorem groupPorts_polyTime :
    ComputableInPolyTime groupPorts encGroup (encList encUnary) := by
  have h := encGroup_elim_polyTime (encP := encUnit) (encE := encList encUnary)
    (g0 := fun p => [p.2.1, p.2.2]) (g1 := fun p => [p.2, p.2 + 1, p.2 + 2])
    (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun g : Group => ((), g))
    encGroup (encPair encUnit encGroup) from by fun_prop)
  exact hh.of_enc_eq (by intro g; cases g <;> rfl)

@[local fun_prop] private theorem middleTest_polyTime :
    ComputableInPolyTime middleTest (encPair encGroup encUnary) encBool := by
  have h := encGroup_elim_polyTime (encP := encUnary) (encE := encBool)
    (g0 := fun _ => false) (g1 := fun p => decide (p.1 = p.2 + 1))
    (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun p : Group × ℕ => (p.2, p.1))
    (encPair encGroup encUnary) (encPair encUnary encGroup) from by fun_prop)
  exact hh.of_enc_eq (by intro p; rcases p with ⟨g, k⟩; cases g <;> rfl)

@[local fun_prop] private theorem activeCount_polyTime :
    ComputableInPolyTime (fun p : Page × ℕ => activeCount p.1 p.2)
      (encPair encPage encUnary) encUnary := by
  unfold activeCount
  fun_prop

@[local fun_prop] private theorem ancestorCount_polyTime :
    ComputableInPolyTime (fun p : Page × Group => ancestorCount p.1 p.2)
      (encPair encPage encGroup) encUnary := by
  unfold ancestorCount Group.Contains
  fun_prop

@[local fun_prop] private theorem maximumActive_polyTime :
    ComputableInPolyTime maximumActive encPage encUnary := by
  unfold maximumActive
  exact (ComputableInPolyTime.unary_foldl_max 0).comp (by fun_prop)

@[local fun_prop] private theorem groupDepth_polyTime :
    ComputableInPolyTime (fun p : Page × Group => groupDepth p.1 p.2)
      (encPair encPage encGroup) encUnary := by
  unfold groupDepth
  fun_prop

@[local fun_prop] private theorem middleUsed_polyTime :
    ComputableInPolyTime (fun p : Pages × Group => middleUsed p.1 p.2)
      (encPair encPages encGroup) encBool := by
  unfold middleUsed
  fun_prop

@[local fun_prop] private theorem upperPage_polyTime :
    ComputableInPolyTime Pages.upperPage encPages encPage := by
  unfold Pages.upperPage
  fun_prop

@[local fun_prop] private theorem lowerPage_polyTime :
    ComputableInPolyTime Pages.lowerPage encPages encPage := by
  unfold Pages.lowerPage
  fun_prop

@[local fun_prop] private theorem computedUpper_polyTime :
    ComputableInPolyTime (fun p : Pages × Group => computedUpper p.1 p.2)
      (encPair encPages encGroup) encUnary := by
  unfold computedUpper
  fun_prop

@[local fun_prop] private theorem computedLower_polyTime :
    ComputableInPolyTime (fun p : Page × Group => computedLower p.1 p.2)
      (encPair encPage encGroup) encUnary := by
  have h := encGroup_elim_polyTime (encP := encPage) (encE := encUnary)
    (g0 := fun p => groupDepth p.1 (.wire p.2.1 p.2.2) + 1)
    (g1 := fun _ => 1) (by fun_prop) (by fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨page, g⟩; cases g <;> rfl)

/-- The actual page-level arrays, including raw inputs with repeated groups, are computed
in polynomial time from their native framed-list encoding. -/
@[fun_prop] theorem computableInPolyTime_levels :
    ComputableInPolyTime Pages.levels encPages (encPair (encList encUnary) (encList encUnary)) := by
  have h : ComputableInPolyTime Pages.computedLevels encPages
      (encPair (encList encUnary) (encList encUnary)) := by
    unfold Pages.computedLevels
    fun_prop
  exact h.of_enc_eq (fun p => congrArg _ p.computedLevels_eq.symm)

end PushPuzzle.PushS.PageLevels
