/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortConstraintGraph
import all PushS.PortConstraintGraph

/-!
# Native edge bounds of the actual constraint records

The existing numerical group bounds retain every original axis in the standard graph's finite
edge interval. The actual contour compiler supplies these bounds directly from the original
native graph and its original drawing array counts.

## Main results

* `PortLayout.graphData_bounded`: actual group bounds give standard native boundedness.
-/

public section

namespace PushPuzzle.PushS

open Cslib.Complexity

namespace PortLayout

private theorem member_bounds {p : PageLevels.Page}
    (h : ∀ i : p.Index, (p.group i).left < (p.group i).right ∧ (p.group i).right < p.portCount)
    {g : PageLevels.Group} (hg : g ∈ p.groups) : g.left < g.right ∧ g.right < p.portCount := by
  rcases List.mem_iff_get.mp hg with ⟨i, hi⟩
  simpa only [PageLevels.Page.group, hi] using h i

/-- Original group bounds retain every actual port in the standard native edge interval. -/
theorem graphData_bounded (l : PortLayout)
    (hu : ∀ i : l.pages.upperPage.Index,
      (l.pages.upperPage.group i).left < (l.pages.upperPage.group i).right ∧
        (l.pages.upperPage.group i).right < l.portCount)
    (hl : ∀ i : l.pages.lowerPage.Index,
      (l.pages.lowerPage.group i).left < (l.pages.lowerPage.group i).right ∧
        (l.pages.lowerPage.group i).right < l.portCount) : l.graphData.Bounded := by
  intro v hv pw hp
  change v ∈ l.upperPairs.map upperVertex ++ l.lowerGroups.map lowerVertex at hv
  change pw.1.edge < l.portCount
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hv
    have hm : PageLevels.Group.wire a b ∈ l.pages.upperPage.groups :=
      List.mem_map.mpr ⟨(a, b), hab, rfl⟩
    have hb := member_bounds hu hm
    simp only [pages, PageLevels.Pages.upperPage, PageLevels.Group.left,
      PageLevels.Group.right] at hb
    simp only [upperVertex, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  · obtain ⟨group, hgroup, rfl⟩ := List.mem_map.mp hv
    have hm : group.shape ∈ l.pages.lowerPage.groups := List.mem_map.mpr ⟨group, hgroup, rfl⟩
    have hb := member_bounds hl hm
    cases group with
    | wire a b =>
      simp only [pages, PageLevels.Pages.lowerPage, LowerGroup.shape,
        PageLevels.Group.left, PageLevels.Group.right] at hb
      simp only [lowerVertex, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega
    | gate kind first =>
      simp only [pages, PageLevels.Pages.lowerPage, LowerGroup.shape,
        PageLevels.Group.left, PageLevels.Group.right] at hb
      cases kind <;>
        simp only [lowerVertex, gateVertex, ite_true, reduceCtorEq, ite_false,
          NCL.Vertex.and, NCL.Vertex.or, List.mem_cons, List.not_mem_nil, or_false] at hp
      all_goals rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega

/-- Valid actual pages in particular give the standard native finite-edge bounds. -/
theorem graphData_bounded_of_pages (l : PortLayout) (hl : l.pages.Valid) : l.graphData.Bounded :=
  l.graphData_bounded hl.upper.bounded hl.lower.bounded

end PortLayout

end PushPuzzle.PushS
