/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointRWall
public import PushS.PortEndpointPageWindow
import all PushS.PortEndpointRWall
import all PushS.PortEndpointCaps
import all PushS.PortEndpointWide
import all PushS.PortPageBackground
import all PushS.PortStreetSeparation
import all PushS.PortStreetSupport
import all PushS.PortSegments

/-!
# Ordinary inward walls at an arbitrary allocated level

The cap lies at depth `Y_e+1` and the horizontal row at `Y_e+2`. The actual page background
anchors every transverse component. Only the r-column cell at depth `Y_e+3` is supplied by
the already established deeper closure.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def LevelCap (p : Scales.Parameters) (e : Endpoint) (q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.1.val = EndpointStreet.r.column p e ∧
    q.2.val = (if e.side = .upper then readDepth p e.level + 1
      else p.H - (readDepth p e.level + 1))

/-- The actual inward row and r cap at this endpoint's working level, excluding permanent holes. -/
noncomputable def levelRWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (g : EndpointWideSeparator l p e (readDepth p e.level + 2)) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
    (LevelCap p e q ∨ InwardRow p e g.cell q)

private theorem mem_levelRWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (g : EndpointWideSeparator l p e (readDepth p e.level + 2)) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.levelRWall p e g ↔ q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
      (LevelCap p e q ∨ InwardRow p e g.cell q) := by
  classical
  simp only [levelRWall, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The complete emitted encoding fills the level-relative cap and inward wall initially. -/
theorem levelRWall_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e (readDepth p e.level + 2)) :
    l.levelRWall p e g ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨hc, hw, hq⟩ := (mem_levelRWall l p e g q).mp hq
  rcases hq with hcap | hrow
  · obtain ⟨hx, hy⟩ := hcap
    apply l.physicalInstance_endpoint_cap_full p hl hM ha initial target e he
    refine ⟨?_, Or.inl ⟨hx, hy⟩⟩
    have hY := readDepth_add_lt_H p e.level
    have hx0 := readLength_add_lt_x p e.port 0
    constructor
    · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
    · rw [hx, EndpointStreet.column_r]
      cases e.inward <;> simp only [Bool.false_eq_true, ite_true, ite_false, Nat.dist] <;> omega
  · by_cases hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 16
    · have hwindow := l.endpointPageWindow_of_workingDepth p e
        (endpoint_branch_depth_mem l p hl hM he) q ((congrArg Fin.val hrow.1).trans g.row) hx
      have hnot : q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) := by
        rw [l.encodedSegments_endpointPageWindow p hl hM ha initial e he q hwindow]
        have hin : if e.inward then p.x e.port < q.1.val else q.1.val < p.x e.port := by
          have hb := hrow.2
          cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb ⊢ <;> omega
        exact cap_source_not_hole l p hl hM initial e he hin (Or.inr rfl)
          ((congrArg Fin.val hrow.1).trans g.row)
      change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜ
      exact Finset.mem_compl.mpr hnot
    · apply l.encodedSegments_far_from_axes_full p hl hM initial _
        (l.physicalInstance_initial_holes p hl hM ha initial target)
        (inward_interval_off_frame l p hl ha he g hrow.1 hrow.2) hc hw
      exact inward_interval_far_axes l p hl hM ha he g hrow.2 (by omega)

private theorem level_wall_point (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : LevelCap p e q ∨ InwardRow p e g.cell q) :
    q ∈ l.levelRWall p e g ∨ q ∈ G := by
  by_cases hm : q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p
  · exact Or.inr (hpage (marker_blocker l p hl hm))
  · exact Or.inl ((mem_levelRWall l p e g q).mpr
      ⟨(not_or.mp hm).1, (not_or.mp hm).2, hq⟩)

private def levelWallCell (p : Scales.Parameters) (e : Endpoint) (x : Fin (p.W + 1)) (k : ℕ) (hk : k ≤ 3) :
    Cell (p.W + 1) (p.H + 1) :=
  (x, ⟨if e.side = .upper then readDepth p e.level + k else p.H - (readDepth p e.level + k), by
    have hm := readDepth_add_lt_H p e.level
    split <;> omega⟩)

private theorem cap_vertical_ray (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.r.column p e →
      q.2.val = (if e.side = .upper then readDepth p e.level + 3
        else p.H - (readDepth p e.level + 3)) → q ∈ G)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : LevelCap p e q) :
    Freeze.Ray (l.levelRWall p e g) G (depthDirection e.side) q := by
  let mid := levelWallCell p e q.1 2 (by omega)
  let far := levelWallCell p e q.1 3 (by omega)
  have hY := readDepth_add_lt_H p e.level
  have hy := hq.2
  have hfar : far ∈ G := hdeep far hq.1 rfl
  have ha : Adjacent (depthDirection e.side) q mid := by
    cases hs : e.side <;>
      simp only [depthDirection, mid, levelWallCell, hs, reduceCtorEq, ite_true, ite_false, Adjacent] at hy ⊢ <;>
      simp only [true_and] <;> omega
  have hb : Adjacent (depthDirection e.side) mid far := by
    cases hs : e.side <;>
      simp only [depthDirection, mid, far, levelWallCell, hs, reduceCtorEq, ite_true, ite_false, Adjacent] <;>
      simp only [true_and]; omega
  have hmid : InwardRow p e g.cell mid := by
    refine ⟨Fin.ext g.row.symm, ?_⟩
    have hx := hq.1
    rw [EndpointStreet.column_r] at hx
    have hg := g.forward
    have hx0 := readLength_add_lt_x p e.port 0
    dsimp only [mid, levelWallCell]
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx hg ⊢ <;> omega
  rcases level_wall_point l p hl e g hpage mid (Or.inr hmid) with hf | hg
  · exact .extend ha hf (.hit hb hfar)
  · exact .hit ha hg

private theorem row_vertical_ray (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.r.column p e →
      q.2.val = (if e.side = .upper then readDepth p e.level + 3
        else p.H - (readDepth p e.level + 3)) → q ∈ G)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : InwardRow p e g.cell q) :
    Freeze.Ray (l.levelRWall p e g) G .north q ∨ Freeze.Ray (l.levelRWall p e g) G .south q := by
  by_cases hx : q.1.val = EndpointStreet.r.column p e
  · let far := levelWallCell p e q.1 3 (by omega)
    have hY := readDepth_add_lt_H p e.level
    have hy := congrArg Fin.val hq.1
    rw [g.row] at hy
    have hf : far ∈ G := hdeep far hx rfl
    have ha : Adjacent (depthDirection e.side) q far := by
      cases hs : e.side <;>
        simp only [depthDirection, far, levelWallCell, hs, reduceCtorEq, ite_true, ite_false, Adjacent] at hy ⊢ <;>
        simp only [true_and] <;> omega
    have hr : Freeze.Ray (l.levelRWall p e g) G (depthDirection e.side) q := .hit ha hf
    cases hs : e.side
    · exact Or.inr (by simpa only [depthDirection, hs, ite_true] using hr)
    · exact Or.inl (by simpa only [depthDirection, hs, reduceCtorEq, ite_false] using hr)
  · have hc : q.1 ∉ l.pageColumnSet p e.side := by
      intro hc
      exact hx (by simpa only [EndpointStreet.column_r] using g.columns _ hc hq.2)
    obtain ⟨r, ha, hr⟩ := l.workingRow_north_blocker p hl e.side
      (endpoint_branch_depth_mem l p hl hM he) q ((congrArg Fin.val hq.1).trans g.row) hc
    exact Or.inl (.hit ha (hpage hr))

private theorem cap_west_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) (q : Cell (p.W + 1) (p.H + 1))
    (hq : LevelCap p e q) : ∃ r, Adjacent .west q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  have hc : q.1 ∈ l.streetColumnSet p := by
    rw [l.streetColumnSet_iff, hq.1]
    exact (auxiliary_columns l p he).2
  have hxeven := l.streetColumnSet_even p hc
  have hx0 : 0 < q.1.val := by
    have hx := hq.1
    rw [EndpointStreet.column_r] at hx
    have hm := readLength_add_lt_x p e.port 0
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx <;> omega
  let r : Cell (p.W + 1) (p.H + 1) := (⟨q.1.val - 1, by have := q.1.isLt; omega⟩, q.2)
  refine ⟨r, ⟨by change q.1.val - 1 + 1 = q.1.val; omega, rfl⟩, ?_⟩
  apply off_page_blocker l p hl
  have hnc : r.1 ∉ l.streetColumnSet p := by
    intro hr
    have heven := l.streetColumnSet_even p hr
    change (q.1.val - 1) % 2 = 0 at heven
    omega
  have hnr : r.2 ∉ l.workingRowSet p := by
    intro hr
    have heven := l.workingRowSet_even p hr
    have hy := hq.2
    have hY := readDepth_even p e.level
    have hH := H_even p
    have hm := readDepth_add_lt_H p e.level
    change q.2.val % 2 = 0 at heven
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  exact fun hp => (pages_subset_streets l p hl hp).elim hnc hnr

/-- The r-column cap is either an earlier blocker or a cell of the level wall. -/
theorem levelRWall_cap_mem (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.r.column p e)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 1
      else p.H - (readDepth p e.level + 1)) :
    q ∈ l.pageFrozenBlockers p hl ∪ l.levelRWall p e g :=
  Finset.mem_union.mpr (level_wall_point l p hl e g (fun _ h => h) q (Or.inl ⟨hx, hy⟩)).symm

/-- One inward cell behind the long public branch lies in this wall or the page blockers. -/
theorem levelRWall_branch_back_mem (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port + 1 else p.x e.port - 1)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 2
      else p.H - (readDepth p e.level + 2)) :
    q ∈ l.pageFrozenBlockers p hl ∪ l.levelRWall p e g := by
  apply Finset.mem_union.mpr
  apply Or.symm
  apply level_wall_point l p hl e g (fun _ h => h) q
  refine Or.inr ⟨Fin.ext (hy.trans g.row.symm), ?_⟩
  have hg := g.forward
  have hm := readLength_add_lt_x p e.port 0
  cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx hg ⊢ <;> omega

/-- Page blockers and the r-column's next depth anchor the entire level-relative wall. -/
theorem levelRWall_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.r.column p e →
      q.2.val = (if e.side = .upper then readDepth p e.level + 3
        else p.H - (readDepth p e.level + 3)) → q ∈ G) :
    Freeze.Anchored (l.levelRWall p e g) G := by
  intro d q hq
  obtain ⟨_, hw, hq⟩ := (mem_levelRWall l p e g q).mp hq
  have hv : Freeze.Ray (l.levelRWall p e g) G .north q ∨
      Freeze.Ray (l.levelRWall p e g) G .south q := by
    rcases hq with hcap | hrow
    · have hr := cap_vertical_ray l p hl e g hpage hdeep q hcap
      cases hs : e.side
      · exact Or.inr (by simpa only [depthDirection, hs, ite_true] using hr)
      · exact Or.inl (by simpa only [depthDirection, hs, reduceCtorEq, ite_false] using hr)
    · exact row_vertical_ray l p hl hM e he g hpage hdeep q hrow
  have hh : Freeze.Ray (l.levelRWall p e g) G .east q ∨
      Freeze.Ray (l.levelRWall p e g) G .west q := by
    rcases hq with hcap | hrow
    · obtain ⟨r, ha, hr⟩ := cap_west_blocker l p hl e he q hcap
      exact Or.inr (.hit ha (hpage hr))
    · have hneq : q.1.val ≠ g.cell.1.val := by
        intro hx
        exact hw ((Prod.ext (Fin.ext hx) hrow.1).symm ▸ g.hole)
      have hb := hrow.2
      have hg := hpage (marker_blocker l p hl (Or.inr g.hole))
      cases hi : e.inward
      · simp only [hi, Bool.false_eq_true, ite_false] at hb
        apply Or.inr
        apply Freeze.Ray.west_of_interval hrow.1 (by omega) hg
        intro r hr hleft hright
        exact level_wall_point l p hl e g hpage r (Or.inr
          ⟨hr.trans hrow.1, by simp only [hi, Bool.false_eq_true, ite_false]; omega⟩)
      · simp only [hi, ite_true] at hb
        apply Or.inl
        apply Freeze.Ray.east_of_interval hrow.1 (by omega) hg
        intro r hr hleft hright
        exact level_wall_point l p hl e g hpage r (Or.inr
          ⟨hr.trans hrow.1, by simp only [hi, ite_true]; omega⟩)
  cases d with
  | north => exact hv
  | south => exact hv.symm
  | east => exact hh
  | west => exact hh.symm

/-- An established deeper closure freezes this endpoint's actual level-relative inward wall. -/
theorem levelRWall_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e (readDepth p e.level + 2))
    (G : Finset (Cell (p.W + 1) (p.H + 1)))
    {R : Finset (Cell (p.W + 1) (p.H + 1))}
    (hc : Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial R G)
    (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.r.column p e →
      q.2.val = (if e.side = .upper then readDepth p e.level + 3
        else p.H - (readDepth p e.level + 3)) → q ∈ G) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial R (G ∪ l.levelRWall p e g) :=
  .add hc (l.levelRWall_initial_full p hl hM ha initial target e he g)
    (l.levelRWall_anchored p hl hM e he g G hpage hdeep)

end PushPuzzle.PushS.PortLayout
