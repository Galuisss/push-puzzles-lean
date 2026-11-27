/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortHoleLocality
public import PushS.PortWideFreeze
public import PushS.FreezePaths
public import PushS.PortCentralFreeze
import all PushS.PortBackground
import all PushS.PortSegmentBounds
import all PushS.PortTwoPageStreets
import all PushS.PortStreetSeparation
import all PushS.PortCentralStrip

/-! Concrete full horizontal bars surrounding the permanent wide separator holes. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Original geometric blockers together with all actual permanent wide separator holes. -/
@[expose] noncomputable def wideBlockers (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := l.geometricBlockers p ∪ l.wideSeparatorHoles p

/-- Full cells on a wide separator's row within one global hole budget of that separator. -/
@[expose] noncomputable def wideMiddleBoxes (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q ∉ l.wideSeparatorHoles p ∧
    ∃ g ∈ l.wideSeparatorHoles p, q.2 = g.2 ∧ Nat.dist q.1.val g.1.val ≤ p.b p.levels

private theorem mem_wideMiddleBoxes (l : PortLayout) (p : Scales.Parameters)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.wideMiddleBoxes p ↔ q ∉ l.wideSeparatorHoles p ∧
      ∃ g ∈ l.wideSeparatorHoles p, q.2 = g.2 ∧ Nat.dist q.1.val g.1.val ≤ p.b p.levels := by
  classical
  simp only [wideMiddleBoxes, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem budget_branch_margin (p : Scales.Parameters) : p.L p.levels + 3 ≤ p.b p.levels := by
  have h := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
    (show 1 ≤ 8 * (p.axes + 1) by omega)
  simp only [Nat.one_mul] at h
  unfold Scales.Parameters.b
  omega

private theorem near_wide_column_gap (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p)
    (hq : Nat.dist q.1.val g.1.val ≤ p.b p.levels) :
    ∀ x ∈ l.streetColumnSet p, p.b p.levels + 2 < Nat.dist q.1.val x.val := by
  intro x hx
  have hd := l.wideSeparatorHoles_street_gap p hl hg x hx
  simp only [Nat.dist] at hd hq ⊢
  omega

private theorem near_wide_not_column (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p)
    (hq : Nat.dist q.1.val g.1.val ≤ p.b p.levels) : q.1 ∉ l.streetColumnSet p := by
  intro hx
  have hd := near_wide_column_gap l p hl hg hq q.1 hx
  simp only [Nat.dist_self] at hd
  omega

private theorem wideMiddle_off_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideMiddleBoxes p) : q ∉ Boundary.frame := by
  obtain ⟨_, g, hg, hy, hd⟩ := (mem_wideMiddleBoxes l p q).mp hq
  have hx := near_wide_not_column l p hl hg hd
  have hgf := l.wideSeparatorHoles_off_frame p hl hg
  intro hf
  obtain ⟨d, he⟩ := (Boundary.mem_frame q).mp hf
  cases d with
  | north =>
    apply hgf ((Boundary.mem_frame g).mpr ⟨.north, ?_⟩)
    simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hy] using he
  | south =>
    apply hgf ((Boundary.mem_frame g).mpr ⟨.south, ?_⟩)
    simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hy] using he
  | east =>
    have he' : q.1.val = p.W := by
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at he
      omega
    apply hx
    change q.1.val ∈ streetColumns l (coordinates p)
    simp [streetColumns, coordinates, he']
  | west =>
    have he' : q.1.val = 0 := by simpa [Boundary.edge] using he
    apply hx
    change q.1.val ∈ streetColumns l (coordinates p)
    simp [streetColumns, he']

private theorem wideMiddle_not_central (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideMiddleBoxes p) : q ∉ l.centralMarkers p := by
  obtain ⟨_, g, hg, hy, _⟩ := (mem_wideMiddleBoxes l p q).mp hq
  have hrow := l.workingRowSet_central_gap p (l.wideSeparatorHoles_working_row p hg)
  have hy' := congrArg Fin.val hy
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  intro hc
  obtain ⟨_, hb, hb'⟩ := Finset.mem_filter.mp hc
  omega

/-- Every cell of the computed wide middle bars is occupied in the actual initial instance. -/
theorem wideMiddleBoxes_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    l.wideMiddleBoxes p ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨hw, g, hg, _, hd⟩ := (mem_wideMiddleBoxes l p q).mp hq
  apply l.encodedSegments_far_from_page_columns_full p hl .upper initial _
    (l.physicalInstance_initial_holes p hl hM ha initial target)
    (wideMiddle_off_frame l p hl hq) (wideMiddle_not_central l p hq) hw
  intro x hx
  have hle := pageColumn_le l p hl ha .upper hx
  let col : Fin (p.W + 1) := ⟨x, by omega⟩
  have hc : col ∈ l.streetColumnSet p := pageColumn_mem_street l p hl .upper hx
  have hgap := near_wide_column_gap l p hl hg hd col hc
  have hb := budget_branch_margin p
  dsimp only [col] at hgap
  omega

private theorem wideMiddle_north_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideMiddleBoxes p) :
    ∃ r, Adjacent .north q r ∧ r ∈ l.wideBlockers p := by
  obtain ⟨_, g, hg, hy, hd⟩ := (mem_wideMiddleBoxes l p q).mp hq
  have hqf := wideMiddle_off_frame l p hl hq
  have hy0 : 0 < q.2.val := by
    by_contra h
    apply hqf ((Boundary.mem_frame q).mpr ⟨.north, ?_⟩)
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  let r : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨q.2.val - 1, by have := q.2.isLt; omega⟩)
  have ha : Adjacent .north q r := ⟨rfl, by change q.2.val - 1 + 1 = q.2.val; omega⟩
  have he := l.workingRowSet_even p (l.wideSeparatorHoles_working_row p hg)
  have hnc := near_wide_not_column l p hl hg hd
  have hnr : r.2 ∉ l.workingRowSet p := by
    intro hr
    have her := l.workingRowSet_even p hr
    have hey := congrArg Fin.val hy
    dsimp only [r] at her
    omega
  have hstreet : r ∉ Support.streets (l.streetColumnSet p) (l.workingRowSet p) :=
    fun h => h.elim hnc hnr
  refine ⟨r, ha, Finset.mem_union_left _ ?_⟩
  by_cases hc : r ∈ l.centralMarkers p
  · exact Finset.mem_union_left _ hc
  · exact Finset.mem_union_right _ ((l.mem_backgroundBoxes p r).mpr ⟨hstreet, hc⟩)

private theorem wide_row_point (l : PortLayout) (p : Scales.Parameters)
    (g q : Cell (p.W + 1) (p.H + 1)) (hg : g ∈ l.wideSeparatorHoles p)
    (hy : q.2 = g.2) (hd : Nat.dist q.1.val g.1.val ≤ p.b p.levels) :
    q ∈ l.wideMiddleBoxes p ∨ q ∈ l.wideBlockers p := by
  by_cases hq : q ∈ l.wideSeparatorHoles p
  · exact Or.inr (Finset.mem_union_right _ hq)
  · exact Or.inl ((mem_wideMiddleBoxes l p q).mpr ⟨hq, g, hg, hy, hd⟩)

private theorem east_wide_ray (l : PortLayout) (p : Scales.Parameters)
    (q g : Cell (p.W + 1) (p.H + 1)) (hg : g ∈ l.wideSeparatorHoles p)
    (hy : q.2 = g.2) (hd : Nat.dist q.1.val g.1.val ≤ p.b p.levels) (hx : q.1.val < g.1.val) :
    Freeze.Ray (l.wideMiddleBoxes p) (l.wideBlockers p) .east q := by
  apply Freeze.Ray.east_of_interval hy hx (Finset.mem_union_right _ hg)
  intro r hr hleft hright
  apply wide_row_point l p g r hg (hr.trans hy)
  simp only [Nat.dist] at hd ⊢
  omega

private theorem west_wide_ray (l : PortLayout) (p : Scales.Parameters)
    (q g : Cell (p.W + 1) (p.H + 1)) (hg : g ∈ l.wideSeparatorHoles p)
    (hy : q.2 = g.2) (hd : Nat.dist q.1.val g.1.val ≤ p.b p.levels) (hx : g.1.val < q.1.val) :
    Freeze.Ray (l.wideMiddleBoxes p) (l.wideBlockers p) .west q := by
  apply Freeze.Ray.west_of_interval hy hx (Finset.mem_union_right _ hg)
  intro r hr hleft hright
  apply wide_row_point l p g r hg (hr.trans hy)
  simp only [Nat.dist] at hd ⊢
  omega

/-- The actual full wide middle bars reach a wide separator horizontally and frozen background
vertically, so every component has an established blocked end. -/
theorem wideMiddleBoxes_anchored (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Freeze.Anchored (l.wideMiddleBoxes p) (l.wideBlockers p) := by
  intro d q hq
  obtain ⟨hw, g, hg, hy, hd⟩ := (mem_wideMiddleBoxes l p q).mp hq
  have hneq : q.1.val ≠ g.1.val := by
    intro he
    have heq : q = g := Prod.ext (Fin.ext he) hy
    exact hw (heq ▸ hg)
  have hh : Freeze.Ray (l.wideMiddleBoxes p) (l.wideBlockers p) .east q ∨
      Freeze.Ray (l.wideMiddleBoxes p) (l.wideBlockers p) .west q := by
    rcases lt_or_gt_of_ne hneq with h | h
    · exact Or.inl (east_wide_ray l p q g hg hy hd h)
    · exact Or.inr (west_wide_ray l p q g hg hy hd h)
  obtain ⟨r, ha, hr⟩ := wideMiddle_north_blocker l p hl hq
  have hn : Freeze.Ray (l.wideMiddleBoxes p) (l.wideBlockers p) .north q := .hit ha hr
  cases d with
  | north => exact Or.inl hn
  | south => exact Or.inr hn
  | east => exact hh
  | west => exact hh.symm

/-- The actual wide middle bars form a concrete freezing closure over the permanent holes. -/
theorem wideMiddleBoxes_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.wideBlockers p)
      (l.wideBlockers p ∪ l.wideMiddleBoxes p) :=
  .add (.refl _) (l.wideMiddleBoxes_initial_full p hl hM ha initial target)
    (l.wideMiddleBoxes_anchored p hl)

/-- Blockers after freezing the actual central auxiliary columns and wide middle bars. -/
@[expose] noncomputable def wideFrozenBlockers (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (l.wideBlockers p ∪ l.centralAuxiliaryBoxes p) ∪ l.wideMiddleBoxes p

/-- The two actual geometric freezing stages form one concrete closure certificate. -/
theorem wideBackground_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.wideBlockers p)
      (l.wideFrozenBlockers p) :=
  .add (.add (.refl _) (l.centralAuxiliaryBoxes_initial_full p hl hM ha initial target)
      ((l.centralAuxiliaryBoxes_anchored p).mono_blockers (fun _ h => Finset.mem_union_left _ h)))
    (l.wideMiddleBoxes_initial_full p hl hM ha initial target)
    ((l.wideMiddleBoxes_anchored p hl).mono_blockers (fun _ h => Finset.mem_union_left _ h))

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

private theorem step_wide_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hm : Step (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Freeze.AvoidingStep (l.physicalInstance p hl hM ha initial target).board none (l.wideBlockers p) u v := by
  have hgeo := l.physicalInstance_step_avoiding p hl hM ha initial target hsu hm hvt ht
  have hWu := l.physicalInstance_wide_excluded_at p hl hM ha initial target hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hWv := l.physicalInstance_wide_excluded_at p hl hM ha initial target (hsu.tail hm) hvt ht
  refine ⟨hm, ?_⟩
  intro d n r hn hp hb i hi
  exact (Finset.mem_union.mp hi).elim
    (hgeo.2 d n r hn hp hb i) (Blocked.run_avoids r hWu hWv hb i)

/-- Actual solution prefixes avoid both the initial geometry and the proved permanent wide holes. -/
theorem physicalInstance_wide_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.wideBlockers p))
      (l.physicalInstance p hl hM ha initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact step_wide_avoiding l p hl hM ha initial target hsa hm (hbu.trans hut) ht

/-- Every actual wide middle bar remains full at every solution prefix. -/
theorem physicalInstance_wide_middle_full {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.wideMiddleBoxes p ⊆ u.boxes :=
  (Freeze.anchored_closure (l.wideMiddleBoxes_anchored p hl)
    (l.physicalInstance_wide_avoiding_prefix p hl hM ha initial target hsu hut ht)
    (l.wideMiddleBoxes_initial_full p hl hM ha initial target)).1

/-- Every solution prefix avoids the full computed background freezing closure. -/
theorem physicalInstance_wide_background_avoiding {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.wideFrozenBlockers p))
      (l.physicalInstance p hl hM ha initial target).initial u :=
  (l.wideBackground_closure p hl hM ha initial target).reachable
    (l.physicalInstance_wide_avoiding_prefix p hl hM ha initial target hsu hut ht)

/-- A complete physical lifting fixes each original box in the computed frozen background. -/
theorem physicalInstance_wide_background_frozen {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (l.physicalInstance p hl hM ha initial target).initial)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ T : LabelledState ι (p.W + 1) (p.H + 1), T.state = t ∧
      Labels.GuardedReachable (l.physicalInstance p hl hM ha initial target).board none
        (l.wideFrozenBlockers p) S T ∧
      ∀ i, S.position i ∈ l.wideFrozenBlockers p → T.position i = S.position i := by
  have hguard := l.physicalInstance_wide_background_avoiding p hl hM ha initial target hr .refl ht
  rw [← hS] at hguard
  obtain ⟨T, hT, hlabels⟩ := Labels.lift_guarded hguard
  exact ⟨T, hT, hlabels, hlabels.position⟩

end Solution
end PushPuzzle.PushS.PortLayout
