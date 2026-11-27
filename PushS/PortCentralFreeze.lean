/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCentralStrip
public import PushS.PortTwoPageStreets
public import PushS.FreezePaths
import all PushS.PortCentralStrip

/-!
# Freezing the actual auxiliary columns in the full central strip

An auxiliary column has a permanent hole at the central cut. Its full strip reaches that
blocker vertically, and its horizontal neighbours belong to the frozen street background.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The full portions of non-main original columns between the two working-page bands. -/
@[expose] noncomputable def centralAuxiliaryBoxes (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q.1 ∈ l.streetColumnSet p ∧ q.1 ∉ l.mainColumnSet p ∧
    p.Y p.levels + 2 < q.2.val ∧ q.2.val + p.Y p.levels + 2 < p.H ∧ q ∉ l.centralMarkers p

private theorem mem_centralAuxiliaryBoxes (l : PortLayout) (p : Scales.Parameters)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.centralAuxiliaryBoxes p ↔ q.1 ∈ l.streetColumnSet p ∧ q.1 ∉ l.mainColumnSet p ∧
      p.Y p.levels + 2 < q.2.val ∧ q.2.val + p.Y p.levels + 2 < p.H ∧ q ∉ l.centralMarkers p := by
  classical
  simp only [centralAuxiliaryBoxes, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem blocker_of_not_street (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∉ Support.streets (l.streetColumnSet p) (l.workingRowSet p)) :
    q ∈ l.geometricBlockers p := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact Finset.mem_union_left _ hc
  · exact Finset.mem_union_right _ ((l.mem_backgroundBoxes p q).mpr ⟨hq, hc⟩)

private theorem central_west_blocker (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralAuxiliaryBoxes p) :
    ∃ r, Adjacent .west q r ∧ r ∈ l.geometricBlockers p := by
  obtain ⟨hx, hm, hy, hy', _⟩ := (mem_centralAuxiliaryBoxes l p q).mp hq
  have hx0 : q.1.val ≠ 0 := fun he => hm ((l.mainColumnSet_iff p q.1).mpr (Or.inl he))
  let r : Cell (p.W + 1) (p.H + 1) := (⟨q.1.val - 1, by have := q.1.isLt; omega⟩, q.2)
  have ha : Adjacent .west q r := by change (q.1.val - 1) + 1 = q.1.val ∧ _; exact ⟨by omega, rfl⟩
  refine ⟨r, ha, blocker_of_not_street l p ?_⟩
  rintro (hcol | hrow)
  · exact l.streetColumnSet_separated p hcol hx ha.1
  · have hb := l.workingRowSet_central_gap p hrow
    change q.2.val ≤ p.Y p.levels + 2 ∨ p.H ≤ q.2.val + p.Y p.levels + 2 at hb
    omega

private theorem central_interval_point (l : PortLayout) (p : Scales.Parameters)
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1 ∈ l.streetColumnSet p)
    (hm : q.1 ∉ l.mainColumnSet p) (hy : p.Y p.levels + 2 < q.2.val)
    (hy' : q.2.val + p.Y p.levels + 2 < p.H) :
    q ∈ l.centralAuxiliaryBoxes p ∨ q ∈ l.geometricBlockers p := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact Or.inr (Finset.mem_union_left _ hc)
  · exact Or.inl ((mem_centralAuxiliaryBoxes l p q).mpr ⟨hx, hm, hy, hy', hc⟩)

private theorem south_central_ray (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralAuxiliaryBoxes p) (hyD : q.2.val < p.D) :
    Freeze.Ray (l.centralAuxiliaryBoxes p) (l.geometricBlockers p) .south q := by
  obtain ⟨hx, hm, hy, hy', _⟩ := (mem_centralAuxiliaryBoxes l p q).mp hq
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  let n := p.D - q.2.val - 1
  let cell : Fin (n + 2) → Cell (p.W + 1) (p.H + 1) := fun i =>
    (q.1, ⟨q.2.val + i.val, by have := i.isLt; dsimp only [n] at *; omega⟩)
  have hstart : cell 0 = q := by apply Prod.ext rfl; exact Fin.ext (by simp [cell])
  rw [← hstart]
  apply Freeze.Ray.of_path cell
  · intro i
    change _ = _ ∧ _
    exact ⟨rfl, by simp only [cell, Fin.val_castSucc, Fin.val_succ]; omega⟩
  · intro i
    let r := cell ⟨i.val + 1, by omega⟩
    apply central_interval_point l p r hx hm
    all_goals have := i.isLt; dsimp only [r, cell, n] at *; omega
  · apply Finset.mem_union_left
    apply l.central_cut_mem_markers p (cell ⟨n + 1, by omega⟩) _ hx hm
    change q.2.val + (n + 1) = p.D
    dsimp only [n]
    omega

private theorem north_central_ray (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralAuxiliaryBoxes p) (hyD : p.D < q.2.val) :
    Freeze.Ray (l.centralAuxiliaryBoxes p) (l.geometricBlockers p) .north q := by
  obtain ⟨hx, hm, hy, hy', _⟩ := (mem_centralAuxiliaryBoxes l p q).mp hq
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  let n := q.2.val - p.D - 1
  let cell : Fin (n + 2) → Cell (p.W + 1) (p.H + 1) := fun i =>
    (q.1, ⟨q.2.val - i.val, by have := q.2.isLt; omega⟩)
  have hstart : cell 0 = q := by apply Prod.ext rfl; exact Fin.ext (by simp [cell])
  rw [← hstart]
  apply Freeze.Ray.of_path cell
  · intro i
    change _ = _ ∧ _
    exact ⟨rfl, by have := i.isLt; dsimp only [cell, n] at *; simp only [Fin.val_castSucc, Fin.val_succ]; omega⟩
  · intro i
    let r := cell ⟨i.val + 1, by omega⟩
    apply central_interval_point l p r hx hm
    all_goals have := i.isLt; dsimp only [r, cell, n] at *; omega
  · apply Finset.mem_union_left
    apply l.central_cut_mem_markers p (cell ⟨n + 1, by omega⟩) _ hx hm
    change q.2.val - (n + 1) = p.D
    dsimp only [n]
    omega

/-- Each full central auxiliary component is anchored to a computed geometric blocker. -/
theorem centralAuxiliaryBoxes_anchored (l : PortLayout) (p : Scales.Parameters) :
    Freeze.Anchored (l.centralAuxiliaryBoxes p) (l.geometricBlockers p) := by
  intro d q hq
  obtain ⟨hx, hm, _, _, hc⟩ := (mem_centralAuxiliaryBoxes l p q).mp hq
  have hneq : q.2.val ≠ p.D := fun he => hc (l.central_cut_mem_markers p q he hx hm)
  have hv : Freeze.Ray (l.centralAuxiliaryBoxes p) (l.geometricBlockers p) .north q ∨
      Freeze.Ray (l.centralAuxiliaryBoxes p) (l.geometricBlockers p) .south q := by
    by_cases h : q.2.val < p.D
    · exact Or.inr (south_central_ray l p hq h)
    · exact Or.inl (north_central_ray l p hq (by omega))
  obtain ⟨r, ha, hr⟩ := central_west_blocker l p hq
  have hw : Freeze.Ray (l.centralAuxiliaryBoxes p) (l.geometricBlockers p) .west q := .hit ha hr
  cases d with
  | north => exact hv
  | south => exact hv.symm
  | east => exact Or.inr hw
  | west => exact Or.inl hw

/-- The actual central auxiliary region is full in the constructed initial configuration. -/
theorem centralAuxiliaryBoxes_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    l.centralAuxiliaryBoxes p ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨_, hm, hy, hy', hc⟩ := (mem_centralAuxiliaryBoxes l p q).mp hq
  apply l.physicalInstance_central_strip_full p hl hM ha initial target _ hc hy hy'
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  have hx0 : q.1.val ≠ 0 := fun he => hm ((l.mainColumnSet_iff p q.1).mpr (Or.inl he))
  have hxW : q.1.val ≠ p.W := fun he => hm ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inl he)))
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega

/-- The first actual freezing closure adds all full central auxiliary components. -/
theorem centralAuxiliaryBoxes_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.geometricBlockers p)
      (l.geometricBlockers p ∪ l.centralAuxiliaryBoxes p) :=
  .add (.refl _) (l.centralAuxiliaryBoxes_initial_full p hl hM ha initial target)
    (l.centralAuxiliaryBoxes_anchored p)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

/-- All central auxiliary components remain full at every actual solution prefix. -/
theorem physicalInstance_central_auxiliary_full {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.centralAuxiliaryBoxes p ⊆ u.boxes :=
  (Freeze.anchored_closure (l.centralAuxiliaryBoxes_anchored p)
    (l.physicalInstance_avoiding_prefix p hl hM ha initial target hsu hut ht)
    (l.centralAuxiliaryBoxes_initial_full p hl hM ha initial target)).1

/-- The actual first freezing closure excludes every central auxiliary box from each push ray. -/
theorem physicalInstance_central_auxiliary_avoiding {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none
      (l.geometricBlockers p ∪ l.centralAuxiliaryBoxes p))
      (l.physicalInstance p hl hM ha initial target).initial u :=
  (l.centralAuxiliaryBoxes_closure p hl hM ha initial target).reachable
    (l.physicalInstance_avoiding_prefix p hl hM ha initial target hsu hut ht)

/-- A complete physical lifting fixes every actual central auxiliary box at its initial cell. -/
theorem physicalInstance_central_auxiliary_frozen {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (l.physicalInstance p hl hM ha initial target).initial)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ T : LabelledState ι (p.W + 1) (p.H + 1), T.state = t ∧
      Labels.GuardedReachable (l.physicalInstance p hl hM ha initial target).board none
        (l.geometricBlockers p ∪ l.centralAuxiliaryBoxes p) S T ∧
      ∀ i, S.position i ∈ l.centralAuxiliaryBoxes p → T.position i = S.position i := by
  have hguard := l.physicalInstance_central_auxiliary_avoiding p hl hM ha initial target hr .refl ht
  rw [← hS] at hguard
  obtain ⟨T, hT, hlabels⟩ := Labels.lift_guarded hguard
  exact ⟨T, hT, hlabels, fun i hi => hlabels.position i (Finset.mem_union_right _ hi)⟩

end Solution
end PushPuzzle.PushS.PortLayout
