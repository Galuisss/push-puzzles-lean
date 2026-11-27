/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateHalfMarkers
import all PushS.PortGateHalfMarkers
import all PushS.PortGatePageWindow
import all PushS.PortGateTails
import all PushS.PortGatePublicWalk
import all PushS.PortStreetSeparation
import all PushS.PortBackground
import all PushS.PortSegments

/-! The actual full axis and private-column segments behind the gate half-depth holes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- Every gate's middle-axis and private-column open segment from half depth to its work row. -/
noncomputable def gateHalfRods (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => ∃ middle ∈ l.gateCenterCoordinates,
    (q.1.val = p.x middle ∨ q.1.val = p.x middle + 4) ∧
      ∃ v, readDepth p 1 / 2 < v ∧ v < readDepth p 1 ∧ q.2.val = p.H - v

private theorem half_rod_data (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateHalfRods p) :
    ∃ middle ∈ l.gateCenterCoordinates,
      (q.1.val = p.x middle ∨ q.1.val = p.x middle + 4) ∧
        ∃ v, readDepth p 1 / 2 < v ∧ v < readDepth p 1 ∧ q.2.val = p.H - v := by
  classical
  simpa only [gateHalfRods, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem rod_source_clear (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {middle v : ℕ} {q : ℕ × ℕ} (hx : q.1 = p.x middle ∨ q.1 = p.x middle + 4)
    (hv : readDepth p 1 / 2 < v) (hvy : v < readDepth p 1) (hy : q.2 = p.H - v)
    (hsource : GateHoleSource l p state middle q) : False := by
  have hx0 := readLength_add_lt_x p middle 0
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  cases hsource with
  | fixed hs =>
    cases gateFixedSegments_location p middle hs with
    | publicStreet hc _ =>
      simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    | privateCap _ hr => omega
    | privateBranch hr _ => omega
    | halfDepth hr => omega
    | marker hlevels _ hr =>
      have hg := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
      have hnext := readDepth_add_lt_H p 2
      simp only [Nat.reduceAdd] at hg
      omega
  | @signal kind first internal _ _ hs =>
    cases gateSegments_location p state kind first internal hs with
    | horizontal hr => omega
    | axis _ hr => omega

/-- Every cell of the two actual gate half rods is occupied in every initial physical encoding. -/
theorem gateHalfRods_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    l.gateHalfRods p ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨middle, hi, hx, v, hv, hvy, hy⟩ := half_rod_data l p hq
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hw : q ∈ gatePageWindow p middle := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [Nat.dist]
    omega
  by_contra hbox
  have hh := (mem_holes _).mpr hbox
  rw [l.physicalInstance_initial_holes p hl hM ha initial target] at hh
  exact rod_source_clear l p initial hx hv hvy hy
    (l.encodedSegments_gatePageWindow p hl hM ha initial hi hw hh)

private theorem rod_south_ray (l : PortLayout) (p : Scales.Parameters)
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hhalf : l.gateHalfMarkers p ⊆ G)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateHalfRods p) :
    Freeze.Ray (l.gateHalfRods p) G .south q := by
  obtain ⟨middle, hi, hx, v, hv, hvy, hy⟩ := half_rod_data l p hq
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  let n := v - readDepth p 1 / 2 - 1
  let path : Fin (n + 2) → Cell (p.W + 1) (p.H + 1) := fun i =>
    (q.1, ⟨q.2.val + i.val, by have := i.isLt; dsimp only [n] at *; omega⟩)
  have hstart : path 0 = q := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change q.2.val + 0 = q.2.val
      omega
  rw [← hstart]
  apply Freeze.Ray.of_path path
  · intro i
    exact ⟨rfl, by simp only [path, Fin.val_castSucc, Fin.val_succ]; omega⟩
  · intro i
    left
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, middle, hi, hx, v - (i.val + 1), ?_, by omega, ?_⟩
    · have := i.isLt
      dsimp only [n] at *
      omega
    · change q.2.val + (i.val + 1) = p.H - (v - (i.val + 1))
      have := i.isLt
      dsimp only [n] at *
      omega
  · apply hhalf
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, middle, hi, hx, ?_⟩
    change q.2.val + (n + 1) = p.H - readDepth p 1 / 2
    dsimp only [n]
    omega

/-- The actual protected half-depth holes and page background anchor both full gate half rods. -/
theorem gateHalfRods_anchored (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hhalf : l.gateHalfMarkers p ⊆ G) : Freeze.Anchored (l.gateHalfRods p) G := by
  intro d q hq
  have hv := rod_south_ray l p hhalf hq
  obtain ⟨middle, hi, hx, v, hvhalf, hvy, hy⟩ := half_rod_data l p hq
  have hx0 := readLength_add_lt_x p middle 0
  have heven : q.1.val % 2 = 0 := by have hc := x_even p middle; omega
  have hpos : 0 < q.1.val := by omega
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  have hrow := gate_walk_not_row l p hi (q := q) (by omega) (by omega)
  obtain ⟨r, ha, hr⟩ := gate_west_background l p hl hpos heven hrow
  have hh : Freeze.Ray (l.gateHalfRods p) G .west q := .hit ha (hpage hr)
  cases d with
  | north => exact Or.inr hv
  | south => exact Or.inl hv
  | east => exact Or.inr hh
  | west => exact Or.inl hh

/-- Both work-row back neighbours lie in the actual axis/private half rods. -/
theorem gateHalfRods_back_mem (l : PortLayout) (p : Scales.Parameters) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle ∨ q.1.val = p.x middle + 4)
    (hy : q.2.val = p.H - (readDepth p 1 - 1)) : q ∈ l.gateHalfRods p := by
  classical
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, middle, hi, hx, readDepth p 1 - 1, by omega, by omega, hy⟩

/-- The computed public blockers, half-depth holes and two full rods protecting a gate's private walk. -/
noncomputable def gatePrivateBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (l.gatePublicBlockers p hl hM ha hi ∪ l.gateHalfMarkers p) ∪ l.gateHalfRods p

/-- The two actual work-row back cells are among the computed private-walk blockers. -/
theorem gatePrivateBlockers_back_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle ∨ q.1.val = p.x middle + 4)
    (hy : q.2.val = p.H - (readDepth p 1 - 1)) :
    q ∈ l.gatePrivateBlockers p hl hM ha hi :=
  Finset.mem_union_right _ (l.gateHalfRods_back_mem p hi hx hy)

/-- Protected half-depth holes extend the actual public-wall closure to the private back rods. -/
theorem gatePrivateBlockers_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      ((l.pageBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateHalfMarkers p)
      (l.gatePrivateBlockers p hl hM ha hi) :=
  .add ((l.gatePublicBlockers_closure p hl hM ha initial target hi).adjoin_blockers (l.gateHalfMarkers p))
    (l.gateHalfRods_initial_full p hl hM ha initial target)
    (l.gateHalfRods_anchored p hl _
      (fun _ h => Finset.mem_union_left _ (gate_public_page l p hl hM ha hi h)) Finset.subset_union_right)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every actual successful prefix avoids the complete computed private-walk blockers. -/
theorem physicalInstance_gate_private_avoiding_prefix {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none (l.gatePrivateBlockers p hl hM ha hi))
      (I).initial u := by
  apply (l.gatePrivateBlockers_closure p hl hM ha initial target hi).reachable
  have hr := l.physicalInstance_gate_marker_avoiding_prefix p hl hM ha initial target hsu hut ht
  apply enrich_path hr
  intro a b hIa hm hbu
  have hIa' : Reachable (I).board none (I).initial a := Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hIa
  have hbt : Reachable (I).board none b t := (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbu).trans hut
  exact hm.union_excluded
    (l.physicalInstance_gate_halfMarkers_excluded p hl hM ha initial target hIa'
      ((Relation.ReflTransGen.single hm.1).trans hbt) ht)
    (l.physicalInstance_gate_halfMarkers_excluded p hl hM ha initial target (hIa'.tail hm.1) hbt ht)

end Solution
end PushPuzzle.PushS.PortLayout
