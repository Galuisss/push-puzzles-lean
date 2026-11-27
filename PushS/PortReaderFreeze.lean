/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortReaderMidpoints
public import PushS.PortInstance
import all PushS.PortReaderExits
import all PushS.PortStreetSeparation
import all PushS.PortWideGeometry
import all PushS.PortStreetSupport
import all PushS.PortEndpointLocality
import all PushS.PortLayoutCoordinates
import all PushS.PortSegments

/-! Actual reader midpoint holes are excluded once their public walks remain empty. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- The actual ordinary f-axis midpoint markers on their own working row at level `j`. -/
@[expose] noncomputable def readerMidpointHoles (l : PortLayout) (p : Scales.Parameters) (j : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => ∃ e ∈ l.endpoints, e.level = j ∧
    q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2 ∧
    q.2.val = if e.side = .upper then readDepth p j else p.H - readDepth p j

/-- Actual level-`j` f-axis midpoint markers on every selected row through the endpoint depth. -/
@[expose] noncomputable def readerMidpointRows (l : PortLayout) (p : Scales.Parameters) (j : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => ∃ e ∈ l.endpoints, e.level = j ∧
    q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2 ∧
    ∃ v ∈ l.workingDepthCoordinates p, v ≤ readDepth p e.level ∧
      q.2.val = if e.side = .upper then v else p.H - v

private theorem own_midpoint_data (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.readerMidpointHoles p j) :
    ∃ e ∈ l.endpoints, e.level = j ∧
      q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2 ∧
      q.2.val = if e.side = .upper then readDepth p j else p.H - readDepth p j := by
  classical
  simpa only [readerMidpointHoles, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem midpoint_data (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.readerMidpointRows p j) :
    ∃ e ∈ l.endpoints, e.level = j ∧
      q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2 ∧
      ∃ v ∈ l.workingDepthCoordinates p, v ≤ readDepth p e.level ∧
        q.2.val = if e.side = .upper then v else p.H - v := by
  classical
  simpa only [readerMidpointRows, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem own_midpoints_subset (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (j : ℕ) :
    l.readerMidpointHoles p j ⊆ l.readerMidpointRows p j := by
  classical
  intro q hq
  obtain ⟨e, he, hj, hx, hy⟩ := own_midpoint_data l p hq
  obtain ⟨hlo, hhi⟩ := l.endpoints_level_bounds p hl hM he
  have hwork := (workingRows_level l p hlo hhi).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, e, he, hj, hx, readDepth p e.level, hwork, le_rfl, ?_⟩
  simpa only [hj] using hy

private theorem midpoint_far (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.readerMidpointRows p j) :
    ∀ a ∈ l.readerExitSet p, p.K j < distance a q := by
  obtain ⟨e, he, hj, hx, _⟩ := midpoint_data l p hq
  simpa only [hj] using l.endpoint_midpoint_readerExit_far p hl hM ha he hx

private theorem midpoint_not_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.readerMidpointRows p j) : q ∉ Boundary.frame := by
  obtain ⟨e, _, _, _, v, hv, _, hy⟩ := midpoint_data l p hq
  have hbounds := workingDepth_positive l p hv
  have hnotcol : q.1 ∉ l.streetColumnSet p := by
    intro hcol
    have := midpoint_far l p hl hM ha hq q (Or.inl hcol)
    simp only [distance_self, Nat.not_lt_zero] at this
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  cases d with
  | west => exact hnotcol (frame_column l p q (Or.inl (by simpa [Boundary.edge] using hd)))
  | east =>
    apply hnotcol
    apply frame_column l p q
    right
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    omega
  | north =>
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  | south =>
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy <;> omega

private theorem midpoint_not_walk (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.readerMidpointRows p j) : q ∉ l.readerWalkHoles p j := by
  obtain ⟨e, he, hj, _, v, _, hve, hy⟩ := midpoint_data l p hq
  obtain ⟨hjlo, hjhi⟩ := l.endpoints_level_bounds p hl hM he
  rw [hj] at hjlo hjhi hve
  have hnotcol : q.1 ∉ l.streetColumnSet p := by
    intro hcol
    have := midpoint_far l p hl hM ha hq q (Or.inl hcol)
    simp only [distance_self, Nat.not_lt_zero] at this
  intro hw
  rcases Finset.mem_union.mp hw with hf | hw
  · exact midpoint_not_frame l p hl hM ha hq hf
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  obtain ⟨f, hf, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨⟨seg, k⟩, hzip, hselected⟩ := List.mem_filterMap.mp hs
  dsimp only at hselected
  have heq : seg = s := by split_ifs at hselected <;> exact Option.some.inj hselected
  subst s
  have hlev : j ≤ f.level := by split_ifs at hselected <;> omega
  dsimp only [endpointFixedSegments] at hzip
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil, or_false] at hzip
  rcases hzip with hzip | hzip | hzip
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzip
    exact hnotcol (column_of_coordinate l p q (auxiliary_columns l p hf).1
      (vertical_contains _ _ _ _ |>.mp hcontains).1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzip
    exact hnotcol (column_of_coordinate l p q (auxiliary_columns l p hf).2
      (vertical_contains _ _ _ _ |>.mp hcontains).1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzip
    have hrow := (horizontal_contains _ _ _ _).mp hcontains |>.1
    obtain ⟨hflo, hfhi⟩ := l.endpoints_level_bounds p hl hM hf
    have hdepth : readDepth p j ≤ readDepth p f.level := by
      rw [readDepth_eq p hjlo hjhi, readDepth_eq p hflo hfhi]
      exact Y_le p hlev
    have hJ := readDepth_add_lt_D p j
    have hF := readDepth_add_lt_D p f.level
    have hH : p.H = 2 * p.D := rfl
    change q.2.val = (if f.side = .upper then readDepth p f.level + 2
      else p.H - (readDepth p f.level + 2)) at hrow
    cases hes : e.side <;> cases hfs : f.side <;>
      simp only [hes, hfs, reduceCtorEq, ite_true, ite_false] at hy hrow <;> omega

private theorem midpoint_encoded (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.readerMidpointRows p j) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  obtain ⟨e, he, _, hx, v, hv, hve, hy⟩ := midpoint_data l p hq
  let c := coordinates p
  let s := point (((auxiliary c e).1 + c.x e.port) / 2) (onSide c e.side v)
  have hs : s ∈ endpointFixedSegments l c e := by
    have hmid : s ∈ (workingRows l c).flatMap (fun v =>
        (if v ≤ c.depth e.level then [point (((auxiliary c e).1 + c.x e.port) / 2) (onSide c e.side v)] else []) ++
        (if v < c.depth e.level then [point (inward (c.x e.port) e.inward 1) (onSide c e.side v)] else [])) := by
      apply List.mem_flatMap.mpr
      refine ⟨v, hv, ?_⟩
      apply List.mem_append_left
      simp only [show v ≤ c.depth e.level from hve, ite_true, List.mem_singleton]
      rfl
    simp only [endpointFixedSegments, List.mem_append]
    exact Or.inl (Or.inr hmid)
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨s, List.mem_append_left _ (l.endpointFixedSegments_mem_fixed p hl hM e he hs), ?_⟩
  change q.1.val = ((auxiliary c e).1 + c.x e.port) / 2 at hx
  have hy' : q.2.val = onSide c e.side v := hy
  simp only [s, point, segment, Segment.Contains, Nat.min_self, Nat.max_self]
  simp only [hx, hy', le_refl, and_self, true_or]

private def ReaderStep (l : PortLayout) (p : Scales.Parameters) (j : ℕ)
    (B : Board (p.W + 1) (p.H + 1)) (s t : State (p.W + 1) (p.H + 1)) : Prop :=
  Radius.PreservingStep B none (l.readerWalkHoles p j) s t ∧
    s.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p) ∧
    t.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p)

private theorem reader_step_exit (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {j : ℕ} {B : Board (p.W + 1) (p.H + 1)}
    {s t : State (p.W + 1) (p.H + 1)} (hm : ReaderStep l p j B s t)
    (hin : s.player ∈ l.readerWalkHoles p j) (hout : t.player ∉ l.readerWalkHoles p j) :
    s.player ∈ l.readerExitSet p :=
  l.step_readerWalk_exit p hl hM hm.1.1 hm.2.1 hm.2.2 hin hout

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

private theorem reader_between {u v t : State (p.W + 1) (p.H + 1)} (j : ℕ)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (huv : Reachable (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.readerWalkHoles p j ⊆ holes s) :
    Relation.ReflTransGen (ReaderStep l p j (l.physicalInstance p hl hM ha initial target).board) u v := by
  revert hvt
  induction huv with
  | refl => exact fun _ => .refl
  | @tail v w huv hm ih =>
    intro hwt
    have hIv := hsu.trans huv
    have hIw := hIv.tail hm
    exact (ih ((Relation.ReflTransGen.single hm).trans hwt)).tail
      ⟨⟨hm, hP w hIw hwt⟩,
        l.physicalInstance_player_on_streets p hl hM ha initial target hIv
          ((Relation.ReflTransGen.single hm).trans hwt) ht,
        l.physicalInstance_player_on_streets p hl hM ha initial target hIw hwt ht⟩

private theorem midpoint_actual_far {j : ℕ} {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ l.readerMidpointRows p j) :
    ∀ a ∈ l.readerExitSet p,
      (holes (l.physicalInstance p hl hM ha initial target).initial \ l.readerWalkHoles p j).card <
        distance a q := by
  obtain ⟨e, he, hj, _, _⟩ := midpoint_data l p hq
  have hjlo := (l.endpoints_level_bounds p hl hM he).1
  rw [hj] at hjlo
  have hbudget : (holes (l.physicalInstance p hl hM ha initial target).initial \ l.readerWalkHoles p j).card ≤ p.K j := by
    rw [l.physicalInstance_initial_holes p hl hM ha initial target]
    exact l.encodedSegments_outside_readerWalk_card_le p hl hM ha initial hjlo
  exact fun a hae => hbudget.trans_lt (midpoint_far l p hl hM ha hq a hae)

/-- All actual selected-row reader midpoint holes stay empty and unvisited on a solution whose reader walks stay empty. -/
theorem physicalInstance_reader_midpointRows_excluded_at {u t : State (p.W + 1) (p.H + 1)}
    (j : ℕ)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.readerWalkHoles p j ⊆ holes s) :
    Blocked.Excluded (l.readerMidpointRows p j) u := by
  have hsu' := reader_between l p hl hM ha initial target j .refl hsu hut ht hP
  have hut' := reader_between l p hl hM ha initial target j hsu hut .refl ht hP
  have hPi : l.readerWalkHoles p j ⊆ holes (l.physicalInstance p hl hM ha initial target).initial := by
    change l.readerWalkHoles p j ⊆ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ
    rw [compl_compl]
    exact l.readerWalkHoles_subset_encoded p hl hM j initial
  have hp : (l.physicalInstance p hl hM ha initial target).initial.player ∈ l.readerWalkHoles p j :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target)
  constructor
  · intro q hq
    have hfinal : q ∈ holes t := by
      change q ∈ t.boxesᶜ
      rw [ht]
      change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ
      rw [compl_compl]
      exact midpoint_encoded l p hl hM target hq
    exact Radius.distant_hole_at_from_exits
      (R := ReaderStep l p j (l.physicalInstance p hl hM ha initial target).board)
      (fun {_ _} h => h.1) (fun {_ _} h hin hout => reader_step_exit l p hl hM h hin hout) hsu' hut' hPi hp
      (midpoint_not_walk l p hl hM ha hq) (midpoint_actual_far l p hl hM ha initial target hq) hfinal
  · intro hq
    exact Radius.player_ne_distant_from_exits
      (R := ReaderStep l p j (l.physicalInstance p hl hM ha initial target).board)
      (fun {_ _} h => h.1) (fun {_ _} h hin hout => reader_step_exit l p hl hM h hin hout) hsu' hPi hp
      (midpoint_not_walk l p hl hM ha hq) (midpoint_actual_far l p hl hM ha initial target hq) rfl

/-- The actual reader midpoint holes stay empty and unvisited on a solution whose reader walks stay empty. -/
theorem physicalInstance_reader_midpoints_excluded_at {u t : State (p.W + 1) (p.H + 1)}
    (j : ℕ)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.readerWalkHoles p j ⊆ holes s) :
    Blocked.Excluded (l.readerMidpointHoles p j) u := by
  have hrows := l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target j hsu hut ht hP
  have hsub := own_midpoints_subset l p hl hM j
  exact ⟨fun _ hq => hrows.empty (hsub hq), fun hq => hrows.player (hsub hq)⟩

/-- Filling all actual level-`j` reader midpoints preserves the complete successful trajectory. -/
theorem physicalInstance_reader_midpoints_fill {t : State (p.W + 1) (p.H + 1)} (j : ℕ)
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.readerWalkHoles p j ⊆ holes s) :
    Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill (l.physicalInstance p hl hM ha initial target).initial (l.readerMidpointHoles p j))
      (Blocked.fill t (l.readerMidpointHoles p j)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) hr
    (fun _ hsu hut => l.physicalInstance_reader_midpoints_excluded_at p hl hM ha initial target j hsu hut ht hP)
  rw [(l.physicalInstance p hl hM ha initial target).walls_empty]
  exact Finset.disjoint_empty_right _

/-- Filling every selected-row midpoint of each actual level-`j` endpoint preserves the complete successful trajectory. -/
theorem physicalInstance_reader_midpointRows_fill {t : State (p.W + 1) (p.H + 1)} (j : ℕ)
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.readerWalkHoles p j ⊆ holes s) :
    Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill (l.physicalInstance p hl hM ha initial target).initial (l.readerMidpointRows p j))
      (Blocked.fill t (l.readerMidpointRows p j)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) hr
    (fun _ hsu hut => l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target j hsu hut ht hP)
  rw [(l.physicalInstance p hl hM ha initial target).walls_empty]
  exact Finset.disjoint_empty_right _

end Solution

end PushPuzzle.PushS.PortLayout
