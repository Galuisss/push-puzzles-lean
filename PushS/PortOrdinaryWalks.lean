/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointLevelPublic
public import PushS.PortEndpointLevelReader
import all PushS.PortDeeperBudget
import all PushS.PortBackground

/-! Descending certification of every actual ordinary endpoint public walk and reader. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- Lowering the cutoff only adds actual endpoint segments at the intervening level. -/
theorem deeperWalkHoles_subset_step (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (j : ℕ) (hj : 1 ≤ j)
    (R : Finset (Cell (p.W + 1) (p.H + 1))) (hD : l.deeperWalkHoles p j ⊆ R)
    (hC : ∀ e ∈ l.endpoints, e.level = j → endpointPublicWalk p e ∪ l.endpointReaderWalk p e ⊆ R) :
    l.deeperWalkHoles p (j - 1) ⊆ R := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact hD (Finset.mem_union_left _ hf)
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨he, hsel⟩ := List.mem_filter.mp he
  have hsel : j - 1 < e.level := of_decide_eq_true hsel
  by_cases hgt : j < e.level
  · apply hD
    apply Finset.mem_union_right
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_flatMap.mpr
      ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true hgt⟩, hs⟩, hcontains⟩
  · exact hC e he (by omega) (l.endpointBaseSegments_subset_walks p hl hM e he
      ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hcontains⟩))

/-- Increasing the cutoff removes public segments from the deeper-walk set. -/
theorem deeperWalkHoles_antitone (l : PortLayout) (p : Scales.Parameters) {i j : ℕ} (hij : i ≤ j) :
    l.deeperWalkHoles p j ⊆ l.deeperWalkHoles p i := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact Finset.mem_union_left _ hf
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨he, hgt⟩ := List.mem_filter.mp he
  have hgt : j < e.level := of_decide_eq_true hgt
  exact Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_flatMap.mpr
    ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true (by omega)⟩, hs⟩, hcontains⟩)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Descending through every actual level certifies all ordinary f/r walks and long branches. -/
theorem physicalInstance_ordinaryWalks_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : l.deeperWalkHoles p 0 ⊆ holes u := by
  let D : ℕ → Prop := fun j => ∀ s, Reachable (I).board none (I).initial s →
    Reachable (I).board none s t → l.deeperWalkHoles p j ⊆ holes s
  have hbase : D (p.levels - 1) := fun _ hs ht' =>
    l.physicalInstance_deeperWalk_last_empty p hl hM ha initial target hs ht' ht
  have hstep (j : ℕ) (hj : 1 ≤ j) (hjM : j < p.levels) (hD : D j) : D (j - 1) := by
    intro s hs hst
    apply l.deeperWalkHoles_subset_step p hl hM j hj (holes s) (hD s hs hst)
    intro e he hej
    have heM : e.level < p.levels := by omega
    have hD' : ∀ a, Reachable (I).board none (I).initial a → Reachable (I).board none a t →
        l.deeperWalkHoles p e.level ⊆ holes a := by simpa only [hej, D] using hD
    have hpub := l.physicalInstance_level_publicWalk_empty p hl hM ha initial target e he heM hs hst ht hD'
    have hreader := l.physicalInstance_level_reader_empty p hl hM ha initial target e he heM hs hst ht hD'
      (fun _ hIa hat => l.physicalInstance_level_readerWalk_empty p hl hM ha initial target e.level heM hIa hat ht hD')
    intro q hq
    exact (Finset.mem_union.mp hq).elim (fun h => hpub h) (fun h => hreader h)
  have hall : ∀ k : ℕ, k ≤ p.levels - 1 → D (p.levels - 1 - k) := by
    intro k
    induction k with
    | zero => exact fun _ => by simpa only [Nat.sub_zero] using hbase
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hcur := hstep (p.levels - 1 - k) (by omega) (by omega) hprev
      have heq : p.levels - 1 - k - 1 = p.levels - 1 - (k + 1) := by omega
      exact heq ▸ hcur
  have hzero : D 0 := by simpa only [Nat.sub_self] using hall (p.levels - 1) le_rfl
  exact hzero u hsu hut

/-- The computed public region at any cutoff is empty on every actual successful prefix. -/
theorem physicalInstance_deeperWalk_empty (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : l.deeperWalkHoles p j ⊆ holes u :=
  Finset.Subset.trans (l.deeperWalkHoles_antitone p (Nat.zero_le j))
    (l.physicalInstance_ordinaryWalks_empty p hl hM ha initial target hsu hut ht)

/-- Every actual successful prefix preserves the computed deeper public-hole region. -/
theorem physicalInstance_deeper_preserving (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Radius.PreservingStep (I).board none (l.deeperWalkHoles p j)) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, l.physicalInstance_deeperWalk_empty p hl hM ha initial target j (hsa.tail hm) (hbu.trans hut) ht⟩

/-- Every actual ordinary r corridor and selected short branch is permanently empty. -/
theorem physicalInstance_ordinaryReaders_empty (e : Endpoint) (he : e ∈ l.endpoints)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : l.endpointReaderWalk p e ⊆ holes u := by
  by_cases heM : e.level = p.levels
  · exact l.physicalInstance_endpoint_reader_empty p hl hM ha initial target e he heM hsu hut ht
  · have heM : e.level < p.levels := by have := (l.endpoints_level_bounds p hl hM he).2; omega
    have hD : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
        l.deeperWalkHoles p e.level ⊆ holes s :=
      fun _ hs ht' => l.physicalInstance_deeperWalk_empty p hl hM ha initial target e.level hs ht' ht
    exact l.physicalInstance_level_reader_empty p hl hM ha initial target e he heM hsu hut ht hD
      (fun _ hs ht' => l.physicalInstance_level_readerWalk_empty p hl hM ha initial target e.level heM hs ht' ht hD)

/-- Every actual reader public-walk region stays empty, at every cutoff. -/
theorem physicalInstance_allReaderWalks_empty (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : l.readerWalkHoles p j ⊆ holes u := by
  by_cases hj : j < p.levels
  · exact l.physicalInstance_level_readerWalk_empty p hl hM ha initial target j hj hsu hut ht
      (fun _ hs ht' => l.physicalInstance_deeperWalk_empty p hl hM ha initial target j hs ht' ht)
  · exact Finset.Subset.trans (l.readerWalkHoles_antitone p (by omega))
      (l.physicalInstance_readerWalk_last_empty p hl hM ha initial target hsu hut ht)

/-- All actual ordinary reader midpoint holes are empty and unvisited. -/
theorem physicalInstance_allMidpointRows_excluded (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : Blocked.Excluded (l.readerMidpointRows p j) u :=
  l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target j hsu hut ht
    (fun _ hs ht' => l.physicalInstance_allReaderWalks_empty p hl hM ha initial target j hs ht' ht)

/-- All actual ordinary interlevel holes are empty and unvisited. -/
theorem physicalInstance_allInterlevel_excluded (j : ℕ) (hj : 1 ≤ j)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : Blocked.Excluded (l.interlevelMarkers p j) u :=
  l.physicalInstance_interlevel_excluded_at p hl hM ha initial target j hj hsu hut ht
    (fun _ hs ht' => l.physicalInstance_deeperWalk_empty p hl hM ha initial target j hs ht' ht)

end Solution
end PushPuzzle.PushS.PortLayout
