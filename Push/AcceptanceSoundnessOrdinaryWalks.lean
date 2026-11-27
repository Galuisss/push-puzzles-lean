/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalksReaders
public import PushS.PortOrdinaryWalks
import all PushS.PortBackground
import all PushS.PortDeeperBudget

/-! Complete actual descending certification of every ordinary public walk and reader. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- The highest actual f/r corridors and long branches establish the descending induction base. -/
private theorem canonical_deeperWalk_last_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.deeperWalkHoles p (p.levels - 1) ⊆ PushS.holes u := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact (PushS.mem_holes _).mpr fun hb =>
      Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target hut ha) hb hf
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨he, hgt⟩ := List.mem_filter.mp he
  have hgt : p.levels - 1 < e.level := of_decide_eq_true hgt
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have heM : e.level = p.levels := by omega
  have hwalks := l.endpointBaseSegments_subset_walks p hl hM e he
    ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hcontains⟩)
  exact (Finset.mem_union.mp hwalks).elim
    (fun h => canonical_last_publicWalk_empty l p hl hM haxes initial target hgate e he heM hsu hut ha h)
    (fun h => canonical_last_reader_empty l p hl hM haxes initial target hgate e he heM hsu hut ha h)

/-- Descending through every actual level proves all ordinary corridors and long branches empty at every prefix. -/
theorem canonical_ordinaryWalks_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.deeperWalkHoles p 0 ⊆ PushS.holes u := by
  let D := fun j => DeeperWalkInvariant l p hl hM haxes initial target j t
  have hbase : D (p.levels - 1) := fun _ hs ht =>
    canonical_deeperWalk_last_empty l p hl hM haxes initial target hgate hs ht ha
  have hstep (j : ℕ) (hj : 1 ≤ j) (hjm : j < p.levels) (hD : D j) : D (j - 1) := by
    intro s hs hst
    apply l.deeperWalkHoles_subset_step p hl hM j hj (PushS.holes s) (hD s hs hst)
    intro e he hej
    have heM : e.level < p.levels := by omega
    have hD' : DeeperWalkInvariant l p hl hM haxes initial target e.level t := by simpa only [hej] using hD
    have hpub := canonical_level_publicWalk_empty_of_deeper l p hl hM haxes initial target hgate
      e he heM hs hst ha hD'
    have hreader := canonical_level_reader_empty_of_deeper l p hl hM haxes initial target hgate
      e he heM hs hst ha hD'
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

/-- The actual public-walk invariant now holds at every cutoff, with no induction contract remaining. -/
theorem canonical_deeperWalk_empty (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.deeperWalkHoles p j ⊆ PushS.holes u :=
  (l.deeperWalkHoles_antitone p (Nat.zero_le j)).trans
    (canonical_ordinaryWalks_empty l p hl hM haxes initial target hgate hsu hut ha)

/-- Every actual accepted prefix preserves the now-established deeper public-hole region. -/
theorem canonical_deeper_preserving (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Relation.ReflTransGen (Radius.PreservingStep
      (l.canonicalInstance p hl hM haxes initial target).board none (l.deeperWalkHoles p j))
      (l.canonicalInstance p hl hM haxes initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, canonical_deeperWalk_empty l p hl hM haxes initial target hgate j (hsa.tail hm) (hbu.trans hut) ha⟩

/-- Every actual ordinary reader corridor and all its short branches stay empty throughout accepted play. -/
theorem canonical_ordinaryReaders_empty (e : Endpoint) (he : e ∈ l.endpoints)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.endpointReaderWalk p e ⊆ PushS.holes u := by
  by_cases heM : e.level = p.levels
  · exact canonical_last_reader_empty l p hl hM haxes initial target hgate e he heM hsu hut ha
  · have heM : e.level < p.levels := by have := (l.endpoints_level_bounds p hl hM he).2; omega
    exact canonical_level_reader_empty_of_deeper l p hl hM haxes initial target hgate e he heM hsu hut ha
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level hs ht ha)

/-- Every computed ordinary reader-public region stays empty at every actual prefix and cutoff. -/
theorem canonical_allReaderWalks_empty (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.readerWalkHoles p j ⊆ PushS.holes u := by
  by_cases hj : j < p.levels
  · exact canonical_level_readerWalk_empty_of_deeper l p hl hM haxes initial target hgate j hj hsu hut ha
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate j hs ht ha)
  · exact (l.readerWalkHoles_antitone p (by omega)).trans
      (canonical_readerWalk_last_empty l p hl hM haxes initial target hgate hsu hut ha)

/-- Every ordinary reader-midpoint row is permanently empty and unvisited on the actual accepted trajectory. -/
theorem canonical_allMidpointRows_excluded (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Blocked.Excluded (l.readerMidpointRows p j) u :=
  canonical_reader_midpointRows_excluded_at_of_reader l p hl hM haxes initial target j hsu hut ha
    (fun _ hs ht => canonical_allReaderWalks_empty l p hl hM haxes initial target hgate j hs ht ha)

/-- Every ordinary interlevel marker is permanently empty and unvisited after completing the actual descent. -/
theorem canonical_allInterlevel_excluded (j : ℕ) (hj : 1 ≤ j) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Blocked.Excluded (l.interlevelMarkers p j) u :=
  canonical_interlevel_excluded_at_of_deeper l p hl hM haxes initial target j hj hsu hut ha
    (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate j hs ht ha)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
