/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesCuts
import all Push.PartnerUpperValidity
import all Push.PartnerInternalValidity

/-! Internal ears increase the global upper load by at most one, outside every gate. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS PageLevels

private def earGap (a gap : ℕ) : ℕ := if gap < a then gap else if gap < a + 3 then a else gap - 2

private theorem ear_upper_perm (l : PortLayout) (a cut : ℕ) (hc : cut = a ∨ cut = a + 2) :
    (ear l cut (a, a + 1)).upperPairs.Perm
      ((a + 1, a + 2) :: (a, a + 3) :: (l.upperPairs.erase (a, a + 1)).map (mapPair cut)) := by
  rcases hc with hc | hc
  · subst cut
    simp only [ear, shift, Nat.lt_irrefl, ite_false, show ¬a + 1 < a by omega,
      Nat.add_assoc, sortPair, min_eq_right (by omega : a + 1 ≤ a + 2),
      max_eq_left (by omega : a + 1 ≤ a + 2), min_eq_right (by omega : a ≤ a + 3),
      max_eq_left (by omega : a ≤ a + 3)]
    exact List.Perm.refl _
  · subst cut
    simp only [ear, shift, show a < a + 2 by omega, show a + 1 < a + 2 by omega,
      ite_true, Nat.add_assoc, sortPair, min_eq_left (by omega : a ≤ a + 3),
      max_eq_right (by omega : a ≤ a + 3), min_eq_left (by omega : a + 1 ≤ a + 2),
      max_eq_right (by omega : a + 1 ≤ a + 2)]
    exact List.Perm.swap ..

private theorem ear_rest_test {l : PortLayout} (hl : l.pages.Valid) {a cut : ℕ}
    (hp : (a, a + 1) ∈ l.upperPairs) (hc : cut = a ∨ cut = a + 2) (gap : ℕ)
    {ab : ℕ × ℕ} (hab : ab ∈ l.upperPairs.erase (a, a + 1)) :
    gapTest gap (mapPair cut ab) = gapTest (earGap a gap) ab := by
  have hpos := adjacent_pair_surroundings hl hp hab
  apply Bool.eq_iff_iff.mpr
  rcases hc with hc | hc <;> subst cut
  all_goals
    simp only [gapTest, mapPair, decide_eq_true_eq]
    unfold shift earGap
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega

private theorem ear_selected_test (a gap : ℕ) :
    gapTest (earGap a gap) (a, a + 1) = gapTest gap (a, a + 3) := by
  apply Bool.eq_iff_iff.mpr
  simp only [gapTest, decide_eq_true_eq]
  unfold earGap
  split_ifs <;> omega

private theorem ear_inner_test (a gap : ℕ) : gapTest gap (a + 1, a + 2) = decide (gap = a + 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [gapTest, decide_eq_true_eq]
  omega

/-- The exact upper count through either actual adjacent-pair ear. -/
private theorem ear_upperLoad {l : PortLayout} (hl : l.pages.Valid) {a cut : ℕ}
    (hp : (a, a + 1) ∈ l.upperPairs) (hc : cut = a ∨ cut = a + 2) (gap : ℕ) :
    upperLoad (ear l cut (a, a + 1)) gap = upperLoad l (earGap a gap) + if gap = a + 1 then 1 else 0 := by
  have hnew := List.Perm.countP_eq (gapTest gap) (ear_upper_perm l a cut hc)
  have hold := List.Perm.countP_eq (gapTest (earGap a gap)) (List.perm_cons_erase hp)
  have hr : ((l.upperPairs.erase (a, a + 1)).map (mapPair cut)).countP (gapTest gap) =
      (l.upperPairs.erase (a, a + 1)).countP (gapTest (earGap a gap)) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro ab hab
    rw [Function.comp_apply, ear_rest_test hl hp hc gap hab]
  simp only [List.countP_cons, ear_inner_test, decide_eq_true_eq] at hnew
  rw [hr] at hnew
  simp only [List.countP_cons, ear_selected_test] at hold
  unfold upperLoad
  omega

/-- The upper budget at a gate's two internal gaps. -/
def GateUpperBound (l : PortLayout) (bound : ℕ) : Prop :=
  ∀ kind first, LowerGroup.gate kind first ∈ l.lowerGroups →
    upperLoad l first ≤ bound ∧ upperLoad l (first + 1) ≤ bound

private theorem gate_positions {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) {other : Shuttle.Kind} {start : ℕ}
    (hk : LowerGroup.gate other start ∈ l.lowerGroups) :
    start + 2 < first ∨ start = first ∨ first + 3 ≤ start := by
  have h₁ := (gate_boundary_safe hl hg).1 other start hk
  have h₂ := (gate_boundary_safe hl hg).2 other start hk
  omega

private theorem leftEar_gateUpper {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hb : GateUpperBound l bound) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hp : (first, first + 1) ∈ l.upperPairs) :
    GateUpperBound (leftEar l first) bound := by
  intro other start hstart
  obtain ⟨old, hold, rfl⟩ := (ear_gate_mem l first _ other start).mp hstart
  have hpos := gate_positions hl hg hold
  have hv := hb other old hold
  have hgeom : earGap first (shift first old) = old ∧
      earGap first (shift first old + 1) = old + 1 ∧
      shift first old ≠ first + 1 ∧ shift first old + 1 ≠ first + 1 := by
    unfold shift earGap
    split_ifs <;> omega
  unfold leftEar
  constructor
  · rw [ear_upperLoad hl hp (Or.inl rfl), hgeom.1, ite_eq_right hgeom.2.2.1, Nat.add_zero]
    exact hv.1
  · rw [ear_upperLoad hl hp (Or.inl rfl), hgeom.2.1, ite_eq_right hgeom.2.2.2, Nat.add_zero]
    exact hv.2

private theorem rightEar_gateUpper {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hb : GateUpperBound l bound) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hp : (first + 1, first + 2) ∈ l.upperPairs) :
    GateUpperBound (rightEar l first) bound := by
  intro other start hstart
  obtain ⟨old, hold, rfl⟩ := (ear_gate_mem l (first + 3) _ other start).mp hstart
  have hpos := gate_positions hl hg hold
  have hv := hb other old hold
  have hgeom : earGap (first + 1) (shift (first + 3) old) = old ∧
      earGap (first + 1) (shift (first + 3) old + 1) = old + 1 ∧
      shift (first + 3) old ≠ (first + 1) + 1 ∧ shift (first + 3) old + 1 ≠ (first + 1) + 1 := by
    unfold shift earGap
    split_ifs <;> omega
  have hpair : (first + 1, (first + 1) + 1) ∈ l.upperPairs := by simpa only [Nat.add_assoc] using hp
  have hc : first + 3 = (first + 1) + 2 := by omega
  unfold rightEar
  constructor
  · rw [show (first + 1, first + 2) = (first + 1, (first + 1) + 1) by congr 1,
      ear_upperLoad hl hpair (Or.inr hc), hgeom.1, ite_eq_right hgeom.2.2.1, Nat.add_zero]
    exact hv.1
  · rw [show (first + 1, first + 2) = (first + 1, (first + 1) + 1) by congr 1,
      ear_upperLoad hl hpair (Or.inr hc), hgeom.2.1, ite_eq_right hgeom.2.2.2, Nat.add_zero]
    exact hv.2

private theorem leftEar_upperLoad_le {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hu : ∀ gap, upperLoad l gap ≤ bound + 1) (hb : GateUpperBound l bound)
    {kind : Shuttle.Kind} {first : ℕ} (hg : LowerGroup.gate kind first ∈ l.lowerGroups)
    (hp : (first, first + 1) ∈ l.upperPairs) (gap : ℕ) : upperLoad (leftEar l first) gap ≤ bound + 1 := by
  unfold leftEar
  rw [ear_upperLoad hl hp (Or.inl rfl)]
  by_cases he : gap = first + 1
  · subst gap
    have h := (hb kind first hg).1
    simp only [earGap, show ¬first + 1 < first by omega, ite_false,
      show first + 1 < first + 3 by omega, ite_true]
    omega
  · rw [ite_eq_right he, Nat.add_zero]
    exact hu _

private theorem rightEar_upperLoad_le {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hu : ∀ gap, upperLoad l gap ≤ bound + 1) (hb : GateUpperBound l bound)
    {kind : Shuttle.Kind} {first : ℕ} (hg : LowerGroup.gate kind first ∈ l.lowerGroups)
    (hp : (first + 1, first + 2) ∈ l.upperPairs) (gap : ℕ) : upperLoad (rightEar l first) gap ≤ bound + 1 := by
  have hpair : (first + 1, (first + 1) + 1) ∈ l.upperPairs := by simpa only [Nat.add_assoc] using hp
  unfold rightEar
  rw [show (first + 1, first + 2) = (first + 1, (first + 1) + 1) by congr 1,
    ear_upperLoad hl hpair (Or.inr (show first + 3 = (first + 1) + 2 by omega))]
  by_cases he : gap = (first + 1) + 1
  · subst gap
    have h := (hb kind first hg).2
    simp only [earGap, show ¬first + 1 + 1 < first + 1 by omega, ite_false,
      show first + 1 + 1 < first + 1 + 3 by omega, ite_true]
    omega
  · rw [ite_eq_right he, Nat.add_zero]
    exact hu _

private theorem bufferAt_upper (s : BufferState) (first : ℕ) (hs : s.layout.pages.Valid) {bound : ℕ}
    (hu : ∀ gap, upperLoad s.layout gap ≤ bound + 1) (hb : GateUpperBound s.layout bound) :
    (∀ gap, upperLoad (s.bufferAt first).layout gap ≤ bound + 1) ∧
      GateUpperBound (s.bufferAt first).layout bound := by
  unfold BufferState.bufferAt
  split_ifs with hg hp hq
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    exact ⟨leftEar_upperLoad_le hs hu hb hgate hp, leftEar_gateUpper hs hb hgate hp⟩
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    exact ⟨rightEar_upperLoad_le hs hu hb hgate hq, rightEar_gateUpper hs hb hgate hq⟩
  all_goals exact ⟨hu, hb⟩

private theorem internal_scan_upperLoad (s : BufferState) (positions : List ℕ)
    (hs : s.layout.pages.Valid) {bound : ℕ}
    (hu : ∀ gap, upperLoad s.layout gap ≤ bound + 1) (hb : GateUpperBound s.layout bound) :
    (∀ gap, upperLoad (s.scan positions).layout gap ≤ bound + 1) ∧ GateUpperBound (s.scan positions).layout bound := by
  induction positions generalizing s with
  | nil => exact ⟨hu, hb⟩
  | cons first rest ih =>
    have h := bufferAt_upper s first hs hu hb
    exact ih (s.bufferAt first) (s.bufferAt_valid first hs) h.1 h.2

/-- All internal ears together spend one additional upper nesting level. -/
theorem internal_upperLoad_le {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hu : l.pages.upperPage.maxActive ≤ bound) (gap : ℕ) :
    upperLoad (bufferInternal l).layout gap ≤ bound + 1 := by
  have hload (i : ℕ) : upperLoad l i ≤ bound := (upperLoad_le_maxActive hl i).trans hu
  exact (internal_scan_upperLoad (BufferState.start l) _ hl
    (fun i => (hload i).trans (by omega)) (fun _ _ _ => ⟨hload _, hload _⟩)).1 gap

private theorem cut_scan_upperLoad (s : BufferState) (positions : List ℕ) {bound : ℕ}
    (hu : ∀ gap, upperLoad s.layout gap ≤ bound) (gap : ℕ) : upperLoad (Cuts.scan s positions).layout gap ≤ bound := by
  induction positions generalizing s with
  | nil => exact hu gap
  | cons cut rest ih =>
    apply ih (Cuts.cutAt s cut)
    intro i
    unfold Cuts.cutAt
    split_ifs
    · exact cut_upperLoad_le hu cut i
    · exact hu i

/-- The full actual repair uses at most one more upper active arc than its valid source. -/
theorem repair_upper_maxActive {l : PortLayout} (hl : l.pages.Valid) {bound : ℕ}
    (hu : l.pages.upperPage.maxActive ≤ bound) :
    (Cuts.repair l).layout.pages.upperPage.maxActive ≤ bound + 1 := by
  apply upper_maxActive_le
  exact cut_scan_upperLoad (bufferInternal l) _ (internal_upperLoad_le hl hu)

end PushPuzzle.Push.Partner.Resources
