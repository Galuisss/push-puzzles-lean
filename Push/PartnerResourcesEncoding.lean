/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesLabels
public import Push.PartnerPolyTime

/-! Polynomial bounds on every complete unary accumulator of the actual repair folds. -/

public section
namespace PushPuzzle.Push.Partner.Resources

open PushS Turing.MultiTapeTM

private theorem kind_length (kind : Shuttle.Kind) : (Shuttle.encKind kind).length ≤ 1 := by
  cases kind <;> decide

private theorem lower_length (g : LowerGroup) : (encLowerGroup g).length = match g with
    | .wire a b => 2 * a + b + 2
    | .gate kind first => 2 * (Shuttle.encKind kind).length + first + 2 := by
  cases g <;> simp [encLowerGroup_apply, encLowerGroupPayload, encLowerGroup_toSum,
    encUnary_apply] <;> omega

theorem labels_of_code (l : PortLayout) : LabelsBounded l ((encPortLayout l).length + 2) := by
  have he : (encPortLayout l).length = 2 * l.portCount + 1 +
      (2 * (encList encPortPair l.upperPairs).length + 1 + (encList encLowerGroup l.lowerGroups).length) := by
    simp [encPortLayout_apply, encPortLayoutFields, encUnary_apply]
  simp only [encPortPair] at he
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro a b hm
    have h := length_le_encList_of_mem encPortPair hm
    simp only [encPortPair, length_encPair, encUnary_apply, List.length_replicate] at h
    omega
  · intro a b hm
    have h := length_le_encList_of_mem encLowerGroup hm
    simp only [lower_length] at h
    omega
  · intro kind first hm
    have h := length_le_encList_of_mem encLowerGroup hm
    simp only [lower_length] at h
    omega

private theorem layout_counts_of_code (l : PortLayout) :
    l.upperPairs.length ≤ (encPortLayout l).length ∧ l.lowerGroups.length ≤ (encPortLayout l).length := by
  have hu := length_le_length_encList encPortPair l.upperPairs
  have hl := length_le_length_encList encLowerGroup l.lowerGroups
  have he : (encPortLayout l).length = 2 * l.portCount + 1 +
      (2 * (encList encPortPair l.upperPairs).length + 1 + (encList encLowerGroup l.lowerGroups).length) := by
    simp [encPortLayout_apply, encPortLayoutFields, encUnary_apply]
  omega

theorem state_code_fields (s : BufferState) :
    (encPortLayout s.layout).length ≤ (encBufferState s).length ∧
      s.ports.length ≤ (encBufferState s).length ∧
        (∀ i ∈ s.ports, i ≤ (encBufferState s).length) := by
  have he : (encBufferState s).length = 2 * (encPortLayout s.layout).length + 1 +
      (encList encUnary s.ports).length := by
    simp only [encBufferState_apply, encBufferStateFields, length_encPair]
  have hp := length_le_length_encList encUnary s.ports
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  have h := length_le_encList_of_mem encUnary hi
  simp only [encUnary_apply, List.length_replicate] at h
  omega

/-- A common budget on all raw fields gives a quadratic bound on the standard complete state code. -/
private theorem state_code_le (s : BufferState) {bound : ℕ} (hl : LabelsBounded s.layout bound)
    (hu : s.layout.upperPairs.length ≤ bound) (hg : s.layout.lowerGroups.length ≤ bound)
    (hp : s.ports.length ≤ bound) (hv : ∀ i ∈ s.ports, i ≤ bound) :
    (encBufferState s).length ≤ 100 * (bound + 1) ^ 2 := by
  have hU := length_encList_le encPortPair s.layout.upperPairs (b := 3 * bound + 1) (by
    intro ab hab
    have h := hl.upper ab.1 ab.2 hab
    simp only [encPortPair, length_encPair, encUnary_apply, List.length_replicate]
    omega)
  have hG := length_encList_le encLowerGroup s.layout.lowerGroups (b := 3 * bound + 4) (by
    intro g hmem
    cases g with
    | wire a b => simp only [lower_length]; have h := hl.lower_wire a b hmem; omega
    | gate kind first => simp only [lower_length]; have h := hl.lower_gate kind first hmem; have := kind_length kind; omega)
  have hP := length_encList_le encUnary s.ports (b := bound) (by
    intro i hi
    simpa only [encUnary_apply, List.length_replicate] using hv i hi)
  have hn := hl.portCount
  have hUm := Nat.mul_le_mul_right (2 * (3 * bound + 1) + 1) hu
  have hGm := Nat.mul_le_mul_right (2 * (3 * bound + 4) + 1) hg
  have hPm := Nat.mul_le_mul_right (2 * bound + 1) hp
  simp only [encBufferState_apply, encBufferStateFields, encPortLayout_apply, encPortLayoutFields,
    length_encPair, encUnary_apply, List.length_replicate]
  change 2 * (2 * s.layout.portCount + 1 + (2 * (encList encPortPair s.layout.upperPairs).length +
    1 + (encList encLowerGroup s.layout.lowerGroups).length)) + 1 + (encList encUnary s.ports).length ≤ _
  nlinarith

/-- Every raw internal-buffer fold accumulator has a fixed polynomial unary size bound. -/
private theorem internal_scan_code (s : BufferState) (positions : List ℕ) :
    (encBufferState (s.scan positions)).length ≤
      100 * ((encBufferState s).length + 2 * positions.length + 3) ^ 2 := by
  let size := (encBufferState s).length
  have hs := state_code_fields s
  have hlabel : LabelsBounded s.layout (size + 2) :=
    (labels_of_code s.layout).mono (Nat.add_le_add_right hs.1 2)
  have hcount := layout_counts_of_code s.layout
  have hi := internal_scan_labels s positions hlabel
  have hv := internal_scan_positions s positions hs.2.2
  have hc := internal_scan_counts s positions
  have hp := s.scan_length positions
  have h := state_code_le (s.scan positions) hi
    (by dsimp [size] at *; omega) (by dsimp [size] at *; omega)
    (by dsimp [size] at *; omega) (by intro i hm; have := hv i hm; dsimp [size] at *; omega)
  convert h using 1; dsimp [size]; ring

/-- Every raw common-cut fold accumulator has a fixed polynomial unary size bound. -/
private theorem cut_scan_code (s : BufferState) (positions : List ℕ) :
    (encBufferState (Cuts.scan s positions)).length ≤
      100 * ((encBufferState s).length + 2 * (encBufferState s).length * positions.length + 3) ^ 2 := by
  let size := (encBufferState s).length
  have hs := state_code_fields s
  have hlabel : LabelsBounded s.layout (size + 2) :=
    (labels_of_code s.layout).mono (Nat.add_le_add_right hs.1 2)
  have hcount := layout_counts_of_code s.layout
  have hload (gap : ℕ) : upperLoad s.layout gap ≤ size :=
    List.countP_le_length.trans (hcount.1.trans hs.1)
  have hi := cut_scan_labels s positions hlabel hload
  have hv := cut_scan_positions s positions hs.2.2 hload
  have hc := cut_scan_counts s positions hload
  have hp := Cuts.scan_length s positions
  have h := state_code_le (Cuts.scan s positions) hi
    (by dsimp [size] at *; nlinarith [hc.2.1]) (by dsimp [size] at *; nlinarith [hc.2.2])
    (by dsimp [size] at *; nlinarith) (by intro i hm; have := hv i hm; dsimp [size] at *; omega)
  convert h using 1; dsimp [size]; ring

/-- The same one-variable polynomial bounds every internal-fold prefix. -/
theorem internal_prefix_code (s : BufferState) (positions : List ℕ) (i : ℕ) :
    (encBufferState (s.scan (positions.take i))).length ≤
      100 * ((encBufferState s).length + 2 * (encList encUnary positions).length + 3) ^ 2 := by
  have h := internal_scan_code s (positions.take i)
  have hn := (List.take_sublist i positions).length_le.trans (length_le_length_encList encUnary positions)
  exact h.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2))

/-- The same fixed polynomial bounds every common-cut-fold prefix. -/
theorem cut_prefix_code (s : BufferState) (positions : List ℕ) (i : ℕ) :
    (encBufferState (Cuts.scan s (positions.take i))).length ≤
      100 * ((encBufferState s).length +
        2 * (encBufferState s).length * (encList encUnary positions).length + 3) ^ 2 := by
  have h := cut_scan_code s (positions.take i)
  have hn := (List.take_sublist i positions).length_le.trans (length_le_length_encList encUnary positions)
  have hm := Nat.mul_le_mul_left (2 * (encBufferState s).length) hn
  exact h.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2))

end PushPuzzle.Push.Partner.Resources
