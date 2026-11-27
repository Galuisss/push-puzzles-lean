/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortStreetEnumeration
import all PushS.PortSegmentBounds
import all PushS.PortSignalLocality
import all PushS.PortSegments
import CslibFrontier.Foundations.Data.List.Counting

/-! A linear bound for the actual adjacent-column pair emitter. -/

public section

namespace PushPuzzle.PushS.PortLayout


/-- Actual coordinate-adjacent column pairs, in the physical emitter's traversal order. -/
def pageAdjacentColumnPairs (l : PortLayout) (p : Scales.Parameters) (side : Side) : List (ℕ × ℕ) :=
  adjacentPairs (l.pageColumnCoordinates p side)

private theorem adjacent_successor_unique (xs : List ℕ) {a b c : ℕ}
    (hb : (a, b) ∈ adjacentPairs xs) (hc : (a, c) ∈ adjacentPairs xs) : b = c := by
  have hgapB := adjacentPair_gap hb
  have hgapC := adjacentPair_gap hc
  have hmemB := adjacentPair_mem hb
  have hmemC := adjacentPair_mem hc
  have hnotB := hgapB.2 _ hmemC.2
  have hnotC := hgapC.2 _ hmemB.2
  omega

private theorem adjacent_from_length_le (xs : List ℕ) (hxs : xs.Nodup) (a : ℕ) (ha : a ∈ xs) :
    (xs.filterMap fun b =>
      if a < b ∧ !(xs.any fun c => decide (a < c ∧ c < b)) then some (a, b) else none).length ≤ 1 := by
  let next (b : ℕ) : Option (ℕ × ℕ) :=
    if a < b ∧ !(xs.any fun c => decide (a < c ∧ c < b)) then some (a, b) else none
  have shape (b : ℕ) (q : ℕ × ℕ) (hq : q ∈ next b) : q = (a, b) := by
    dsimp only [next] at hq
    split at hq
    · symm; simpa using hq
    · simp at hq
  have hn : (xs.filterMap next).Nodup := List.Nodup.filterMap (fun b c q hb hc =>
    congrArg Prod.snd ((shape b q hb).symm.trans (shape c q hc))) hxs
  have lift (q : ℕ × ℕ) (hq : q ∈ xs.filterMap next) : q ∈ adjacentPairs xs :=
    List.mem_flatMap.mpr ⟨a, ha, hq⟩
  have first (q : ℕ × ℕ) (hq : q ∈ xs.filterMap next) : q.1 = a := by
    obtain ⟨b, _, hb⟩ := List.mem_filterMap.mp hq
    exact congrArg Prod.fst (shape b q (by rw [hb]; simp))
  have hc : (xs.filterMap next).toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro q hq r hr
    have hq := List.mem_toFinset.mp hq
    have hr := List.mem_toFinset.mp hr
    apply Prod.ext
    · exact (first q hq).trans (first r hr).symm
    · have hq' : (a, q.2) ∈ adjacentPairs xs := by
        have h := lift q hq
        change (q.1, q.2) ∈ adjacentPairs xs at h
        rwa [first q hq] at h
      have hr' : (a, r.2) ∈ adjacentPairs xs := by
        have h := lift r hr
        change (r.1, r.2) ∈ adjacentPairs xs at h
        rwa [first r hr] at h
      exact adjacent_successor_unique xs hq' hr'
  rw [List.toFinset_card_of_nodup hn] at hc
  exact hc

private theorem adjacentPairs_linear (xs : List ℕ) (hxs : xs.Nodup) :
    (adjacentPairs xs).length ≤ xs.length := by
  unfold adjacentPairs
  calc
    _ ≤ xs.length * 1 := by
      apply List.length_flatMap_le
      exact fun a ha => adjacent_from_length_le xs hxs a ha
    _ = xs.length := Nat.mul_one _

/-- The actual per-page neighbor-pair list is linear in its distinct column list. -/
theorem pageAdjacentColumnPairs_length_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (side : Side) :
    (l.pageAdjacentColumnPairs p side).length ≤ (l.pageColumnCoordinates p side).length :=
  adjacentPairs_linear _ (l.pageColumnCoordinates_nodup p hl hM ha side)

end PushPuzzle.PushS.PortLayout
