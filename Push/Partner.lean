/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortLayout

/-! Reader partners and order-preserving insertion at lower-group boundaries. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

/-- An actual middle incidence of a lower three-port group. -/
def Middle (l : PortLayout) (i : ℕ) : Prop :=
  ∃ kind first, LowerGroup.gate kind first ∈ l.lowerGroups ∧ i = first + 1

/-- An actual incidence of a lower WIRE. -/
def Ordinary (l : PortLayout) (i : ℕ) : Prop :=
  ∃ a b, LowerGroup.wire a b ∈ l.lowerGroups ∧ (i = a ∨ i = b)

/-- Upper partners of middle incidences are middle incidences or ordinary WIRE ports. -/
structure ReaderPartners (l : PortLayout) : Prop where
  left {a b : ℕ} : (a, b) ∈ l.upperPairs → Middle l a → Middle l b ∨ Ordinary l b
  right {a b : ℕ} : (a, b) ∈ l.upperPairs → Middle l b → Middle l a ∨ Ordinary l a

/-- Insert two fresh ports immediately before the given cut. -/
def shift (cut i : ℕ) : ℕ := if i < cut then i else i + 2

theorem shift_strictMono (cut : ℕ) : StrictMono (shift cut) := by
  intro i j hij
  unfold shift
  split_ifs <;> omega

theorem shift_injective (cut : ℕ) : Function.Injective (shift cut) :=
  (shift_strictMono cut).injective

theorem shift_ne_cut (cut i : ℕ) : shift cut i ≠ cut := by
  unfold shift
  split_ifs <;> omega

theorem shift_ne_cut_succ (cut i : ℕ) : shift cut i ≠ cut + 1 := by
  unfold shift
  split_ifs <;> omega

theorem shift_lt (cut : ℕ) {i n : ℕ} (hi : i < n) : shift cut i < n + 2 := by
  unfold shift
  split_ifs <;> omega

/-- Old ports and the two new ports partition the enlarged finite interval. -/
theorem shift_range (cut n : ℕ) (hc : cut ≤ n) :
    (Finset.range n).image (shift cut) ∪ {cut, cut + 1} = Finset.range (n + 2) := by
  ext i
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨j, hj, rfl⟩ | rfl | rfl)
    · exact shift_lt cut hj
    all_goals omega
  · intro hi
    by_cases he : i = cut ∨ i = cut + 1
    · exact Or.inr he
    apply Or.inl
    by_cases hs : i < cut
    · exact ⟨i, by omega, by simp only [shift, ite_eq_left hs]⟩
    · refine ⟨i - 2, by omega, ?_⟩
      have hsub : ¬i - 2 < cut := by omega
      simp only [shift, ite_eq_right hsub]
      omega

/-- Reindex the first port of a gate and both endpoints of a WIRE. -/
def mapGroup (cut : ℕ) : LowerGroup → LowerGroup
  | .wire a b => .wire (shift cut a) (shift cut b)
  | .gate kind first => .gate kind (shift cut first)

/-- A cut does not split any existing consecutive three-port block. -/
def SafeCut (l : PortLayout) (cut : ℕ) : Prop :=
  ∀ kind first, LowerGroup.gate kind first ∈ l.lowerGroups →
    cut ≤ first ∨ first + 2 < cut

/-- All three existing gate incidences retain their consecutive order. -/
theorem shift_gate {cut first : ℕ} (hs : cut ≤ first ∨ first + 2 < cut) :
    shift cut (first + 1) = shift cut first + 1 ∧
      shift cut (first + 2) = shift cut first + 2 := by
  unfold shift
  split_ifs <;> omega

/-- The actual port word of a lower group. -/
def groupPorts : LowerGroup → List ℕ
  | .wire a b => [a, b]
  | .gate _ first => [first, first + 1, first + 2]

/-- Reindexing a whole gate at a safe cut preserves every original incidence. -/
theorem mapGroup_ports {l : PortLayout} {cut : ℕ} (hs : SafeCut l cut)
    (g : LowerGroup) (hg : g ∈ l.lowerGroups) :
    groupPorts (mapGroup cut g) = (groupPorts g).map (shift cut) := by
  cases g with
  | wire a b => rfl
  | gate kind first =>
    obtain ⟨h₁, h₂⟩ := shift_gate (hs kind first hg)
    simp only [groupPorts, mapGroup, List.map_cons, List.map_nil, h₁, h₂]

end PushPuzzle.Push.Partner
