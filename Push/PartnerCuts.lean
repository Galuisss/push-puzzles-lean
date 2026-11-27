/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerInternalValidity
public import PushS.CombSort
import all Push.PartnerUpperValidity
import all Push.PartnerValidity

/-! Simultaneously cut all active upper arcs at one lower-group boundary. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS PageLevels

/-- An upper arc meets the gap immediately before `cut`. -/
def crosses (cut : ℕ) (ab : ℕ × ℕ) : Bool := decide (ab.1 < cut ∧ cut ≤ ab.2)

/-- The literal active arcs sorted from outside to inside by their left endpoints. -/
def active (l : PortLayout) (cut : ℕ) : List (ℕ × ℕ) :=
  Comb.Sort.run Prod.fst (0, 0) (l.upperPairs.filter (crosses cut))

def passive (l : PortLayout) (cut : ℕ) : List (ℕ × ℕ) :=
  l.upperPairs.filter fun ab => !(crosses cut ab)

theorem mem_active (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) :
    ab ∈ active l cut ↔ ab ∈ l.upperPairs ∧ ab.1 < cut ∧ cut ≤ ab.2 := by
  rw [active, (Comb.Sort.run_perm _ _ _).mem_iff]
  simp only [List.mem_filter, crosses, decide_eq_true_eq]

theorem mem_passive (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) :
    ab ∈ passive l cut ↔ ab ∈ l.upperPairs ∧ ¬(ab.1 < cut ∧ cut ≤ ab.2) := by
  simp only [passive, List.mem_filter, crosses, Bool.not_eq_true', decide_eq_false_iff_not]

theorem active_passive_perm (l : PortLayout) (cut : ℕ) :
    (active l cut ++ passive l cut).Perm l.upperPairs :=
  ((Comb.Sort.run_perm _ _ _).append_right _).trans (List.filter_append_perm _ _)

/-- Move every old port to make room for `count` pairs of new incidences. -/
def shift (cut count i : ℕ) : ℕ := if i < cut then i else i + 2 * count

theorem shift_strictMono (cut count : ℕ) : StrictMono (shift cut count) := by
  intro i j hij
  unfold shift
  split_ifs <;> omega

theorem shift_injective (cut count : ℕ) : Function.Injective (shift cut count) :=
  (shift_strictMono cut count).injective

theorem shift_lt (cut count : ℕ) {i n : ℕ} (hi : i < n) : shift cut count i < n + 2 * count := by
  unfold shift
  split_ifs <;> omega

theorem shift_gate {cut count first : ℕ} (hs : cut ≤ first ∨ first + 2 < cut) :
    shift cut count (first + 1) = shift cut count first + 1 ∧
      shift cut count (first + 2) = shift cut count first + 2 := by
  unfold shift
  split_ifs <;> omega

def mapPair (cut count : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ :=
  (shift cut count ab.1, shift cut count ab.2)

def mapGroup (cut count : ℕ) : LowerGroup → LowerGroup
  | .wire a b => .wire (shift cut count a) (shift cut count b)
  | .gate kind first => .gate kind (shift cut count first)

/-- Left cut incidences close the active arcs in reverse nesting order. -/
def left (cut count j : ℕ) : ℕ := cut + (count - 1 - j)

/-- Right cut incidences reopen the same active arcs in their original nesting order. -/
def right (cut count j : ℕ) : ℕ := cut + count + j

def upperPiece (cut count : ℕ) (p : (ℕ × ℕ) × ℕ) : List (ℕ × ℕ) :=
  [(shift cut count p.1.1, left cut count p.2), (right cut count p.2, shift cut count p.1.2)]

def lowerPiece (cut count : ℕ) (p : (ℕ × ℕ) × ℕ) : LowerGroup :=
  .wire (left cut count p.2) (right cut count p.2)

/-- The actual common-cut output retains all original lower groups and adds the nested WIRE block. -/
def compile (l : PortLayout) (cut : ℕ) : PortLayout :=
  let xs := active l cut
  { portCount := l.portCount + 2 * xs.length
    upperPairs := xs.zipIdx.flatMap (upperPiece cut xs.length) ++
      (passive l cut).map (mapPair cut xs.length)
    lowerGroups := l.lowerGroups.map (mapGroup cut xs.length) ++
      xs.zipIdx.map (lowerPiece cut xs.length) }

theorem left_bounds {cut count j : ℕ} (hj : j < count) :
    cut ≤ left cut count j ∧ left cut count j < cut + count := by
  unfold left
  omega

theorem right_bounds {cut count j : ℕ} (hj : j < count) :
    cut + count ≤ right cut count j ∧ right cut count j < cut + 2 * count := by
  unfold right
  omega

theorem left_lt_right {cut count j : ℕ} (hj : j < count) : left cut count j < right cut count j := by
  have := left_bounds (cut := cut) hj
  have := right_bounds (cut := cut) hj
  omega

/-- New cut incidences are distinct from every shifted old port. -/
theorem shift_ne_fresh (cut count i : ℕ) {j : ℕ} (hj : cut ≤ j ∧ j < cut + 2 * count) :
    shift cut count i ≠ j := by
  unfold shift
  split_ifs <;> omega

theorem active_nested {l : PortLayout} (hl : l.pages.Valid) (cut : ℕ)
    {i j : Fin (active l cut).length} (hij : i < j) :
    ((active l cut).get i).1 < ((active l cut).get j).1 ∧
      ((active l cut).get j).2 < ((active l cut).get i).2 := by
  have hs := Comb.Sort.run_pairwise Prod.fst (0, 0) (l.upperPairs.filter (crosses cut))
  have hle := hs.rel_get_of_lt hij
  change ((active l cut).get i).1 ≤ ((active l cut).get j).1 at hle
  obtain ⟨hi, hia, hib⟩ := (mem_active l cut _).mp (List.get_mem _ i)
  obtain ⟨hj, hja, hjb⟩ := (mem_active l cut _).mp (List.get_mem _ j)
  have hn : (active l cut).Nodup := (Comb.Sort.run_perm _ _ _).nodup_iff.mpr
    ((upperPairs_nodup (inventory_of_pages hl)).filter _)
  have hne : (active l cut).get i ≠ (active l cut).get j := by
    intro he
    have he' := hn.injective_get he
    exact (ne_of_lt hij) he'
  have hleft : ((active l cut).get i).1 ≠ ((active l cut).get j).1 := by
    intro he
    exact hne (shared_upper (inventory_of_pages hl) hi hj
      (i := ((active l cut).get i).1)
      (by simp only [pairPorts, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl trivial)
      (by simp only [pairPorts, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl he))
  have hright : ((active l cut).get i).2 ≠ ((active l cut).get j).2 := by
    intro he
    exact hne (shared_upper (inventory_of_pages hl) hi hj
      (i := ((active l cut).get i).2)
      (by simp only [pairPorts, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr trivial)
      (by simp only [pairPorts, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr he))
  have hcomp := page_compatible_mem hl.upper
    (List.mem_map.mpr ⟨_, hi, rfl⟩) (List.mem_map.mpr ⟨_, hj, rfl⟩) (by
      intro he
      exact hne (Prod.ext (Group.wire.inj he).1 (Group.wire.inj he).2))
  simp only [Compatible, Group.Contains, Group.left, Group.right] at hcomp
  omega

end PushPuzzle.Push.Partner.Cuts
