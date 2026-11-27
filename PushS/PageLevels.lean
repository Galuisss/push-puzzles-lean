/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-! Working levels computed from active intervals on two noncrossing pages.
Each rank is the maximum active count minus the number of strict ancestors. -/

public section
namespace PushPuzzle.PushS.PageLevels


/-- A wire joins two ports; a vertex group occupies three consecutive ports. -/
inductive Group where
  | wire (left right : ℕ)
  | triple (first : ℕ)
  deriving DecidableEq

namespace Group

/-- Left endpoint of the group's interval. -/
@[expose] def left : Group → ℕ
  | .wire a _ => a
  | .triple a => a

/-- Right endpoint of the group's interval. -/
@[expose] def right : Group → ℕ
  | .wire _ b => b
  | .triple a => a + 2

/-- Ports belonging to the group. -/
@[expose] def ports : Group → Finset ℕ
  | .wire a b => {a, b}
  | .triple a => {a, a + 1, a + 2}

/-- The middle port of a vertex group. -/
@[expose] def middles : Group → Finset ℕ
  | .wire _ _ => ∅
  | .triple a => {a + 1}

/-- Proper containment of endpoint intervals. -/
@[expose] def Contains (outer inner : Group) : Prop :=
  outer.left ≤ inner.left ∧ inner.right ≤ outer.right ∧
    (outer.left < inner.left ∨ inner.right < outer.right)

instance (outer inner : Group) : Decidable (Contains outer inner) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _)))

private theorem contains_irrefl (g : Group) : ¬g.Contains g := by
  simp only [Contains, lt_self_iff_false, or_self, and_false, not_false_eq_true]

private theorem contains_trans {g h k : Group}
    (hgh : g.Contains h) (hhk : h.Contains k) : g.Contains k := by
  unfold Contains at *
  omega

private theorem left_mem_ports (g : Group) : g.left ∈ g.ports := by
  cases g <;> simp [left, ports]

end Group

/-- An explicit group list on ports numbered from zero. -/
structure Page where
  portCount : ℕ
  groups : List Group

namespace Page

/-- A group's position in the actual list. -/
abbrev Index (p : Page) := Fin p.groups.length

/-- Read a group by its position. -/
@[expose] def group (p : Page) (i : p.Index) : Group := p.groups.get i

/-- Bounded intervals, a partition of the ports, and noncrossing intervals. -/
structure Valid (p : Page) : Prop where
  bounded (i : p.Index) : (p.group i).left < (p.group i).right ∧
    (p.group i).right < p.portCount
  partition (k : ℕ) (hk : k < p.portCount) : ∃! i : p.Index, k ∈ (p.group i).ports
  noncrossing (i j : p.Index) (hij : i ≠ j) :
    (p.group i).right < (p.group j).left ∨
    (p.group j).right < (p.group i).left ∨
    (p.group i).Contains (p.group j) ∨ (p.group j).Contains (p.group i)

/-- Distinct groups in a page partition have distinct left ports. -/
theorem Valid.left_injective {p : Page} (hp : p.Valid) :
    Function.Injective (fun i : p.Index => (p.group i).left) := by
  intro i j hij
  obtain ⟨k, _, hk⟩ := hp.partition (p.group i).left
    ((hp.bounded i).1.trans (hp.bounded i).2)
  have hi := hk i (Group.left_mem_ports (p.group i))
  have hj := hk j (by
    change (p.group i).left ∈ (p.group j).ports
    change (p.group i).left = (p.group j).left at hij
    rw [hij]
    exact Group.left_mem_ports (p.group j))
  exact hi.trans hj.symm

/-- A page partition has at most one group per declared port. -/
theorem Valid.length_le {p : Page} (hp : p.Valid) : p.groups.length ≤ p.portCount := by
  let f : p.Index → Fin p.portCount := fun i =>
    ⟨(p.group i).left, (hp.bounded i).1.trans (hp.bounded i).2⟩
  have hf : Function.Injective f := fun i j h => hp.left_injective (congrArg Fin.val h)
  simpa only [Page.Index, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Groups strictly containing the specified group. -/
@[expose] def ancestors (p : Page) (i : p.Index) : Finset p.Index :=
  Finset.univ.filter fun j => (p.group j).Contains (p.group i)

/-- Groups crossing the gap between ports `k` and `k + 1`. -/
@[expose] def active (p : Page) (k : ℕ) : Finset p.Index :=
  Finset.univ.filter fun i => (p.group i).left ≤ k ∧ k < (p.group i).right

/-- Maximum active-group count over the actual port gaps. -/
@[expose] def maxActive (p : Page) : ℕ :=
  (Finset.range (p.portCount - 1)).sup fun k => (p.active k).card

/-- A concrete nesting rank, decreasing with the number of ancestors. -/
@[expose] def depth (p : Page) (i : p.Index) : ℕ := p.maxActive - (p.ancestors i).card

/-- Actual middle ports of the page's three-port groups. -/
@[expose] def middlePorts (p : Page) : Finset ℕ :=
  Finset.univ.biUnion fun i : p.Index => (p.group i).middles

private theorem self_notMem_ancestors (p : Page) (i : p.Index) :
    i ∉ p.ancestors i := by
  simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Group.contains_irrefl _

private theorem ancestors_insert_subset_active (p : Page) (i : p.Index)
    (hi : (p.group i).left < (p.group i).right) :
    insert i (p.ancestors i) ⊆ p.active (p.group i).left := by
  intro j hj
  simp only [Finset.mem_insert, ancestors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hj
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hj with rfl | hj
  · exact ⟨le_rfl, hi⟩
  · unfold Group.Contains at hj
    omega

/-- Every group's own internal gap witnesses one more active group than its ancestors. -/
private theorem ancestors_card_lt_maxActive (p : Page) (hp : p.Valid) (i : p.Index) :
    (p.ancestors i).card < p.maxActive := by
  have hb := hp.bounded i
  have hs := Finset.card_le_card (p.ancestors_insert_subset_active i hb.1)
  rw [Finset.card_insert_of_notMem (p.self_notMem_ancestors i)] at hs
  have hk : (p.group i).left ∈ Finset.range (p.portCount - 1) := by
    simp only [Finset.mem_range]
    omega
  have hm := Finset.le_sup (f := fun k => (p.active k).card) hk
  unfold maxActive
  omega

private theorem depth_pos (p : Page) (hp : p.Valid) (i : p.Index) : 1 ≤ p.depth i := by
  have := p.ancestors_card_lt_maxActive hp i
  unfold depth
  omega

private theorem depth_le_maxActive (p : Page) (i : p.Index) : p.depth i ≤ p.maxActive :=
  Nat.sub_le _ _

private theorem ancestors_card_lt {p : Page} {i j : p.Index}
    (hij : (p.group i).Contains (p.group j)) :
    (p.ancestors i).card < (p.ancestors j).card := by
  have hsub : insert i (p.ancestors i) ⊆ p.ancestors j := by
    intro k hk
    simp only [Finset.mem_insert] at hk
    simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hk with rfl | hk
    · exact hij
    · exact Group.contains_trans (by simpa only [ancestors, Finset.mem_filter,
        Finset.mem_univ, true_and] using hk) hij
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (p.self_notMem_ancestors i)] at hc
  omega

/-- A containing group has a strictly larger computed rank. -/
theorem depth_parent_gt {p : Page} (hp : p.Valid) {i j : p.Index}
    (hij : (p.group i).Contains (p.group j)) : p.depth j < p.depth i := by
  have ha := ancestors_card_lt hij
  have hb := p.ancestors_card_lt_maxActive hp j
  unfold depth
  omega

private theorem index_eq_of_shared_port {p : Page} (hp : p.Valid)
    {i j : p.Index} {k : ℕ} (hk : k < p.portCount)
    (hi : k ∈ (p.group i).ports) (hj : k ∈ (p.group j).ports) : i = j := by
  obtain ⟨a, _, ha⟩ := hp.partition k hk
  exact (ha i hi).trans (ha j hj).symm

/-- Consecutive three-port groups are leaves of a port partition. -/
theorem triple_leaf {p : Page} (hp : p.Valid) {i j : p.Index} {a : ℕ}
    (hi : p.group i = .triple a) : ¬(p.group i).Contains (p.group j) := by
  intro hc
  have hb := hp.bounded j
  have hc' := hc
  rw [hi] at hc'
  change a ≤ (p.group j).left ∧ (p.group j).right ≤ a + 2 ∧
    (a < (p.group j).left ∨ (p.group j).right < a + 2) at hc'
  have hmem : (p.group j).left ∈ (p.group i).ports := by
    rw [hi]
    simp only [Group.ports, Finset.mem_insert, Finset.mem_singleton]
    omega
  have heq := index_eq_of_shared_port hp (by omega) hmem
    (Group.left_mem_ports (p.group j))
  subst j
  exact Group.contains_irrefl _ hc

end Page

/-- Two explicit pages sharing the same ordered ports. -/
structure Pages where
  portCount : ℕ
  upper : List Group
  lower : List Group

namespace Pages

/-- Upper page. -/
@[expose] def upperPage (p : Pages) : Page := ⟨p.portCount, p.upper⟩

/-- Lower page. -/
@[expose] def lowerPage (p : Pages) : Page := ⟨p.portCount, p.lower⟩

/-- Both pages partition the ports; upper groups are wires. -/
structure Valid (p : Pages) : Prop where
  upper : p.upperPage.Valid
  lower : p.lowerPage.Valid
  upper_wire (i : p.upperPage.Index) : ∃ a b, p.upperPage.group i = .wire a b

/-- Whether an upper group contains a middle port of a lower triple. -/
@[expose] def UsesMiddle (p : Pages) (i : p.upperPage.Index) : Prop :=
  ((p.upperPage.group i).ports ∩ p.lowerPage.middlePorts).Nonempty

instance (p : Pages) (i : p.upperPage.Index) : Decidable (p.UsesMiddle i) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

/-- Upper levels are even at middle ports and odd elsewhere. -/
@[expose] def upperLevel (p : Pages) (i : p.upperPage.Index) : ℕ :=
  if p.UsesMiddle i then 2 * p.upperPage.depth i else 2 * p.upperPage.depth i - 1

/-- Lower triples use level one; wires lie above it. -/
@[expose] def lowerLevel (p : Pages) (i : p.lowerPage.Index) : ℕ :=
  match p.lowerPage.group i with
  | .triple _ => 1
  | .wire _ _ => p.lowerPage.depth i + 1

/-- The two actual arrays of allocated working levels. -/
@[expose] def levels (p : Pages) : List ℕ × List ℕ :=
  (List.ofFn p.upperLevel, List.ofFn p.lowerLevel)

/-- Highest allocated working level, zero for two empty pages. -/
@[expose] def highest (p : Pages) : ℕ :=
  max (Finset.univ.sup p.upperLevel) (Finset.univ.sup p.lowerLevel)

private theorem upperLevel_bounds (p : Pages) (i : p.upperPage.Index) :
    2 * p.upperPage.depth i - 1 ≤ p.upperLevel i ∧
      p.upperLevel i ≤ 2 * p.upperPage.depth i := by
  unfold upperLevel
  split <;> omega

theorem upperLevel_pos (p : Pages) (hp : p.Valid) (i : p.upperPage.Index) :
    1 ≤ p.upperLevel i := by
  have := p.upperLevel_bounds i
  have := p.upperPage.depth_pos hp.upper i
  omega

/-- Upper groups incident to middle ports have even working levels. -/
theorem upperLevel_even (p : Pages) {i : p.upperPage.Index} (hi : p.UsesMiddle i) :
    p.upperLevel i % 2 = 0 := by
  rw [upperLevel, ite_eq_left hi]
  omega

/-- Other upper groups have odd working levels. -/
theorem upperLevel_odd (p : Pages) (hp : p.Valid) {i : p.upperPage.Index}
    (hi : ¬p.UsesMiddle i) : p.upperLevel i % 2 = 1 := by
  have := p.upperPage.depth_pos hp.upper i
  rw [upperLevel, ite_eq_right hi]
  omega

theorem upperLevel_parent_gt {p : Pages} (hp : p.Valid) {i j : p.upperPage.Index}
    (hij : (p.upperPage.group i).Contains (p.upperPage.group j)) :
    p.upperLevel j < p.upperLevel i := by
  have := Page.depth_parent_gt hp.upper hij
  have := p.upperLevel_bounds i
  have := p.upperLevel_bounds j
  omega

theorem lowerLevel_triple (p : Pages) {i : p.lowerPage.Index} {a : ℕ}
    (hi : p.lowerPage.group i = .triple a) : p.lowerLevel i = 1 := by
  simp only [lowerLevel, hi]

theorem lowerLevel_wire_ge_two (p : Pages) (hp : p.Valid) {i : p.lowerPage.Index}
    {a b : ℕ} (hi : p.lowerPage.group i = .wire a b) : 2 ≤ p.lowerLevel i := by
  have := p.lowerPage.depth_pos hp.lower i
  simp only [lowerLevel, hi]
  omega

theorem lowerLevel_parent_gt {p : Pages} (hp : p.Valid) {i j : p.lowerPage.Index}
    (hij : (p.lowerPage.group i).Contains (p.lowerPage.group j)) :
    p.lowerLevel j < p.lowerLevel i := by
  have hd := Page.depth_parent_gt hp.lower hij
  have hi := p.lowerPage.depth_pos hp.lower i
  cases hgi : p.lowerPage.group i with
  | triple a => exact (Page.triple_leaf hp.lower hgi hij).elim
  | wire a b =>
    cases hgj : p.lowerPage.group j <;> simp only [lowerLevel, hgi, hgj] <;> omega

/-- A pagewise bound using the actual maximum active counts. -/
theorem highest_le (p : Pages) :
    p.highest ≤ max (2 * p.upperPage.maxActive) (p.lowerPage.maxActive + 1) := by
  unfold highest
  apply max_le
  · apply Finset.sup_le
    intro i _
    have := p.upperLevel_bounds i
    have := p.upperPage.depth_le_maxActive i
    omega
  · apply Finset.sup_le
    intro i _
    have := p.lowerPage.depth_le_maxActive i
    cases hgi : p.lowerPage.group i <;> simp only [lowerLevel, hgi] <;> omega

/-- A common active-arc budget gives a linear bound on all working levels. -/
theorem highest_le_twice_maxActive (p : Pages) :
    p.highest ≤ 2 * max p.upperPage.maxActive p.lowerPage.maxActive + 2 := by
  have := p.highest_le
  have := le_max_left p.upperPage.maxActive p.lowerPage.maxActive
  have := le_max_right p.upperPage.maxActive p.lowerPage.maxActive
  omega

/-- The ear and common-cut depth budgets give the original two-page scale bound. -/
theorem highest_le_repaired (p : Pages) (upperDepth lowerDepth : ℕ)
    (hu : p.upperPage.maxActive ≤ upperDepth + 1)
    (hl : p.lowerPage.maxActive ≤ upperDepth + lowerDepth + 1) :
    p.highest ≤ 2 * max upperDepth lowerDepth + 2 := by
  have := p.highest_le
  have := le_max_left upperDepth lowerDepth
  have := le_max_right upperDepth lowerDepth
  omega

end Pages
end PushPuzzle.PushS.PageLevels
