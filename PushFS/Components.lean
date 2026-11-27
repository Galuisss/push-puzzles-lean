/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Run
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin

/-!
# The wall-only displacement graph

Each box in a simultaneous push follows an arc of this static graph. The number
of predecessors is monotone along arcs, and equality along a path characterizes
remaining in the same strongly connected component.

## Main definitions

* `Displacement`, `StaticReach`, `Component`: wall-only box movement and its SCCs.
* `rank`: cardinality of the static predecessor set.
* `potential`: the sum of ranks over the unlabelled box set.

-/

@[expose] public section

namespace PushPuzzle.PushFS


open scoped BigOperators
open scoped Classical

variable {w h : ℕ}

/-- A box can move from `p` to `q` if both its support and destination are floor. -/
def Displacement (B : Board w h) (p q : Cell w h) : Prop :=
  p ∉ B.walls ∧ ∃ (d : Direction) (rear : Cell w h),
    Adjacent d rear p ∧ Adjacent d p q ∧ rear ∉ B.walls ∧ q ∉ B.walls

/-- Reflexive static displacement reachability, ignoring boxes and player access. -/
abbrev StaticReach (B : Board w h) := Relation.ReflTransGen (Displacement B)

/-- Strong connectivity in the static displacement graph. -/
abbrev SameComponent (B : Board w h) := AntisymmRel (StaticReach B)

/-- Strongly connected components of the wall-only displacement graph. -/
abbrev Component (B : Board w h) := Antisymmetrization (Cell w h) (StaticReach B)

/-- The static SCC containing a cell. -/
def component (B : Board w h) : Cell w h → Component B :=
  toAntisymmetrization (StaticReach B)

theorem component_eq_iff {B : Board w h} {p q : Cell w h} :
    component B p = component B q ↔ SameComponent B p q :=
  toAntisymmetrization_eq (StaticReach B) p q

/-- Number of cells that can statically reach a cell. -/
noncomputable def rank (B : Board w h) (p : Cell w h) : ℕ :=
  (Finset.univ.filter (fun q => StaticReach B q p)).card

private theorem rank_mono {B : Board w h} {p q : Cell w h} (hr : StaticReach B p q) :
    rank B p ≤ rank B q := by
  classical
  exact Finset.card_le_card (Finset.monotone_filter_right _ (fun _ _ h => h.trans hr))

/-- Equal predecessor counts along a path force a return path. -/
theorem sameComponent_of_rank_eq {B : Board w h} {p q : Cell w h}
    (hr : StaticReach B p q) (he : rank B p = rank B q) : SameComponent B p q := by
  classical
  have hs : Finset.univ.filter (fun x => StaticReach B x p) ⊆
      Finset.univ.filter (fun x => StaticReach B x q) :=
    Finset.monotone_filter_right _ (fun _ _ h => h.trans hr)
  have hf := Finset.eq_of_subset_of_card_le hs (Nat.le_of_eq he.symm)
  refine ⟨hr, ?_⟩
  have hq : q ∈ Finset.univ.filter (fun x => StaticReach B x q) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  rw [← hf] at hq
  exact (Finset.mem_filter.mp hq).2

theorem SameComponent.rank_eq {B : Board w h} {p q : Cell w h}
    (he : SameComponent B p q) : rank B p = rank B q :=
  Nat.le_antisymm (rank_mono he.1) (rank_mono he.2)

/-- Rank as a function of the strongly connected component. -/
noncomputable def componentRank (B : Board w h) : Component B → ℕ :=
  Quotient.lift (rank B) (fun _ _ h => SameComponent.rank_eq h)

/-- The wall-only potential of an unlabelled box set. -/
noncomputable def potential (B : Board w h) (s : State w h) : ℕ :=
  ∑ p ∈ s.boxes, rank B p

/-- C1: equal initial and target box counts in every static SCC. -/
def ComponentBalanced (B : Board w h) (initial : State w h) : Prop :=
  ∀ c : Component B,
    (initial.boxes.filter (fun p => component B p = c)).card =
      (B.goals.filter (fun p => component B p = c)).card

theorem ComponentBalanced.potential_eq {B : Board w h} {initial : State w h}
    (hb : ComponentBalanced B initial) :
    potential B initial = ∑ p ∈ B.goals, rank B p := by
  classical
  let : Fintype (Component B) := Fintype.ofSurjective (component B) Quotient.mk_surjective
  have hf (s : Finset (Cell w h)) :
      ∑ p ∈ s, rank B p =
        ∑ c : Component B, (s.filter (fun p => component B p = c)).card * componentRank B c := by
    change (∑ p ∈ s, componentRank B (component B p)) = _
    rw [← Finset.sum_fiberwise_of_maps_to' (g := component B)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _) (componentRank B)]
    simp only [Finset.sum_const, Nat.nsmul_eq_mul]
  change (∑ p ∈ initial.boxes, rank B p) = _
  rw [hf initial.boxes, hf B.goals]
  exact Finset.sum_congr rfl (fun c _ => congrArg (· * componentRank B c) (hb c))

namespace Run

variable {B : Board w h} {d : Direction} {s : State w h} {n : ℕ}

/-- Each moved box, including an internal box, has a floor support cell. -/
private theorem displacement (r : Run B d s n) (i : Fin (n + 1)) (hi : 0 < i.val) :
    Displacement B (r.cell i.castSucc) (r.cell i.succ) := by
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have he : j.succ = i.castSucc := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  exact ⟨r.floor _, d, r.cell j.castSucc, he ▸ r.adjacent j,
    r.adjacent i, r.floor _, r.floor _⟩

/-- Every forward subsegment after the player is a static box path. -/
private theorem staticReach (r : Run B d s n) (i j : Fin (n + 2))
    (hi : 0 < i.val) (hij : i ≤ j) : StaticReach B (r.cell i) (r.cell j) := by
  have hm : ∀ m, i.val ≤ m → ∀ hm : m < n + 2,
      StaticReach B (r.cell i) (r.cell ⟨m, hm⟩) := by
    intro m him
    induction him with
    | refl => intro _; exact .refl
    | @step m him ih =>
      intro hm
      have hpositive : 0 < m := hi.trans_le him
      have hbound : m < n + 1 := by omega
      have hp := ih (by omega)
      have hd := r.displacement ⟨m, hbound⟩ hpositive
      exact hp.tail hd
  exact hm j.val (show i.val ≤ j.val from hij) j.isLt

theorem first_staticReach_end (r : Run B d s n) :
    StaticReach B (r.cell 1) (r.cell ⟨n + 1, by omega⟩) :=
  r.staticReach _ _ (by simp) (by simp only [Fin.le_def, Fin.val_one]; omega)

end Run

theorem Move.potential_mono {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : State w h} (hm : Move B cap d s t) : potential B s ≤ potential B t := by
  classical
  cases hm with
  | walk _ _ _ _ hb => simp only [potential, hb, le_refl]
  | push _ hn _ run _ hb =>
    have hp := run.first_occupied hn
    have hsum := Finset.sum_erase_add s.boxes (rank B) hp
    have hr := rank_mono run.first_staticReach_end
    simp only [potential, hb, Finset.sum_insert
      (fun h => run.empty (Finset.mem_of_mem_erase h))]
    omega

theorem Reachable.potential_mono {B : Board w h} {cap : Option ℕ}
    {s t : State w h} (hr : Reachable B cap s t) : potential B s ≤ potential B t := by
  induction hr with
  | refl => exact le_rfl
  | tail _ hm ih => exact ih.trans hm.choose_spec.potential_mono

/-- Every intermediate state of a C1-balanced successful path has equal potential. -/
theorem potential_eq_on_successful_path {B : Board w h} {cap : Option ℕ}
    {initial s final : State w h} (hb : ComponentBalanced B initial)
    (hbefore : Reachable B cap initial s) (hafter : Reachable B cap s final)
    (hsol : final.boxes = B.goals) : potential B s = potential B initial := by
  classical
  have hlow := hbefore.potential_mono
  have hhigh := hafter.potential_mono
  have he : potential B final = potential B initial := by
    rw [hb.potential_eq]
    simp only [potential, hsol]
  omega

/-- Equal potential on one push keeps its first and last slots in one SCC. -/
theorem Run.component_eq_of_potential_eq {B : Board w h} {d : Direction}
    {s t : State w h} {n : ℕ} (r : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (he : potential B s = potential B t) :
    component B (r.cell 1) = component B (r.cell ⟨n + 1, by omega⟩) := by
  classical
  have hs := Finset.sum_erase_add s.boxes (rank B) (r.first_occupied hn)
  change (∑ p ∈ s.boxes.erase (r.cell 1), rank B p) + rank B (r.cell 1) =
    potential B s at hs
  have ht : potential B t = rank B (r.cell ⟨n + 1, by omega⟩) +
      ∑ p ∈ s.boxes.erase (r.cell 1), rank B p := by
    simp only [potential, hb, Finset.sum_insert
      (fun h => r.empty (Finset.mem_of_mem_erase h))]
  apply component_eq_iff.mpr
  apply sameComponent_of_rank_eq r.first_staticReach_end
  omega

/-- If a run's endpoints share an SCC, all its box slots share that SCC. -/
theorem Run.component_eq_first {B : Board w h} {d : Direction}
    {s : State w h} {n : ℕ} (r : Run B d s n)
    (he : component B (r.cell 1) = component B (r.cell ⟨n + 1, by omega⟩))
    (i : Fin (n + 2)) (hi : 0 < i.val) : component B (r.cell i) = component B (r.cell 1) := by
  apply component_eq_iff.mpr
  refine ⟨?_, r.staticReach _ _ (by simp) (by change 1 ≤ i.val; omega)⟩
  exact (r.staticReach _ _ hi (by change i.val ≤ n + 1; omega)).trans
    (component_eq_iff.mp he).2

/-- A path with equal endpoint potentials can be viewed as potential-preserving steps. -/
theorem Reachable.preserving_potential {B : Board w h} {cap : Option ℕ}
    {s t : State w h} (hr : Reachable B cap s t) (he : potential B s = potential B t) :
    Relation.ReflTransGen (fun a b => Step B cap a b ∧ potential B a = potential B b) s t := by
  induction hr with
  | refl => exact .refl
  | @tail u v hp hm ih =>
    have hl := Reachable.potential_mono hp
    have hh := hm.choose_spec.potential_mono
    have heu : potential B s = potential B u := by omega
    have huv : potential B u = potential B v := by omega
    exact (ih heu).tail ⟨hm, huv⟩

end PushPuzzle.PushFS
