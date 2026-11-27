/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Labels
public import PushFS.StaticTracks
import Mathlib.Order.Hom.Set
import Mathlib.Order.Preorder.Finite

/-!
# Physical target identities from unlabelled storage

The compiler's source and target slots preserve strict coordinate order within
each source SCC. On a C1–C3 successful path, physical boxes stay on their initial
straight SCC and cannot overtake. The actual and prescribed final positions are
therefore increasing enumerations of the same finite target set, and agree.

## Main results

* `SlotMatching.Ordered.matches_target`: real physical trajectories match the prescribed slots.
* `SlotMatching.Ordered.lift_success`: lift unlabelled success with exact terminal identities.

The finite-order argument uses Mathlib's uniqueness theorem for strictly
increasing maps with equal ranges.
-/

@[expose] public section

namespace PushPuzzle.PushFS


open Gadgets
open scoped Classical

variable {w h : ℕ} {Label : Type} [Fintype Label]

private def along (horizontal : Bool) (p : Cell w h) : ℕ :=
  if horizontal then p.1.val else p.2.val

private def across (horizontal : Bool) (p : Cell w h) : ℕ :=
  if horizontal then p.2.val else p.1.val

private theorem coordinate_ext (axis : Bool) {p q : Cell w h}
    (ha : along axis p = along axis q) (hc : across axis p = across axis q) : p = q := by
  cases axis <;> simp only [along, across, Bool.false_eq_true, ↓reduceIte] at * <;>
    exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))

private theorem adjacent_unit_bound (axis : Bool) {d : Direction} {p q : Cell w h}
    (ha : Adjacent d p q) : along axis q ≤ along axis p + 1 ∧ along axis p ≤ along axis q + 1 := by
  cases axis <;> cases d <;> simp only [along, Adjacent, Bool.false_eq_true, ↓reduceIte] at * <;>
    constructor <;> omega

private theorem step_preserves_order {B : Board w h} {S T : LabelledState Label w h}
    (axis : Bool) (hs : LabelledState.Step B S T) (i j : Label)
    (hcross : across axis (T.position i) = across axis (T.position j))
    (horder : along axis (S.position i) < along axis (S.position j)) :
    along axis (T.position i) < along axis (T.position j) := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact Nat.lt_irrefl _ horder
  have hne : along axis (T.position i) ≠ along axis (T.position j) := by
    intro he
    exact hij (T.injective (coordinate_ext axis he hcross))
  obtain ⟨d, _, hwalk | hpush⟩ := hs
  · simpa only [hwalk.2] using horder
  · obtain ⟨q, _, hq, _, _, hpos⟩ := hpush
    have hbound := adjacent_unit_bound axis hq
    by_cases hi : S.position i = T.state.player
    · have hj : S.position j ≠ T.state.player := by
        intro hj
        exact hij (S.injective (hi.trans hj.symm))
      simp only [hpos, Function.comp_apply, hi, shiftBox_source, shiftBox_other hj] at hne ⊢
      rw [hi] at horder
      omega
    · by_cases hj : S.position j = T.state.player
      · simp only [hpos, Function.comp_apply, hj, shiftBox_source, shiftBox_other hi] at hne ⊢
        rw [hj] at horder
        omega
      · simpa only [hpos, Function.comp_apply, shiftBox_other hi, shiftBox_other hj] using horder

private theorem reachable_preserves_order {B : Board w h} {S T : LabelledState Label w h}
    (axis : Bool) (hr : LabelledState.Reachable B S T)
    (he : potential B S.state = potential B T.state) (c : Component B)
    (hline : ∀ p q, component B p = c → component B q = c → across axis p = across axis q)
    (i j : Label) (hi : component B (S.position i) = c) (hj : component B (S.position j) = c)
    (horder : along axis (S.position i) < along axis (S.position j)) :
    along axis (T.position i) < along axis (T.position j) := by
  induction hr with
  | refl => exact horder
  | @tail U V hr hs ih =>
    have hlo := Reachable.potential_mono (LabelledState.Reachable.forget hr)
    have hhi := hs.forget.choose_spec.potential_mono
    have hp : potential B S.state = potential B U.state := by omega
    have hci := (LabelledState.Reachable.component_eq (hr.tail hs) he i).symm.trans hi
    have hcj := (LabelledState.Reachable.component_eq (hr.tail hs) he j).symm.trans hj
    exact step_preserves_order axis hs i j (hline _ _ hci hcj) (ih hp)

private theorem ordered_image_unique (sources : Finset Label) (key : Label → ℕ)
    (hkey : Set.InjOn key (sources : Set Label)) (f g : Label → ℕ)
    (hf : ∀ i ∈ sources, ∀ j ∈ sources, key i < key j → f i < f j)
    (hg : ∀ i ∈ sources, ∀ j ∈ sources, key i < key j → g i < g j)
    (himage : sources.image f = sources.image g) : ∀ i ∈ sources, f i = g i := by
  classical
  let σ := {i : Label // i ∈ sources}
  let _ : LinearOrder σ := LinearOrder.lift' (fun i : σ => key i.val) (by
    intro i j he
    exact Subtype.ext (hkey i.property j.property he))
  have hf' : StrictMono (fun i : σ => f i.val) :=
    fun i j hij => hf i.val i.property j.val j.property hij
  have hg' : StrictMono (fun i : σ => g i.val) :=
    fun i j hij => hg i.val i.property j.val j.property hij
  have hrange : Set.range (fun i : σ => f i.val) = Set.range (fun i : σ => g i.val) := by
    ext n
    constructor
    · rintro ⟨i, rfl⟩
      have hm : f i.val ∈ sources.image g := by
        rw [← himage]
        exact Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
      exact ⟨⟨j, hj⟩, heq⟩
    · rintro ⟨i, rfl⟩
      have hm : g i.val ∈ sources.image f := by
        rw [himage]
        exact Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
      exact ⟨⟨j, hj⟩, heq⟩
  have heq := (hf'.range_inj_of_wellFoundedLT hg').mp hrange
  exact fun i hi => congrFun heq (⟨i, hi⟩ : σ)

private theorem component_image {B : Board w h} (source f : Label → Cell w h)
    (goals : Finset (Cell w h)) (himage : Finset.univ.image f = goals)
    (hc : ∀ i, component B (source i) = component B (f i)) (c : Component B) :
    (Finset.univ.filter (fun i => component B (source i) = c)).image f =
      goals.filter (fun p => component B p = c) := by
  classical
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, (hc i).symm.trans hi⟩
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · rintro ⟨hp, hpc⟩
    rw [← himage] at hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i, (hc i).trans hpc, rfl⟩

namespace SlotMatching

variable {I : Instance} (M : SlotMatching I Label)

/-- A compiler-side order check on source and target slots within each initial SCC. -/
structure Ordered : Prop where
  /-- Left-to-right source order is kept by the prescribed target slots. -/
  horizontal : ∀ i j, component I.board (M.source i) = component I.board (M.source j) →
    (M.source i).1.val < (M.source j).1.val → (M.target i).1.val < (M.target j).1.val
  /-- Top-to-bottom source order is kept by the prescribed target slots. -/
  vertical : ∀ i j, component I.board (M.source i) = component I.board (M.source j) →
    (M.source i).2.val < (M.source j).2.val → (M.target i).2.val < (M.target j).2.val

/-- The complete physical identities prescribed by the compiler's initial slots. -/
def initialLabelled : LabelledState Label I.width I.height where
  state := I.initial
  position := M.source
  injective := M.source.injective
  boxes_image := by rw [← Finset.map_eq_image]; exact M.source_image

private theorem ordered_axis (ho : M.Ordered) (axis : Bool) (i j : Label)
    (hc : component I.board (M.source i) = component I.board (M.source j))
    (hij : along axis (M.source i) < along axis (M.source j)) :
    along axis (M.target i) < along axis (M.target j) := by
  cases axis
  · exact ho.vertical i j hc hij
  · exact ho.horizontal i j hc hij

private theorem matches_in_component (ho : M.Ordered)
    {T : LabelledState Label I.width I.height}
    (hr : LabelledState.Reachable I.board M.initialLabelled T)
    (hsol : T.state.boxes = I.board.goals)
    (he : potential I.board I.initial = potential I.board T.state)
    (axis : Bool) (c : Component I.board)
    (hline : ∀ p q, component I.board p = c → component I.board q = c →
      across axis p = across axis q) (i : Label) (hi : component I.board (M.source i) = c) :
    T.position i = M.target i := by
  classical
  let sources : Finset Label := Finset.univ.filter (fun j => component I.board (M.source j) = c)
  have mem_sources (j : Label) : j ∈ sources ↔ component I.board (M.source j) = c := by
    simp only [sources, Finset.mem_filter, Finset.mem_univ, true_and]
  have hactual (j : Label) : component I.board (M.source j) = component I.board (T.position j) :=
    LabelledState.Reachable.component_eq hr he j
  have htarget (j : Label) : component I.board (M.source j) = component I.board (M.target j) :=
    component_eq_iff.mpr (M.connected j)
  have hactual_image : Finset.univ.image T.position = I.board.goals := T.boxes_image.trans hsol
  have htarget_image : Finset.univ.image M.target = I.board.goals := by
    rw [← Finset.map_eq_image]
    exact M.target_image
  have himage : sources.image T.position = sources.image M.target :=
    (component_image M.source T.position I.board.goals hactual_image hactual c).trans
      (component_image M.source M.target I.board.goals htarget_image htarget c).symm
  have hkey : Set.InjOn (fun j => along axis (M.source j)) (sources : Set Label) := by
    intro j hj k hk hjk
    exact M.source.injective (coordinate_ext axis hjk
      (hline _ _ ((mem_sources j).mp hj) ((mem_sources k).mp hk)))
  have hf : ∀ j ∈ sources, ∀ k ∈ sources,
      along axis (M.source j) < along axis (M.source k) →
        along axis (T.position j) < along axis (T.position k) := by
    intro j hj k hk hjk
    exact reachable_preserves_order axis hr he c hline j k
      ((mem_sources j).mp hj) ((mem_sources k).mp hk) hjk
  have hg : ∀ j ∈ sources, ∀ k ∈ sources,
      along axis (M.source j) < along axis (M.source k) →
        along axis (M.target j) < along axis (M.target k) := by
    intro j hj k hk hjk
    exact ordered_axis M ho axis j k
      (((mem_sources j).mp hj).trans ((mem_sources k).mp hk).symm) hjk
  have himage' : sources.image (fun j => along axis (T.position j)) =
      sources.image (fun j => along axis (M.target j)) := by
    simpa only [Finset.image_image, Function.comp_def] using
      congrArg (Finset.image (along axis)) himage
  have hcoord := ordered_image_unique sources _ hkey _ _ hf hg himage' i ((mem_sources i).mpr hi)
  exact coordinate_ext axis hcoord
    (hline _ _ ((hactual i).symm.trans hi) ((htarget i).symm.trans hi))

variable {M}

/-- Every successful real physical trajectory ends at the compiler's prescribed target slots. -/
theorem Ordered.matches_target (ho : M.Ordered) (cert : Certificate I)
    {T : LabelledState Label I.width I.height}
    (hr : LabelledState.Reachable I.board M.initialLabelled T)
    (hsol : T.state.boxes = I.board.goals) : T.position = M.target := by
  have he : potential I.board I.initial = potential I.board T.state := by
    rw [cert.balanced.potential_eq]
    simp only [potential, hsol]
  funext i
  have hmem : M.source i ∈ I.initial.boxes := by
    rw [← M.source_image]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rcases cert.linear (M.source i) hmem with hx | hy
  · exact matches_in_component M ho hr hsol he false _
      (fun p q hp hq => congrArg Fin.val (hx p q hp hq)) i rfl
  · exact matches_in_component M ho hr hsol he true _
      (fun p q hp hq => congrArg Fin.val (hy p q hp hq)) i rfl

/-- Lift any unlabelled successful trajectory to actual physical identities with exact final slots. -/
theorem Ordered.lift_success (ho : M.Ordered) (cert : Certificate I) {cap : Option ℕ}
    {final : State I.width I.height}
    (hr : Reachable I.board cap I.initial final) (hsol : final.boxes = I.board.goals) :
    ∃ T : LabelledState Label I.width I.height,
      T.state = final ∧ LabelledState.Reachable I.board M.initialLabelled T ∧ T.position = M.target := by
  have hu : Reachable I.board none I.initial final := hr.mono (cap' := none) (fun _ _ => trivial)
  have hs := cert.reachable_one_of_solved hu hsol
  obtain ⟨T, ht, hreach⟩ := LabelledState.lift_reachable I.board M.initialLabelled hs
  refine ⟨T, ht, hreach, ho.matches_target cert hreach ?_⟩
  rw [ht]
  exact hsol

end SlotMatching

end PushPuzzle.PushFS
