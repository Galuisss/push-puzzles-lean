/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanNormalizePolyTime
public import Push.AcceptanceProgramRounds
public import Mathlib.Data.Finset.Sort
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive

/-! Canonical unary clear-lane sets and compact round encodings for the actual program emitter. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS Turing.MultiTapeTM

/-- A finite lane set has the canonical increasing unary-list encoding. -/
@[expose] def encLaneSet : Finset ℕ ↪ List Bool where
  toFun lanes := encList encUnary (lanes.sort (· ≤ ·))
  inj' := by
    intro a b he
    have hs := (encList encUnary).injective he
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset hs

noncomputable section

/-- Tagged read requests and clear-lane sets, retaining the physical side. -/
enc_inductive encRound : Round where
  | read : (encFinite Direction), Scan.encRequests
  | clear : (encFinite Direction), encLaneSet

/-- The same standard fields encode literal coordinate-prefix templates. -/
enc_inductive encTemplate : Template where
  | read : (encFinite Direction), Scan.encRequests
  | clear : (encFinite Direction), encLaneSet

/-- Standard framed list encoding of compact actual rounds. -/
abbrev encRounds : List Round ↪ List Bool := encList encRound

/-- Standard framed list encoding of literal coordinate templates. -/
abbrev encTemplates : List Template ↪ List Bool := encList encTemplate

end

/-- Compute canonical increasing distinct lanes by scanning a unary bound from the actual input list. -/
@[expose] def sortedLanes (lanes : List ℕ) : List ℕ :=
  (List.range (lanes.sum + 1)).filter lanes.contains

private theorem sortedLanes_finset (lanes : List ℕ) : (sortedLanes lanes).toFinset = lanes.toFinset := by
  ext lane
  simp only [sortedLanes, List.mem_toFinset, List.mem_filter, List.mem_range, List.contains_iff_mem]
  constructor
  · exact And.right
  · intro hlane
    exact ⟨Nat.lt_succ_of_le (List.single_le_sum (fun _ _ => Nat.zero_le _) lane hlane), hlane⟩

/-- The executable unary lane enumeration is exactly the finite set's canonical sort. -/
private theorem sortedLanes_eq_sort (lanes : List ℕ) : sortedLanes lanes = lanes.toFinset.sort
    (· ≤ ·) := by
  have hn : (sortedLanes lanes).Nodup := List.nodup_range.filter _
  have ho : (sortedLanes lanes).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h)).filter _
  exact ((List.toFinset_sort (· ≤ ·) hn).mpr ho).symm.trans (congrArg (fun s => s.sort (· ≤ ·)) (sortedLanes_finset lanes))

/-- The canonical sorted lane list is already the encoded content of a finite set. -/
@[fun_prop] theorem laneSet_sort_polyTime :
    ComputableInPolyTime (fun lanes : Finset ℕ => lanes.sort (· ≤ ·)) encLaneSet (encList encUnary) :=
  ComputableInPolyTime.id'.of_enc_eq (fun _ => rfl)

/-- Sorting and deduplicating arbitrary unary lane lists uses an actual polynomial-time scan. -/
@[fun_prop] theorem sortedLanes_polyTime :
    ComputableInPolyTime sortedLanes (encList encUnary) (encList encUnary) := by
  have hcontains : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.contains p.2)
      (encPair (encList encUnary) encUnary) encBool := by
    simp only [List.contains_eq_any_beq]
    fun_prop
  unfold sortedLanes
  fun_prop

/-- Ordinary explicit lane lists emit their actual finite clear set in canonical unary form. -/
@[fun_prop] theorem laneSet_ofList_polyTime :
    ComputableInPolyTime (List.toFinset (α := ℕ)) (encList encUnary) encLaneSet :=
  sortedLanes_polyTime.of_enc_eq (fun lanes => congrArg (encList encUnary) (sortedLanes_eq_sort lanes).symm)

/-- Membership in the actual canonically encoded finite lane set is standard polynomial time. -/
@[fun_prop] theorem laneSet_mem_polyTime :
    ComputableInPolyTime (fun p : Finset ℕ × ℕ => decide (p.2 ∈ p.1))
      (encPair encLaneSet encUnary) encBool := by
  have hs : ComputableInPolyTime (fun p : Finset ℕ × ℕ => (p.1.sort (· ≤ ·), p.2))
      (encPair encLaneSet encUnary) (encPair (encList encUnary) encUnary) := by fun_prop
  have hm : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.contains p.2)
      (encPair (encList encUnary) encUnary) encBool := by
    simp only [List.contains_eq_any_beq]
    fun_prop
  exact (hm.comp hs).of_enc_eq (fun p => by
    apply congrArg encBool
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def, decide_eq_true_eq, List.contains_iff_mem, Finset.mem_sort])

/-- Finite clear-set union emits its canonical sorted lane list in standard polynomial time. -/
@[fun_prop] theorem laneSet_union_polyTime :
    ComputableInPolyTime (fun p : Finset ℕ × Finset ℕ => p.1 ∪ p.2)
      (encPair encLaneSet encLaneSet) encLaneSet := by
  have hl : ComputableInPolyTime (fun p : Finset ℕ × Finset ℕ => p.1.sort (· ≤ ·) ++ p.2.sort (· ≤ ·))
      (encPair encLaneSet encLaneSet) (encList encUnary) := by fun_prop
  exact (laneSet_ofList_polyTime.comp hl).of_enc_eq (fun p => by
    apply congrArg encLaneSet
    simp only [Function.comp_def, List.toFinset_append, Finset.sort_toFinset])

/-- Filtering an actual finite lane set by a computed Boolean test is standard polynomial time. -/
private theorem laneSet_filter_polyTime {α : Type} {enc : α ↪ List Bool} {lanes : α → Finset ℕ}
    {keep : α → ℕ → Bool}
    (hl : ComputableInPolyTime lanes enc encLaneSet)
    (hk : ComputableInPolyTime (fun p : α × ℕ => keep p.1 p.2) (encPair enc encUnary) encBool) :
    ComputableInPolyTime (fun a => (lanes a).filter fun lane => keep a lane) enc encLaneSet := by
  have hs := laneSet_sort_polyTime.comp hl
  have hf : ComputableInPolyTime (fun a => ((lanes a).sort (· ≤ ·)).filter (keep a)) enc (encList encUnary) := by
    fun_prop
  exact (laneSet_ofList_polyTime.comp hf).of_enc_eq (fun a => by
    apply congrArg encLaneSet
    ext lane
    simp only [Function.comp_def, List.mem_toFinset, List.mem_filter, Finset.mem_sort, Finset.mem_filter])

/-- An actual finite lane set emits its cardinality in standard unary polynomial time. -/
@[fun_prop] theorem laneSet_card_polyTime :
    ComputableInPolyTime (Finset.card (α := ℕ)) encLaneSet encUnary := by
  have hlen : ComputableInPolyTime (fun lanes : Finset ℕ => (lanes.sort (· ≤ ·)).length) encLaneSet encUnary := by fun_prop
  exact hlen.of_enc_eq (fun lanes => by simp only [Finset.length_sort])

/-- The complete bounded lane interval emits in standard unary polynomial time. -/
@[fun_prop] theorem laneSet_range_polyTime : ComputableInPolyTime Finset.range encUnary encLaneSet := by
  have hr : ComputableInPolyTime List.range encUnary (encList encUnary) := by fun_prop
  exact (laneSet_ofList_polyTime.comp hr).of_enc_eq (fun n => by
    apply congrArg encLaneSet
    ext lane
    simp only [Function.comp_def, List.mem_toFinset, List.mem_range, Finset.mem_range])

/-- Difference of actual finite clear-lane sets is standard polynomial time. -/
@[fun_prop] theorem laneSet_sdiff_polyTime :
    ComputableInPolyTime (fun p : Finset ℕ × Finset ℕ => p.1 \ p.2)
      (encPair encLaneSet encLaneSet) encLaneSet := by
  have hk : ComputableInPolyTime (fun q : (Finset ℕ × Finset ℕ) × ℕ => !decide (q.2 ∈ q.1.2))
      (encPair (encPair encLaneSet encLaneSet) encUnary) encBool := by
    have hargs : ComputableInPolyTime (fun q : (Finset ℕ × Finset ℕ) × ℕ => (q.1.2, q.2))
        (encPair (encPair encLaneSet encLaneSet) encUnary) (encPair encLaneSet encUnary) := by fun_prop
    have hm := laneSet_mem_polyTime.comp hargs
    exact ComputableInPolyTime.bool_not.comp hm
  have hf := laneSet_filter_polyTime (keep := fun p lane => !decide (lane ∈ p.2))
    (ComputableInPolyTime.fst encLaneSet encLaneSet) hk
  exact hf.of_enc_eq (fun p => by
    apply congrArg encLaneSet
    ext lane
    simp only [Finset.mem_sdiff, Finset.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not])

/-- An actual finite family of mapped lane coordinates emits its canonical unary clear set. -/
theorem laneSet_image_polyTime {α : Type} {enc : α ↪ List Bool} {lanes : α → Finset ℕ} {f : α → ℕ → ℕ}
    (hl : ComputableInPolyTime lanes enc encLaneSet)
    (hf : ComputableInPolyTime (fun p : α × ℕ => f p.1 p.2) (encPair enc encUnary) encUnary) :
    ComputableInPolyTime (fun a => (lanes a).image (f a)) enc encLaneSet := by
  have hm := ComputableInPolyTime.mapWithInput (laneSet_sort_polyTime.comp hl) hf
  exact (laneSet_ofList_polyTime.comp hm).of_enc_eq (fun a => by
    apply congrArg encLaneSet
    ext lane
    simp only [Function.comp_def, Finset.mem_image, List.mem_toFinset, List.mem_map, Finset.mem_sort])

/-- A single actual unary lane emits as its canonical singleton clear set. -/
@[fun_prop] theorem laneSet_singleton_polyTime :
    ComputableInPolyTime (fun n : ℕ => ({n} : Finset ℕ)) encUnary encLaneSet := by
  have hl : ComputableInPolyTime (fun n : ℕ => [n]) encUnary (encList encUnary) := by fun_prop
  exact (laneSet_ofList_polyTime.comp hl).of_enc_eq (fun n => by simp [encLaneSet])

/-- Inserting one computed lane into an actual finite clear family is standard polynomial time. -/
@[fun_prop] theorem laneSet_insert_polyTime :
    ComputableInPolyTime (fun p : ℕ × Finset ℕ => insert p.1 p.2)
      (encPair encUnary encLaneSet) encLaneSet := by
  have hu : ComputableInPolyTime (fun p : ℕ × Finset ℕ => ({p.1} : Finset ℕ) ∪ p.2)
      (encPair encUnary encLaneSet) encLaneSet := by fun_prop
  exact hu.of_enc_eq (fun p => by simp)

/-- A decidable geometric predicate gives the same polynomial-time canonical set filter. -/
theorem laneSet_filterDecide_polyTime {α : Type} {enc : α ↪ List Bool} {lanes : α → Finset ℕ}
    {keep : α → ℕ → Prop} [∀ a lane, Decidable (keep a lane)]
    (hl : ComputableInPolyTime lanes enc encLaneSet)
    (hk : ComputableInPolyTime (fun p : α × ℕ => decide (keep p.1 p.2)) (encPair enc encUnary) encBool) :
    ComputableInPolyTime (fun a => (lanes a).filter (keep a)) enc encLaneSet := by
  have hf := laneSet_filter_polyTime (keep := fun a lane => decide (keep a lane)) hl hk
  exact hf.of_enc_eq (fun a => by apply congrArg encLaneSet; ext lane; simp)

end PushPuzzle.Push.AcceptanceProgram
