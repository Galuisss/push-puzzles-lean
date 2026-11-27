/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramTrimStock
public import PushS.PortEndpointFStock
import all Push.AcceptanceProgramTrimStock
import all PushS.PortEndpointFStock

/-! Each actual first trim pays the complete non-frame f corridor, including all three near work depths. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem f_interior_iff (p : Scales.Parameters) (e : Endpoint)
    (column : 0 < EndpointStreet.f.column p e ∧ EndpointStreet.f.column p e < p.W)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointFWalk p e \ Boundary.frame ↔ q.1.val = EndpointStreet.f.column p e ∧
      1 ≤ pageDepth p e.side q ∧ pageDepth p e.side q ≤ readDepth p e.level + 2 := by
  have hY := readDepth_add_lt_H p e.level
  have hq := q.2.isLt
  rw [Finset.mem_sdiff, mem_endpointFWalk]
  simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  cases e.side <;> simp only [pageDepth, reduceCtorEq, ite_true, ite_false]
  all_goals constructor
  all_goals first
    | rintro ⟨⟨hx, v, hv, hy⟩, hframe⟩; exact ⟨hx, by omega, by omega⟩
    | rintro ⟨hx, hlo, hhi⟩; exact ⟨⟨hx, by first | exact ⟨q.2.val, by omega, rfl⟩ | exact ⟨p.H - q.2.val, by omega, by omega⟩⟩, by omega⟩

private theorem f_column_bounds (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    0 < EndpointStreet.f.column p e ∧ EndpointStreet.f.column p e < p.W := by
  obtain ⟨a, ha, hx, _, _⟩ := endpoint_trim_column l p e he .f
  obtain ⟨_, _, hlo, hhi⟩ := pageColumn_bounds l p hl hM haxes e.side ha
  exact hx ▸ ⟨hlo, hhi⟩

/-- The actual non-frame f corridor has exactly its work depth plus two cells. -/
theorem endpoint_f_interior_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    (endpointFWalk p e \ Boundary.frame).card = readDepth p e.level + 2 := by
  classical
  have column := f_column_bounds l p hl hM haxes e he
  have hY := readDepth_add_lt_H p e.level
  have hcount : (Finset.Ico 1 (readDepth p e.level + 3)).card = readDepth p e.level + 2 := by
    rw [Nat.card_Ico]
    omega
  rw [← hcount]
  apply Finset.card_bij (fun q _ => pageDepth p e.side q)
  · intro q hq
    obtain ⟨_, hlo, hhi⟩ := (f_interior_iff p e column q).mp hq
    exact Finset.mem_Ico.mpr ⟨hlo, by omega⟩
  · intro q hq r hr equal
    have hqx := ((f_interior_iff p e column q).mp hq).1
    have hrx := ((f_interior_iff p e column r).mp hr).1
    apply Prod.ext (Fin.ext (hqx.trans hrx.symm))
    apply Fin.ext
    have hq' := q.2.isLt
    have hr' := r.2.isLt
    dsimp only [pageDepth] at equal
    split at equal <;> omega
  · intro v hv
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hv
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨EndpointStreet.f.column p e, by omega⟩, ⟨if e.side = .upper then v else p.H - v, by split <;> omega⟩)
    have depth : pageDepth p e.side q = v := by
      dsimp only [q, pageDepth]
      split_ifs <;> omega
    refine ⟨q, (f_interior_iff p e column q).mpr ⟨rfl, ?_, ?_⟩, depth⟩ <;> rw [depth] <;> omega

/-- Every original non-frame f hole survives the frame, side clear and preceding opposite-page trim. -/
theorem endpoint_f_before_trim (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointFWalk p e \ Boundary.frame ⊆
      (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining := by
  intro q hq
  obtain ⟨hwalk, hframe⟩ := Finset.mem_sdiff.mp hq
  have htarget : q ∈ targetHoles l p target := l.endpointFWalk_subset_encoded p hl hM haxes (l.canonical target) e he hwalk
  have hdepth := ((f_interior_iff p e (f_column_bounds l p hl hM haxes e he) q).mp hq).2.2
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  cases hs : e.side with
  | lower =>
    simpa only [trimBeforeSchedule, hs, reduceCtorEq, ite_false, List.append_nil,
      sideClear_target_remaining l p hl haxes target] using Finset.mem_sdiff.mpr ⟨htarget, hframe⟩
  | upper =>
    rw [trimBeforeSchedule, ite_eq_left rfl, emit_remaining_append,
      sideClear_target_remaining l p hl haxes target]
    simp only [emit_remaining, allRegions, Finset.union_empty]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨htarget, hframe⟩, ?_⟩
    intro removed
    obtain ⟨a, ha, _, _, hlow⟩ := (mem_trim_region l p .lower q).mp removed
    obtain ⟨hj, hjm, _⟩ := pageColumn_bounds l p hl hM haxes .lower ha
    have cutoff := trimDepth_lt_D p hj hjm
    simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at hdepth hlow
    omega

/-- The whole actual first trim pays at least `Y+2` holes in each endpoint's f column. -/
theorem endpoint_f_trim_target_loss (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    let T := (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining
    let U := (emit [trimRound l p e.side] T).remaining
    (U.filter fun q => q.1.val = EndpointStreet.f.column p e).card + (readDepth p e.level + 2) ≤
      (T.filter fun q => q.1.val = EndpointStreet.f.column p e).card := by
  classical
  dsimp only
  let T := (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining
  let U := (emit [trimRound l p e.side] T).remaining
  let F := endpointFWalk p e \ Boundary.frame
  have hU : U = T \ (trimRound l p e.side).region := by
    simp only [U, emit_remaining, allRegions, Finset.union_empty]
  have hFT : F ⊆ T.filter fun q => q.1.val = EndpointStreet.f.column p e := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨endpoint_f_before_trim l p hl hM haxes target e he hq,
      ((f_interior_iff p e (f_column_bounds l p hl hM haxes e he) q).mp hq).1⟩
  have hFR : F ⊆ (trimRound l p e.side).region := by
    intro q hq
    obtain ⟨hx, _, hy⟩ := (f_interior_iff p e (f_column_bounds l p hl hM haxes e he) q).mp hq
    have hr := readDepth_eq p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
    exact endpoint_column_trim l p hl hM e he .f q hx (by rwa [← hr])
  have hUT : U.filter (fun q => q.1.val = EndpointStreet.f.column p e) ⊆
      T.filter (fun q => q.1.val = EndpointStreet.f.column p e) := by
    rw [hU]
    exact Finset.filter_subset_filter _ Finset.sdiff_subset
  have disjoint : Disjoint (U.filter fun q => q.1.val = EndpointStreet.f.column p e) F := by
    apply Finset.disjoint_left.mpr
    intro q hq hf
    exact (Finset.mem_sdiff.mp (hU ▸ (Finset.mem_filter.mp hq).1)).2 (hFR hf)
  have bound := Finset.card_le_card (Finset.union_subset hUT hFT)
  rw [Finset.card_union_of_disjoint disjoint, endpoint_f_interior_card l p hl hM haxes e he] at bound
  exact bound

end PushPuzzle.Push.AcceptanceProgram
