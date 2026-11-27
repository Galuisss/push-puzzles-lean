/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramMainStockGeometry
public import Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramLayout

/-! Each actual whole main-axis block consumes exactly two holes on every genuine endpoint column. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- The literal input prefix of the upper or lower main-axis block, at indices six and seven. -/
@[expose] def mainBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (side : Side) : List Template :=
  (schedule l p (targetHoles l p target \ Boundary.frame).card).take (if side = .upper then 6 else 7)

/-- The upper input is the first row clear; the lower input also contains the preceding upper main read. -/
private theorem mainBefore_eq_firstRows (l : PortLayout) (p : Scales.Parameters)
    (target : List Bool) (side : Side) :
    mainBefore l p target side = firstRowSchedule l p (targetHoles l p target \ Boundary.frame).card ++
      if side = .upper then [] else [mainRound l p .upper] := by
  cases side <;>
    simp only [mainBefore, schedule, preparation, frameSchedule, firstRowSchedule,
      firstTrimSchedule, firstRowKeep, mainRound, mainTop]
  all_goals simp only [reduceCtorEq, ite_true, ite_false, List.cons_append, List.nil_append,
    List.append_nil, List.take_succ_cons, List.take_zero]

private theorem main_front_before (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) :
    mainSourceFront l p target e ⊆ (emit (mainBefore l p target e.side) (targetHoles l p target)).remaining := by
  intro q hq
  obtain ⟨hx, hdepth⟩ := (mem_mainSourceFront l p hl hM haxes target e he q).mp hq
  obtain ⟨hq, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp hq
  have hframe := frame_avoids p hf
  have haxis : q.1.val ∈ axes l p := List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨e.port, List.mem_range.mpr (l.endpoints_port_lt hl he), hx.symm⟩)
  have htrim (side : Side) : ReadAvoids q (trimRound l p side) := by
    intro hr
    obtain ⟨a, ha, _, hcol, _⟩ := (mem_trim_region l p side q).mp hr
    have haux := hcol.symm ▸ l.acceptancePageColumn_aux p hl hM haxes side ha
    exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ haxis)
  have hupper : e.side = .lower → ReadAvoids q (mainRound l p .upper) := by
    intro hside hr
    obtain ⟨_, hreq, _, hpos⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hreq
    obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
    obtain ⟨hfj, hfm⟩ := l.endpoints_level_bounds p hl hM (List.mem_filter.mp hf).1
    have hY := readDepth_add_lt_D p e.level
    have hFY := readDepth_add_lt_D p f.level
    rw [readDepth_eq p hj hjm] at hY
    rw [readDepth_eq p hfj hfm] at hFY
    have hH : p.H = 2 * p.D := rfl
    change q.2.val < p.Y f.level + 2 at hpos
    simp only [pageDepth, hside, reduceCtorEq, ite_false] at hdepth
    omega
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  have hzero : (emit (mainBefore l p target e.side) (targetHoles l p target)).discarded = 0 :=
    take_discarded_zero l p hl hM haxes target _
  apply emit_mem_of_no_reads _ _ hzero ht
  have hfirst : ∀ stage ∈ firstRowSchedule l p (targetHoles l p target \ Boundary.frame).card,
      ReadAvoids q stage := by
    simp only [firstRowSchedule, firstTrimSchedule, List.forall_mem_append,
      List.forall_mem_cons, List.not_mem_nil, forall_false, hclear, htrim, true_and]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial
  have hrest : ∀ stage ∈ (if e.side = .upper then [] else [mainRound l p .upper]), ReadAvoids q stage := by
    intro stage hs
    cases hside : e.side with
    | upper => simp only [hside, ite_true, List.not_mem_nil] at hs
    | lower =>
      simp only [hside, reduceCtorEq, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst stage
      exact hupper hside
  have hall : ∀ stage ∈ mainBefore l p target e.side, ReadAvoids q stage := by
    rw [mainBefore_eq_firstRows]
    exact List.forall_mem_append.mpr ⟨hfirst, hrest⟩
  exact fun side requests hs => hall (.read side requests) hs

/-- The actual whole main read removes precisely the original two-cell endpoint front on that column. -/
private theorem main_removed_stock (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) :
    (((emit (mainBefore l p target e.side) (targetHoles l p target)).remaining.filter
      fun q => q.1.val = p.x e.port).filter fun q => q ∈ (mainRound l p e.side).region) =
      mainSourceFront l p target e := by
  apply Finset.ext
  intro q
  constructor
  · intro hq
    obtain ⟨hq, hr⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
    have hi := take_stock_interior l p target (if e.side = .upper then 6 else 7)
      (by split <;> omega) hq
    exact Finset.mem_filter.mpr ⟨hi, hx, (mainRound_column_region l p hl e he hx).mp hr⟩
  · intro hq
    have hbefore := main_front_before l p hl hM haxes target e he hq
    obtain ⟨_, hx, hy⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbefore, hx⟩,
      (mainRound_column_region l p hl e he hx).mpr hy⟩

/-- Every actual endpoint main-axis block pays exactly two holes, with all repeated requests handled as one block. -/
theorem main_target_column_loss (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) :
    let T := (emit (mainBefore l p target e.side) (targetHoles l p target)).remaining
    let U := (emit [mainRound l p e.side] T).remaining
    (U.filter fun q => q.1.val = p.x e.port).card + 2 =
      (T.filter fun q => q.1.val = p.x e.port).card := by
  classical
  dsimp only
  let T := (emit (mainBefore l p target e.side) (targetHoles l p target)).remaining
  let C := T.filter fun q => q.1.val = p.x e.port
  let R := C.filter fun q => q ∈ (mainRound l p e.side).region
  have hU : (emit [mainRound l p e.side] T).remaining.filter (fun q => q.1.val = p.x e.port) = C \ R := by
    simp only [emit_remaining, allRegions, Finset.union_empty]
    ext q
    simp only [C, R, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hR : R = mainSourceFront l p target e := main_removed_stock l p hl hM haxes target e he
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun q => q ∈ (mainRound l p e.side).region) C)
  change (C \ R).card + R.card = C.card at hc
  have hcard : R.card = 2 := by rw [hR, mainSourceFront_card l p hl hM haxes target e he]
  rw [hcard] at hc
  rw [hU]
  exact hc

end PushPuzzle.Push.AcceptanceProgram
