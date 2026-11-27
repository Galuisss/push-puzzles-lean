/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCutConsumed
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramLowerFinishStockLocation

/-! Each physical column is selected by at most one southward page-finishing block. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Whether an actual southward read block selects the given whole column. -/
def southReadsColumn (x : ℕ) : Template → Bool
  | .read .south requests => requests.any fun a => a.1 == x
  | _ => false

private theorem southReadsColumn_finish (p : Scales.Parameters) (cols : Finset ℕ) (x : ℕ) :
    southReadsColumn x (lowerFinish p cols) = decide (x ∈ cols) := by
  apply Bool.eq_iff_iff.mpr
  simp only [southReadsColumn, lowerFinish, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨lane, quota⟩, ha, hx⟩
    have hx : lane = x := by simpa only [beq_iff_eq] using hx
    exact hx ▸ ((mem_prefixRequests cols _ lane quota).mp ha).1
  · intro hx
    exact ⟨(x, p.D + 1), (mem_prefixRequests cols _ _ _).mpr ⟨hx, rfl⟩, by simp⟩

private theorem southReadsColumn_row (p : Scales.Parameters) (rows : Finset ℕ) (x : ℕ) :
    southReadsColumn x (readRows p .west rows) = false := rfl

private theorem southReadsColumn_clear (side : Direction) (cols : Finset ℕ) (x : ℕ) :
    southReadsColumn x (.clear side cols) = false := rfl

private theorem level_column_live (l : PortLayout) (p : Scales.Parameters) {j x : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) (hx : x ∈ levelColumns l p .lower j) :
    x ∈ live l p .lower := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨ha, hj'⟩ := List.mem_filter.mp ha
  have hj' : a.level = j := by simpa only [beq_iff_eq] using hj'
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,
    List.mem_filter.mpr ⟨ha, by simpa only [hj', decide_eq_true_eq] using And.intro hj hjm⟩, he⟩)

private theorem level_column_unique (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {i j x : ℕ} (hi : x ∈ levelColumns l p .lower i) (hj : x ∈ levelColumns l p .lower j) : i = j := by
  obtain ⟨a, ha, hax⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
  obtain ⟨b, hb, hbx⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
  obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbj⟩ := List.mem_filter.mp hb
  have hai : a.level = i := by simpa only [beq_iff_eq] using hai
  have hbj : b.level = j := by simpa only [beq_iff_eq] using hbj
  exact hai.symm.trans ((l.acceptanceLowerColumn_level p hl ha hb (hax.trans hbx.symm)).trans hbj)

private theorem countP_le_one_unique {α : Type*} (xs : List α) (f : α → Bool)
    (hn : xs.Nodup) (hu : ∀ a ∈ xs, ∀ b ∈ xs, f a → f b → a = b) : xs.countP f ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hn
    by_cases ha : f a
    · have hz : xs.countP f = 0 := List.countP_eq_zero.mpr (by
        intro b hb hfb
        exact hnot ((hu b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hfb ha) ▸ hb))
      simp [ha, hz]
    · have hi := ih hn (fun b hb c hc => hu b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc))
      simpa [ha] using hi

private theorem pairs_count (l : PortLayout) (p : Scales.Parameters) (x : ℕ) (ks : List ℕ) :
    (lowerPairs l p ks).countP (southReadsColumn x) =
      ks.countP (fun k => decide (x ∈ levelColumns l p .lower (k + 1))) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    change (readRows p .west {p.H - (p.Y (k + 1) + p.Y (k + 2)) / 2} ::
      lowerFinish p (levelColumns l p .lower (k + 1)) :: lowerPairs l p ks).countP _ = _
    simp only [List.countP_cons, southReadsColumn_row, southReadsColumn_finish, ih,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

/-- Every physical column occurs in at most one literal southward page-check block. -/
theorem pageCheck_south_column_count_le_one (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (x : ℕ) :
    (pageCheckStages l p).countP (southReadsColumn x) ≤ 1 := by
  have hupper : (pageChecks l p .upper).countP (southReadsColumn x) = 0 := by
    apply List.countP_eq_zero.mpr
    intro stage hs
    simp only [pageChecks, reduceCtorEq, ite_false, List.mem_append, List.mem_singleton] at hs
    rcases hs with rfl | hs
    · simp only [southReadsColumn_clear, Bool.false_eq_true, not_false_eq_true]
    · obtain ⟨k, _, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [southReadsColumn, readRows]
  have hcount : (pageCheckStages l p).countP (southReadsColumn x) =
      (if x ∈ auxiliaries l p \ live l p .lower then 1 else 0) +
      (List.range (p.levels - 1)).countP (fun k => decide (x ∈ levelColumns l p .lower (k + 1))) := by
    change ((lowerFinish p (auxiliaries l p \ live l p .lower) ::
      readRows p .west {p.H - p.Y 1 / 2} :: .clear .north (cores l p) ::
        lowerPairs l p (List.range (p.levels - 1))) ++ pageChecks l p .upper).countP _ = _
    simp only [List.countP_append, List.countP_cons, southReadsColumn_finish, southReadsColumn_row,
      southReadsColumn_clear, Bool.false_eq_true, ↓reduceIte, hupper, Nat.add_zero, pairs_count,
      decide_eq_true_eq]
    omega
  rw [hcount]
  by_cases hx : x ∈ live l p .lower
  · rw [ite_eq_right (fun h => (Finset.mem_sdiff.mp h).2 hx), Nat.zero_add]
    apply countP_le_one_unique _ _ List.nodup_range
    intro i _ j _ hi hj
    have he := level_column_unique l p hl (of_decide_eq_true hi) (of_decide_eq_true hj)
    omega
  · have hz : (List.range (p.levels - 1)).countP (fun k => decide (x ∈ levelColumns l p .lower (k + 1))) = 0 := by
      apply List.countP_eq_zero.mpr
      intro k hk hf
      exact hx (level_column_live l p (by omega) (by have := List.mem_range.mp hk; omega)
        (of_decide_eq_true hf))
    rw [hz, Nat.add_zero]
    split <;> omega

private theorem findIdx_split {α : Type*} (f : α → Bool) (before after : List α) (a : α)
    (hz : before.countP f = 0) (ha : f a) : (before ++ a :: after).findIdx f = before.length := by
  induction before with
  | nil => simp only [List.nil_append, List.findIdx_cons, ha, ↓reduceIte, List.length_nil]
  | cons b before ih =>
    have hb : ¬ f b := List.countP_eq_zero.mp hz b (List.mem_cons_self ..)
    have htail : before.countP f = 0 := List.countP_eq_zero.mpr (fun c hc =>
      List.countP_eq_zero.mp hz c (List.mem_cons_of_mem _ hc))
    simpa only [List.cons_append, List.findIdx_cons, hb, Bool.false_eq_true, ↓reduceIte, List.length_cons] using
      congrArg (· + 1) (ih htail)

private theorem unique_split_prefix {α : Type*} (xs : List α) (f : α → Bool)
    (hcount : xs.countP f ≤ 1) (before after before' after' : List α) (a b : α)
    (hs : xs = before ++ a :: after) (hs' : xs = before' ++ b :: after')
    (ha : f a) (hb : f b) : before = before' := by
  have hz : before.countP f = 0 := by
    simp only [hs, List.countP_append, List.countP_cons, ha, ↓reduceIte] at hcount
    omega
  have hz' : before'.countP f = 0 := by
    simp only [hs', List.countP_append, List.countP_cons, hb, ↓reduceIte] at hcount
    omega
  have hidx := findIdx_split f before after a hz ha
  have hidx' := findIdx_split f before' after' b hz' hb
  rw [← hs] at hidx
  rw [← hs'] at hidx'
  have hlen : before.length = before'.length := hidx.symm.trans hidx'
  have ht : xs.take before.length = before := by rw [hs]; simp
  have ht' : xs.take before'.length = before' := by rw [hs']; simp
  exact ht.symm.trans ((congrArg xs.take hlen).trans ht')

/-- The real before/after stocks of two south payments in the same physical column agree. -/
theorem pageCheck_south_payments_same (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {T E : Finset (Cell (p.W + 1) (p.H + 1))} {q r : Cell (p.W + 1) (p.H + 1)}
    (pay : RoundPayment (pageCheckStages l p) T E q)
    (pay' : RoundPayment (pageCheckStages l p) T E r)
    (hs : pay.side = .south) (hs' : pay'.side = .south) (hx : q.1 = r.1) :
    pay.before = pay'.before ∧ pay.input = pay'.input ∧ pay.output = pay'.output := by
  have touched (b : Cell (p.W + 1) (p.H + 1))
      (payment : RoundPayment (pageCheckStages l p) T E b) (hside : payment.side = .south)
      (hcol : b.1 = q.1) : southReadsColumn q.1.val (.read payment.side payment.requests) := by
    obtain ⟨request, hr, hline⟩ := payment.on_line
    simp only [hside, Direction.lane] at hline
    simp only [hside, southReadsColumn, List.any_eq_true]
    refine ⟨request, hr, ?_⟩
    simpa only [beq_iff_eq] using hline.symm.trans (congrArg Fin.val hcol)
  have hp := unique_split_prefix _ (southReadsColumn q.1.val)
    (pageCheck_south_column_count_le_one l p hl q.1.val)
    pay.before pay.after pay'.before pay'.after _ _ pay.split pay'.split
    (touched q pay hs rfl) (touched r pay' hs' hx.symm)
  have hi : pay.input = pay'.input := by
    have h := pay.prefix_eval
    rw [hp] at h
    exact Option.some.inj (h.symm.trans pay'.prefix_eval)
  have hst : Template.read pay.side pay.requests = .read pay'.side pay'.requests := by
    have h := pay.split.symm.trans pay'.split
    rw [hp] at h
    exact (List.cons.inj (List.append_cancel_left h)).1
  have hr := pay.read_eval
  rw [hp, hi, hst] at hr
  exact ⟨hp, hi, Option.some.inj (hr.symm.trans pay'.read_eval)⟩

/-- A real south payment occurs at any specified selected-column occurrence in the literal page schedule. -/
theorem pageCheck_south_payment_before_at (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {T E : Finset (Cell (p.W + 1) (p.H + 1))} {q : Cell (p.W + 1) (p.H + 1)}
    (pay : RoundPayment (pageCheckStages l p) T E q) (hs : pay.side = .south)
    (n : ℕ) (cols : Finset ℕ)
    (hi : (pageCheckStages l p)[n]? = some (.read .south (prefixRequests cols fun _ => p.D + 1)))
    (hx : q.1.val ∈ cols) :
    pay.before = (pageCheckStages l p).take n := by
  have hsplit : pageCheckStages l p = (pageCheckStages l p).take n ++
      lowerFinish p cols :: (pageCheckStages l p).drop (n + 1) := by
    calc
      pageCheckStages l p = (pageCheckStages l p).take (n + 1) ++ (pageCheckStages l p).drop (n + 1) :=
        (List.take_append_drop _ _).symm
      _ = _ := by simp only [List.take_add_one, hi, Option.toList_some, List.append_assoc, List.singleton_append, lowerFinish]
  have hpay : southReadsColumn q.1.val (.read pay.side pay.requests) := by
    obtain ⟨request, hr, he⟩ := pay.on_line
    simp only [hs, Direction.lane] at he
    simp only [hs, southReadsColumn, List.any_eq_true]
    exact ⟨request, hr, by simpa only [beq_iff_eq] using he.symm⟩
  have hfirst : southReadsColumn q.1.val (lowerFinish p cols) := by
    rw [southReadsColumn_finish]
    exact decide_eq_true hx
  exact unique_split_prefix _ (southReadsColumn q.1.val)
    (pageCheck_south_column_count_le_one l p hl q.1.val)
    pay.before pay.after ((pageCheckStages l p).take n) ((pageCheckStages l p).drop (n + 1)) _ _
    pay.split hsplit hpay hfirst

end PushPuzzle.Push.AcceptanceSoundness
