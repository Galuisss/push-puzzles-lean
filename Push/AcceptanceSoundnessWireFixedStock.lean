/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalks
public import Push.AcceptanceProgramWireRowStockSlots
public import Push.AcceptanceProgramWireRowStockFixed
import all Push.AcceptanceProgramWireRowStockSlots
import all Push.AcceptanceSoundnessSupportFirst
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportResidual
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all PushS.PortEndpointReaderWalk
import all PushS.PortSegments

/-! Genuine ordinary short-branch holes survive to the actual remaining-working-row input. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem column_unread {p : Scales.Parameters} {q : Cell (p.W + 1) (p.H + 1)}
    (side : Direction) (hd : side = .north ∨ side = .south) (cols : Finset ℕ) (span : ℕ → ℕ)
    (hx : q.1.val ∉ cols) : ¬ReadTouches (.read side (prefixRequests cols span)) q := by
  intro ht
  have hc := prefix_touches p side cols span ht
  rcases hd with rfl | rfl <;> exact hx hc

private theorem short_branch_reads_avoid (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) (side : Side)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ l.endpointShortBranches p e) (hrow : q.2.val = wireWorkRow p side j) :
    ∀ stage ∈ wireWorkPrefix l p target, ¬ReadTouches stage q := by
  have hx := ((mem_endpointShortBranches l p e q).mp hq).1
  have heven := l.streetColumnCoordinates_even p (axis_in_streetColumns l p (l.endpoints_port_lt hl he))
  have hpos := readLength_add_lt_x p e.port 0
  have hodd : q.1.val % 2 = 1 := by
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx <;> omega
  have hnStreet : q.1.val ∉ l.streetColumnCoordinates p := by
    intro hm
    have heven := l.streetColumnCoordinates_even p hm
    omega
  have hnGuard : q.1.val ∉ guards l p := by
    intro hm
    have hfar := l.acceptanceGuard_street_far p hm (axis_in_streetColumns l p (l.endpoints_port_lt hl he))
    simp only [Nat.dist] at hfar
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx <;> omega
  have hnSample : q.1.val ∉ samples l p := by
    intro hm
    have heven := sample_columns_even l p hm
    omega
  have hnAxes : q.1.val ∉ axes l p := by
    intro hm
    exact hnStreet (axes_street l p hm)
  have hnCore : q.1.val ∉ cores l p := fun hm => hnAxes (l.acceptanceCore_subset_axes p hl hm)
  have hnProbe : q.2.val ∉ probeRows l p := hrow ▸ wireWorkRow_not_probe l p hl hM side hj hjm
  have hD := readDepth_add_lt_D p j
  have hY := readDepth_ge p hj hjm
  rw [readDepth_eq p hj hjm] at hD hY
  have hH : p.H = 2 * p.D := rfl
  have hrows : q.2.val ∉ ({0, p.H, p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases hside : side <;> simp only [wireWorkRow, hside, ite_true, reduceCtorEq, ite_false] at hrow <;> omega
  have hframe : ∀ stage ∈ frameSchedule p.W p.H, ¬ReadTouches stage q := by
    intro stage hs ht
    simp only [frameSchedule, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals obtain ⟨⟨lane, count⟩, hreq, hlane⟩ := ht
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hreq
    · change q.1.val = lane at hlane
      apply hnStreet
      change q.1.val ∈ [0, p.W] ++ _
      apply List.mem_append_left
      rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact List.mem_cons.mpr (Or.inl hlane)
      · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr hlane))
    · change q.2.val = lane at hlane
      apply hrows
      rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Finset.mem_insert.mpr (Or.inl hlane)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hlane))
  have htrim (s : Side) : ¬ReadTouches (trimRound l p s) q :=
    fun ht => hnStreet (trim_touch_street l p hl hM haxes s ht)
  have hmain (s : Side) : ¬ReadTouches (mainRound l p s) q :=
    fun ht => hnStreet (main_touch_street l p hl s ht)
  have hprivate : ¬ReadTouches (privateRound l p) q :=
    fun ht => hnStreet (private_touch_street l p hl hM haxes ht)
  have haxis : ¬ReadTouches (axisReadRound l p) q :=
    fun ht => hnStreet (axis_touch_street l p hl ht)
  have hguardN : ¬ReadTouches (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) q :=
    column_unread .north (Or.inl rfl) _ _ hnGuard
  have hguardS : ¬ReadTouches (readColumns p .south (guards l p)) q :=
    column_unread .south (Or.inr rfl) _ _ hnGuard
  have hsample : ¬ReadTouches (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) q :=
    column_unread .south (Or.inr rfl) _ _ hnSample
  have hcore : ¬ReadTouches (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) q :=
    column_unread .north (Or.inl rfl) _ _ hnCore
  have hrowDM2 : q.2.val ≠ p.D - 2 := fun h => hrows (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inl h)))
  have hrowDP2 : q.2.val ≠ p.D + 2 := fun h => hrows (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hrowDM4 : q.2.val ≠ p.D - 4 := fun h => hrows (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hrowDP4 : q.2.val ≠ p.D + 4 := fun h => hrows (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have hflanks : ¬ReadTouches (readRows p .east {p.D - 2, p.D + 2}) q := by
    intro ht
    have hr := row_touches p .east _ (Or.inr rfl) ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    exact hr.elim hrowDM2 hrowDP2
  have hminus : ¬ReadTouches (readRows p .west {p.D - 4}) q :=
    fun ht => hrowDM4 (Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht))
  have hplus : ¬ReadTouches (readRows p .east {p.D + 4}) q :=
    fun ht => hrowDP4 (Finset.mem_singleton.mp (row_touches p .east _ (Or.inr rfl) ht))
  have hprobe : ¬ReadTouches (readRows p .west (probeRows l p)) q :=
    fun ht => hnProbe (row_touches p .west _ (Or.inl rfl) ht)
  have hclear : ∀ s cols, ¬ReadTouches (.clear s cols) q := by intros; exact id
  have hf1 := hframe _ (.head _)
  have hf2 := hframe _ (.tail _ (.head _))
  have hmTop : ¬ReadTouches (mainTop l p) q := by simpa only [mainRound, mainTop, ite_true] using hmain .upper
  have hmBottom : ¬ReadTouches (mainBottom l p) q := by
    simpa only [mainRound, mainBottom, reduceCtorEq, ite_false] using hmain .lower
  simp only [axisReadRound] at haxis
  simp only [privateRound, privateColumns] at hprivate
  simp only [wireWorkPrefix, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
    List.take_succ_cons, List.take_zero]
  simp only [List.forall_mem_cons, List.not_mem_nil, forall_false]
  simp only [hf1, hf2, hclear, htrim, hmTop, hmBottom, hprivate, hguardN, hguardS, hsample]
  simp only [hcore, haxis, hflanks, hminus, hplus, hprobe, not_false_eq_true, true_and]
  exact fun _ => trivial

/-- Every actual short-branch hole on an allocated WIRE work row survives to the real R23 residual. -/
private theorem canonical_short_branch_R23_survives (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (e : Endpoint) (he : e ∈ l.endpoints) (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.endpointShortBranches p e)
    (hrow : q.2.val = wireWorkRow p side j) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 23 := by
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hqt := canonical_ordinaryReaders_empty l p hl hM haxes initial target hgate e he hr .refl ha
    (Finset.mem_union_right _ (Finset.mem_union_right _ hq))
  apply clean_unread_survives _ _ _ _ (roundResidual_clean _ _ _ 23 hc)
    (roundResidual_eval _ _ _ 23 hc) hqt
  exact short_branch_reads_avoid l p hl hM haxes target e he side hj hjm hq hrow

/-- The entire canonical fixed stock of an ordinary work row is present in the actual R23 input. -/
theorem canonical_wire_fixed_stock_at_work (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hordinary : side = .upper ∨ 2 ≤ j)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    wireRowFixedStock l p side j ⊆
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 23 := by
  intro q hq
  have hrow := (Finset.mem_filter.mp hq).2
  obtain ⟨e, he, _, _, hs⟩ := wireRowFixedStock_short l p hl hM haxes hgate side hj hjm hordinary hq
  exact canonical_short_branch_R23_survives l p hl hM haxes initial target hgate hr ha e he side hj hjm hs hrow

end PushPuzzle.Push.AcceptanceSoundness
