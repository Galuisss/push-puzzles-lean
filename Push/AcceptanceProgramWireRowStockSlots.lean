/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockLedger
public import Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramWireRowStockGeometry
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all PushS.PortWireRail
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! The two unit receiving holes survive to R23; the original r-column slots are its only prior WIRE payments. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem wireWorkRow_not_probe (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (side : Side)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) : wireWorkRow p side j ∉ probeRows l p := by
  intro hr
  obtain ⟨e, he, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
  obtain ⟨he, _⟩ := List.mem_filter.mp he
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  change p.Y e.level + 2 = wireWorkRow p side j at hy
  have hs := work_band_owner p side .upper he0 heM hj hjm
    (y := wireWorkRow p side j) rfl (by rw [← hy]; exact ⟨by omega, le_rfl⟩)
  have hdepth := hs.2
  rw [hdepth] at hy
  rw [← hs.1] at hy
  simp only [wireWorkRow, ite_true] at hy
  omega

private theorem odd_column_read_avoids (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (hodd : q.1.val % 2 = 1) :
    (∀ side, ReadAvoids q (trimRound l p side)) ∧
      (∀ side, ReadAvoids q (mainRound l p side)) ∧ ReadAvoids q (privateRound l p) := by
  have hn : q.1.val ∉ l.streetColumnCoordinates p := by
    intro hx
    have he := l.streetColumnCoordinates_even p hx
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro side hr
    obtain ⟨a, ha, _, hx, _⟩ := (mem_trim_region l p side q).mp hr
    exact hn (hx.symm ▸ List.mem_toFinset.mp (Finset.mem_sdiff.mp (l.acceptancePageColumn_aux p hl hM haxes side ha)).1)
  · intro side hr
    obtain ⟨⟨lane, count⟩, hreq, hx, _⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨e, he, hdata⟩ := List.mem_map.mp hreq
    obtain ⟨he, _⟩ := List.mem_filter.mp he
    have hx : q.1.val = lane := by cases side <;> exact hx
    have hcol := congrArg Prod.fst hdata
    exact hn ((hx.trans hcol.symm) ▸ axis_in_streetColumns l p (l.endpoints_port_lt hl he))
  · intro hr
    have hc := (private_region l p q).mp hr
    have hs := private_column_aux l p hl hM haxes hc.1
    exact hn (List.mem_toFinset.mp (Finset.mem_sdiff.mp hs).1)

private theorem unit_slot_reads_avoid (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)} (hr : q ∈ wireOpenRail p g)
    (hunit : q.1.val = p.x g.left + 1 ∨ q.1.val + 1 = p.x g.right) :
    ∀ stage ∈ wireWorkPrefix l p target, ReadAvoids q stage := by
  have hb := wire_ports l hl hg hw
  have hg0 := placement_level_bounds l hl hg
  have hgM := hg0.2.trans hM
  have hrow := (Finset.mem_filter.mp hr).2.1
  have hrow' : q.2.val = wireWorkRow p g.side g.level := by
    simpa only [wireWorkRow, readDepth_eq p hg0.1 hgM] using hrow
  have hodd : q.1.val % 2 = 1 := by
    have heL := x_even p g.left
    have heR := x_even p g.right
    rcases hunit with h | h <;> omega
  have hnStreet : q.1.val ∉ l.streetColumnCoordinates p := by
    intro hx
    have he := l.streetColumnCoordinates_even p hx
    omega
  obtain ⟨htrim, hmain, hprivate⟩ := odd_column_read_avoids l p hl hM haxes hodd
  have hnGuard : q.1.val ∉ guards l p := by
    intro hx
    have far (port : ℕ) (hp : port < l.portCount) := l.acceptanceGuard_street_far p hx (axis_in_streetColumns l p hp)
    rcases hunit with hx | hx
    · have hf := far g.left (hb.1.trans hb.2)
      simp only [Nat.dist] at hf
      omega
    · have hf := far g.right hb.2
      simp only [Nat.dist] at hf
      omega
  have hnSample : q.1.val ∉ samples l p := by
    intro hx
    have he := PushPuzzle.Push.AcceptanceSoundness.sample_columns_even l p hx
    omega
  have hnCore : q.1.val ∉ cores l p := by
    intro hx
    obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    have hi := gate_center_lt l hl hi
    exact hnStreet (he ▸ axis_in_streetColumns l p hi)
  have hnAxes : q.1.val ∉ axes l p := by
    intro hx
    obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hnStreet (he ▸ axis_in_streetColumns l p (List.mem_range.mp hi))
  have hnProbe : q.2.val ∉ probeRows l p := hrow' ▸ wireWorkRow_not_probe l p hl hM g.side hg0.1 hgM
  have hD := readDepth_add_lt_D p g.level
  have hY := readDepth_ge p hg0.1 hgM
  have hH : p.H = 2 * p.D := rfl
  have hrows : q.2.val ∉ ({0, p.H, p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases hs : g.side <;> simp only [hs, ite_true, reduceCtorEq, ite_false] at hrow <;> omega
  have hnFrame : ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
    apply frame_avoids p
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    · exact hrows (Finset.mem_insert.mpr (Or.inl hd))
    · apply hnStreet
      change q.1.val ∈ [0, p.W] ++ _
      exact List.mem_append_left _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (by omega))))
    · apply hrows
      exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl (by omega)))
    · apply hnStreet
      change q.1.val ∈ [0, p.W] ++ _
      exact List.mem_append_left _ (List.mem_cons.mpr (Or.inl hd))
  have hguardN : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hnGuard
  have hguardS : ReadAvoids q (readColumns p .south (guards l p)) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnGuard
  have hsample : ReadAvoids q (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnSample
  have hcore : ReadAvoids q (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hnCore
  have haxis : ReadAvoids q (.read .north (prefixRequests (axes l p \ cores l p) (fun _ => p.H + 1) ++
      prefixRequests (cores l p) (fun _ => p.H - p.Y 1))) := by
    change q ∉ readRegion .north (_ ++ _)
    rw [readRegion_append]
    exact fun hx => (Finset.mem_union.mp hx).elim
      (avoid_prefix_columns .north (Or.inl rfl) _ _ (fun h => hnAxes (Finset.mem_sdiff.mp h).1))
      (avoid_prefix_columns .north (Or.inl rfl) _ _ hnCore)
  have hrowDM2 : q.2.val ≠ p.D - 2 := fun h => hrows (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inl h)))
  have hrowDP2 : q.2.val ≠ p.D + 2 := fun h => hrows (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hrowDM4 : q.2.val ≠ p.D - 4 := fun h => hrows (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hrowDP4 : q.2.val ≠ p.D + 4 := fun h => hrows (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have hflanks : ReadAvoids q (readRows p .east {p.D - 2, p.D + 2}) :=
    avoid_whole_rows .east (Or.inr rfl) _ (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact fun h => h.elim hrowDM2 hrowDP2)
  have hminus : ReadAvoids q (readRows p .west {p.D - 4}) :=
    avoid_whole_rows .west (Or.inl rfl) _ (by simpa only [Finset.mem_singleton] using hrowDM4)
  have hplus : ReadAvoids q (readRows p .east {p.D + 4}) :=
    avoid_whole_rows .east (Or.inr rfl) _ (by simpa only [Finset.mem_singleton] using hrowDP4)
  have hprobe : ReadAvoids q (readRows p .west (probeRows l p)) :=
    avoid_whole_rows .west (Or.inl rfl) _ hnProbe
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  have hf1 := hnFrame _ (.head _)
  have hf2 := hnFrame _ (.tail _ (.head _))
  have hmTop : ReadAvoids q (mainTop l p) := by simpa only [mainRound, mainTop, ite_true] using hmain .upper
  have hmBottom : ReadAvoids q (mainBottom l p) := by simpa only [mainRound, mainBottom, reduceCtorEq, ite_false] using hmain .lower
  simp only [privateRound, privateColumns] at hprivate
  simp only [wireWorkPrefix, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
    List.take_succ_cons, List.take_zero, List.forall_mem_cons, List.not_mem_nil, forall_false,
    hf1, hf2, hclear, htrim, hmTop, hmBottom, hprivate, hguardN, hguardS, hsample, hcore,
    haxis, hflanks, hminus, hplus, hprobe, true_and]
  exact fun _ => trivial

/-- The two compulsory unit receiving holes of every actual ordinary WIRE survive the whole R23 prefix. -/
theorem wire_unit_slot_survives (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ targetHoles l p target ∩ wireOpenRail p g)
    (hunit : q.1.val = p.x g.left + 1 ∨ q.1.val + 1 = p.x g.right) :
    q ∈ wireWorkReference l p target := by
  apply emit_mem_of_no_reads _ _ (take_discarded_zero l p hl hM haxes target 23) (Finset.mem_inter.mp hq).1
  intro d requests hs
  exact unit_slot_reads_avoid l p hl hM haxes target hg hw (Finset.mem_inter.mp hq).2 hunit _ hs

end PushPuzzle.Push.AcceptanceProgram
