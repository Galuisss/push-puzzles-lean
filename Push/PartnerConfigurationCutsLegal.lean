/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationCuts
import all Push.PartnerConfiguration
import all Push.PartnerCutsPaths
import all Push.PartnerCutsUpperValidity

/-! Exact weighted legality across every simultaneous upper-WIRE subdivision. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

private theorem cutState_gate_reads {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hs : SafeCut l cut)
    {kind : Shuttle.Kind} {first : ℕ} (hg : LowerGroup.gate kind first ∈ l.lowerGroups)
    (axes leftValues rightValues : List Bool) :
    (cutState l cut axes leftValues rightValues).getD (shift cut (active l cut).length first) false = axes.getD first false ∧
    (cutState l cut axes leftValues rightValues).getD (shift cut (active l cut).length first + 1) false = axes.getD (first + 1) false ∧
    (cutState l cut axes leftValues rightValues).getD (shift cut (active l cut).length first + 2) false = axes.getD (first + 2) false := by
  have hb := inventory_gate_bound hl hg
  obtain ⟨h₁, h₂⟩ := shift_gate (count := (active l cut).length) (hs kind first hg)
  rw [← h₁, ← h₂]
  exact ⟨cutState_old l cut axes leftValues rightValues (by omega), cutState_old l cut axes leftValues rightValues (by omega),
    cutState_old l cut axes leftValues rightValues (by omega)⟩

/-- Copy all old weighted constraints and check the three literal constraints at every new active chain. -/
theorem cutState_legal {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {axes : List Bool} (haxes : l.InputLegal axes) (leftValues rightValues : List Bool)
    (hchain : ∀ p ∈ (active l cut).zipIdx,
      (axes.getD p.1.1 false = true ∨ leftValues.getD p.2 false = true) ∧
      (axes.getD p.1.2 false = true ∨ rightValues.getD p.2 false = true) ∧
      (leftValues.getD p.2 false = false ∨ rightValues.getD p.2 false = false)) :
    (compile l cut).InputLegal (cutState l cut axes leftValues rightValues) := by
  have hi := inventory_of_pages hl
  refine ⟨cutState_length l cut axes leftValues rightValues, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rcases compile_upper_cases l cut (.wire a b) (List.mem_map.mpr ⟨(a, b), hab, rfl⟩) with
      ⟨p, hp, side, he⟩ | ⟨ab, hpassive, he⟩
    · have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      have hm := ((mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)).1
      have hbound := upper_bounds hi hm
      cases side
      · simp only [upperShape, Bool.false_eq_true, ite_false] at he
        cases he
        rw [cutState_right l cut hc axes leftValues rightValues hj, cutState_old l cut axes leftValues rightValues hbound.2]
        exact Or.comm.mp (hchain p hp).2.1
      · simp only [upperShape, ite_true] at he
        cases he
        rw [cutState_old l cut axes leftValues rightValues hbound.1, cutState_left l cut hc axes leftValues rightValues hj]
        exact (hchain p hp).1
    · cases he
      have hbound := upper_bounds hi ((mem_passive l cut ab).mp hpassive).1
      rw [cutState_old l cut axes leftValues rightValues hbound.1, cutState_old l cut axes leftValues rightValues hbound.2]
      exact haxes.upper _ _ ((mem_passive l cut ab).mp hpassive).1
  · intro a b hab
    rcases List.mem_append.mp hab with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | gate kind first => cases he
      | wire x y =>
        simp only [mapGroup, LowerGroup.wire.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hbound := lower_wire_bounds hi hmem
        rw [cutState_old l cut axes leftValues rightValues hbound.1, cutState_old l cut axes leftValues rightValues hbound.2]
        exact haxes.lower_wire _ _ hmem
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp hnew
      cases he
      have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      rw [cutState_left l cut hc axes leftValues rightValues hj, cutState_right l cut hc axes leftValues rightValues hj]
      exact (hchain p hp).2.2
  · intro first hg
    obtain ⟨old, hold, rfl⟩ := (compile_gate_mem l cut .orGate first).mp hg
    obtain ⟨h₀, h₁, h₂⟩ := cutState_gate_reads hi hs hold axes leftValues rightValues
    rw [h₀, h₁, h₂]
    exact haxes.or_gate _ hold
  · intro first hg
    obtain ⟨old, hold, rfl⟩ := (compile_gate_mem l cut .andGate first).mp hg
    obtain ⟨h₀, h₁, h₂⟩ := cutState_gate_reads hi hs hold axes leftValues rightValues
    rw [h₀, h₁, h₂]
    exact haxes.and_gate _ hold

private theorem active_constraints {l : PortLayout} {cut : ℕ} {axes : List Bool}
    (haxes : (compile l cut).InputLegal axes) {p : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) :
    (axes.getD (shift cut (active l cut).length p.1.1) false = true ∨
      axes.getD (left cut (active l cut).length p.2) false = true) ∧
    (axes.getD (shift cut (active l cut).length p.1.2) false = true ∨
      axes.getD (right cut (active l cut).length p.2) false = true) ∧
    (axes.getD (left cut (active l cut).length p.2) false = false ∨
      axes.getD (right cut (active l cut).length p.2) false = false) := by
  have hleft : (shift cut (active l cut).length p.1.1, left cut (active l cut).length p.2) ∈ (compile l cut).upperPairs :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self⟩)
  have hright : (right cut (active l cut).length p.2, shift cut (active l cut).length p.1.2) ∈ (compile l cut).upperPairs :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_of_mem _ List.mem_cons_self⟩)
  have hwire : LowerGroup.wire (left cut (active l cut).length p.2) (right cut (active l cut).length p.2) ∈ (compile l cut).lowerGroups :=
    List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact ⟨haxes.upper _ _ hleft, Or.comm.mp (haxes.upper _ _ hright), haxes.lower_wire _ _ hwire⟩

/-- Every actual common-cut configuration projects to a legal original weighted axis configuration. -/
theorem cutRestrict_legal {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} (hs : SafeCut l cut)
    {axes : List Bool} (haxes : (compile l cut).InputLegal axes) : l.InputLegal (cutRestrict l cut axes) := by
  have hi := inventory_of_pages hl
  refine ⟨cutRestrict_length l cut axes, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hb := upper_bounds hi hab
    rw [cutRestrict_get l cut axes hb.1, cutRestrict_get l cut axes hb.2]
    by_cases hcross : a < cut ∧ cut ≤ b
    · obtain ⟨j, hj⟩ := active_zip_exists ((mem_active l cut (a, b)).mpr ⟨hab, hcross⟩)
      obtain ⟨ha, hb, hw⟩ := active_constraints haxes hj
      cases hA : axes.getD (shift cut (active l cut).length a) false <;>
        cases hB : axes.getD (shift cut (active l cut).length b) false <;>
        cases hP : axes.getD (left cut (active l cut).length j) false <;>
        cases hQ : axes.getD (right cut (active l cut).length j) false <;> simp_all
    · exact haxes.upper _ _ ((compile_old_pair_mem l cut (a, b)).mpr ((mem_passive l cut (a, b)).mpr ⟨hab, hcross⟩))
  · intro a b hab
    have hb := lower_wire_bounds hi hab
    rw [cutRestrict_get l cut axes hb.1, cutRestrict_get l cut axes hb.2]
    exact haxes.lower_wire _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨.wire a b, hab, rfl⟩))
  · intro first hg
    have hb := inventory_gate_bound hi hg
    obtain ⟨h₁, h₂⟩ := shift_gate (count := (active l cut).length) (hs .orGate first hg)
    have ht := haxes.or_gate _ ((compile_gate_mem l cut .orGate _).mpr ⟨first, hg, rfl⟩)
    rw [← h₁, ← h₂] at ht
    rw [cutRestrict_get l cut axes (by omega), cutRestrict_get l cut axes (by omega), cutRestrict_get l cut axes (by omega)]
    exact ht
  · intro first hg
    have hb := inventory_gate_bound hi hg
    obtain ⟨h₁, h₂⟩ := shift_gate (count := (active l cut).length) (hs .andGate first hg)
    have ht := haxes.and_gate _ ((compile_gate_mem l cut .andGate _).mpr ⟨first, hg, rfl⟩)
    rw [← h₁, ← h₂] at ht
    rw [cutRestrict_get l cut axes (by omega), cutRestrict_get l cut axes (by omega), cutRestrict_get l cut axes (by omega)]
    exact ht

/-- The actual canonical alternating common-cut extension preserves all weighted constraints. -/
theorem cutExtend_legal {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {axes : List Bool} (haxes : l.InputLegal axes) :
    (compile l cut).InputLegal (cutExtend l cut axes) := by
  apply cutState_legal hl hc hs haxes
  intro p hp
  rw [activeValues_get hp axes false, activeValues_get hp axes true]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  refine ⟨haxes.upper _ _ ((mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)).1, ?_, ?_⟩
  all_goals cases axes.getD p.1.2 false <;> simp

end PushPuzzle.Push.Partner.Cuts
