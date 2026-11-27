/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationCutsStep
import all Push.PartnerConfiguration
import all Push.PartnerConfigurationStep
import all Push.PartnerConfigurationCutsStep
import all Push.PartnerCutsUpperValidity

/-! One active upper-WIRE cursor controls exactly its two fresh common-cut axes. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

private def overrideState (l : PortLayout) (cut : ℕ) (axes : List Bool) (j : ℕ) (p q : Bool) : List Bool :=
  cutState l cut axes ((activeValues l cut axes false).set j p) ((activeValues l cut axes true).set j q)

private theorem active_right_ne {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {p q : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) (hq : q ∈ (active l cut).zipIdx)
    (hne : p.2 ≠ q.2) : p.1.2 ≠ q.1.2 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact Ne.symm (ne_of_lt (active_zip_nested hl hp hq h).2)
  · exact ne_of_lt (active_zip_nested hl hq hp h).2

private theorem active_zip_at (l : PortLayout) (cut : ℕ) (j : ℕ) (hj : j < (active l cut).length) :
    ((active l cut)[j], j) ∈ (active l cut).zipIdx := by
  apply List.mem_zipIdx_iff_getElem?.mpr
  exact List.getElem?_eq_getElem hj

private theorem activeValues_length (l : PortLayout) (cut : ℕ) (axes : List Bool) (negate : Bool) :
    (activeValues l cut axes negate).length = (active l cut).length := by simp only [activeValues, List.length_map]

private theorem activeValues_congr {l : PortLayout} {cut : ℕ} {axes next : List Bool}
    (he : ∀ ab ∈ active l cut, axes.getD ab.2 false = next.getD ab.2 false) (negate : Bool) :
    activeValues l cut axes negate = activeValues l cut next negate := by
  apply List.map_congr_left
  intro ab hab
  rw [he ab hab]

private theorem activeValues_override_update {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {owner : (ℕ × ℕ) × ℕ} (hp : owner ∈ (active l cut).zipIdx) (axes : List Bool)
    (negate value : Bool) :
    (activeValues l cut axes negate).set owner.2 value =
      (activeValues l cut (axes.set owner.1.2 (!(axes.getD owner.1.2 false))) negate).set owner.2 value := by
  apply words_eq_of_reads (by simp only [List.length_set, activeValues_length])
  intro j hj
  have hbound : j < (active l cut).length := by simpa only [List.length_set, activeValues_length] using hj
  by_cases he : j = owner.2
  · subst j
    rw [List.getD_set_self (by simpa only [activeValues_length] using hbound),
      List.getD_set_self (by simpa only [activeValues_length] using hbound)]
  · rw [List.getD_set_ne (Ne.symm he), List.getD_set_ne (Ne.symm he)]
    have hz := active_zip_at l cut j hbound
    have hne := active_right_ne hl hp hz (Ne.symm he)
    rw [activeValues_get hz axes negate, activeValues_get hz _ negate, List.getD_set_ne hne]

private theorem set_read_self (axes : List Bool) (i : ℕ) (hi : i < axes.length) :
    axes.set i (axes.getD i false) = axes := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.set_getElem_self hi

private theorem overrideState_eq_extend {l : PortLayout} {cut : ℕ} {owner : (ℕ × ℕ) × ℕ}
    (hp : owner ∈ (active l cut).zipIdx) (axes : List Bool) :
    overrideState l cut axes owner.2 (axes.getD owner.1.2 false) (!(axes.getD owner.1.2 false)) = cutExtend l cut axes := by
  have hj : owner.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hleft := activeValues_get hp axes false
  have hright := activeValues_get hp axes true
  simp only [Bool.false_eq_true, ite_false, ite_true] at hleft hright
  unfold overrideState cutExtend
  rw [← hright, ← hleft, set_read_self _ _ (by simpa only [activeValues_length] using hj),
    set_read_self _ _ (by simpa only [activeValues_length] using hj)]

private theorem overrideState_legal {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {owner : (ℕ × ℕ) × ℕ} (hp : owner ∈ (active l cut).zipIdx)
    {axes : List Bool} (haxes : l.InputLegal axes) (p q : Bool)
    (ha : axes.getD owner.1.1 false = true ∨ p = true)
    (hb : axes.getD owner.1.2 false = true ∨ q = true) (hw : p = false ∨ q = false) :
    (compile l cut).InputLegal (overrideState l cut axes owner.2 p q) := by
  apply cutState_legal hl hc hs haxes
  intro current hcurrent
  have hj : current.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hcurrent
  by_cases he : current.2 = owner.2
  · have hepair := zip_payload_eq hcurrent hp he
    rw [he] at hj ⊢
    rw [List.getD_set_self (by simpa only [activeValues_length] using hj),
      List.getD_set_self (by simpa only [activeValues_length] using hj)]
    rw [hepair]
    exact ⟨ha, hb, hw⟩
  · rw [List.getD_set_ne (Ne.symm he), List.getD_set_ne (Ne.symm he),
      activeValues_get hcurrent axes false, activeValues_get hcurrent axes true]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    refine ⟨haxes.upper _ _ ((mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hcurrent)).1, ?_, ?_⟩
    all_goals cases axes.getD current.1.2 false <;> simp

private theorem overrideState_left_reachable {l : PortLayout} {cut : ℕ} (hc : cut ≤ l.portCount)
    {axes : List Bool} {owner : (ℕ × ℕ) × ℕ} (hp : owner ∈ (active l cut).zipIdx) {p p' q : Bool}
    (hs : (compile l cut).InputLegal (overrideState l cut axes owner.2 p q))
    (ht : (compile l cut).InputLegal (overrideState l cut axes owner.2 p' q)) :
    Relation.ReflTransGen (compile l cut).AxisStep (overrideState l cut axes owner.2 p q)
      (overrideState l cut axes owner.2 p' q) := by
  have hj : owner.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hr := cutState_left_reachable hc hj p' hs (by simpa only [overrideState, List.set_set] using ht)
  simpa only [overrideState, List.set_set] using hr

private theorem overrideState_right_reachable {l : PortLayout} {cut : ℕ} (hc : cut ≤ l.portCount)
    {axes : List Bool} {owner : (ℕ × ℕ) × ℕ} (hp : owner ∈ (active l cut).zipIdx) {p q q' : Bool}
    (hs : (compile l cut).InputLegal (overrideState l cut axes owner.2 p q))
    (ht : (compile l cut).InputLegal (overrideState l cut axes owner.2 p q')) :
    Relation.ReflTransGen (compile l cut).AxisStep (overrideState l cut axes owner.2 p q)
      (overrideState l cut axes owner.2 p q') := by
  have hj : owner.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hr := cutState_right_reachable hc hj q' hs (by simpa only [overrideState, List.set_set] using ht)
  simpa only [overrideState, List.set_set] using hr

private theorem overrideState_old_reachable {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {axes next : List Bool} {owner : (ℕ × ℕ) × ℕ} (hp : owner ∈ (active l cut).zipIdx)
    (he : next = axes.set owner.1.2 (!(axes.getD owner.1.2 false))) {p q : Bool}
    (hs : (compile l cut).InputLegal (overrideState l cut axes owner.2 p q))
    (ht : (compile l cut).InputLegal (overrideState l cut next owner.2 p q)) :
    Relation.ReflTransGen (compile l cut).AxisStep (overrideState l cut axes owner.2 p q)
      (overrideState l cut next owner.2 p q) := by
  have hb := upper_bounds (inventory_of_pages hl) ((mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)).1
  have hlft := activeValues_override_update hl hp axes false p
  have hrgt := activeValues_override_update hl hp axes true q
  rw [← he] at hlft hrgt
  unfold overrideState at hs ht ⊢
  rw [← hlft, ← hrgt] at ht ⊢
  exact cutState_old_reachable hb.2 he hs ht

end PushPuzzle.Push.Partner.Cuts
