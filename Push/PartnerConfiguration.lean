/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerInternalValidity
public import PushS.PortInputStep
import all Push.PartnerValidity

/-! Actual direction words and weighted interface legality for a two-port ear subdivision. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS PageLevels

/-- Undo an old-port insertion outside its two fresh positions. -/
def unshift (cut i : ℕ) : ℕ := if i < cut then i else i - 2

private theorem unshift_shift (cut i : ℕ) : unshift cut (shift cut i) = i := by
  unfold unshift shift
  split_ifs <;> omega

/-- Direction at one old or fresh port of the concrete ear. -/
def earValue (cut : ℕ) (axes : List Bool) (p q : Bool) (i : ℕ) : Bool :=
  if i = cut then p else if i = cut + 1 then q else axes.getD (unshift cut i) false

/-- Keep every old axis and explicitly set the two fresh WIRE-axis directions. -/
def earState (l : PortLayout) (cut : ℕ) (axes : List Bool) (p q : Bool) : List Bool :=
  (List.range (l.portCount + 2)).map (earValue cut axes p q)

/-- The standard consistent extension has alternating values along the new three-axis chain. -/
def earExtend (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) (axes : List Bool) : List Bool :=
  earState l cut axes (!(axes.getD ab.2 false)) (axes.getD ab.2 false)

/-- Read the exact original axis word at its shifted original port positions. -/
def earRestrict (l : PortLayout) (cut : ℕ) (axes : List Bool) : List Bool :=
  (List.range l.portCount).map fun i => axes.getD (shift cut i) false

@[simp] theorem earState_length (l : PortLayout) (cut : ℕ) (axes : List Bool) (p q : Bool) :
    (earState l cut axes p q).length = l.portCount + 2 := by simp only [earState, List.length_map, List.length_range]

@[simp] theorem earRestrict_length (l : PortLayout) (cut : ℕ) (axes : List Bool) :
    (earRestrict l cut axes).length = l.portCount := by simp only [earRestrict, List.length_map, List.length_range]

private theorem earState_get (l : PortLayout) (cut : ℕ) (axes : List Bool) (p q : Bool) {i : ℕ}
    (hi : i < l.portCount + 2) : (earState l cut axes p q).getD i false = earValue cut axes p q i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [earState_length] using hi)]
  simp only [earState, List.getElem_map, List.getElem_range]

private theorem earState_old (l : PortLayout) (cut : ℕ) (axes : List Bool) (p q : Bool) {i : ℕ}
    (hi : i < l.portCount) : (earState l cut axes p q).getD (shift cut i) false = axes.getD i false := by
  rw [earState_get l cut axes p q (shift_lt cut hi)]
  simp only [earValue, ite_eq_right (shift_ne_cut cut i), ite_eq_right (shift_ne_cut_succ cut i), unshift_shift]

private theorem earState_fresh (l : PortLayout) (cut : ℕ) (hc : cut ≤ l.portCount)
    (axes : List Bool) (p q : Bool) :
    (earState l cut axes p q).getD cut false = p ∧ (earState l cut axes p q).getD (cut + 1) false = q := by
  rw [earState_get l cut axes p q (by omega), earState_get l cut axes p q (by omega)]
  simp only [earValue, ite_true, show cut + 1 ≠ cut by omega, ite_false, and_self]

theorem earRestrict_get (l : PortLayout) (cut : ℕ) (axes : List Bool) {i : ℕ} (hi : i < l.portCount) :
    (earRestrict l cut axes).getD i false = axes.getD (shift cut i) false := by
  rw [List.getD_eq_getElem _ _ (by simpa only [earRestrict_length] using hi)]
  simp only [earRestrict, List.getElem_map, List.getElem_range]

/-- Restricting the actual extended word restores every original axis in its original order. -/
theorem earRestrict_extend (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) (axes : List Bool)
    (hlen : axes.length = l.portCount) : earRestrict l cut (earExtend l cut ab axes) = axes := by
  apply List.ext_getElem (by simpa only [earRestrict_length] using hlen.symm)
  intro i hi hi'
  have hbound : i < l.portCount := by simpa only [earRestrict_length] using hi
  have hr := earRestrict_get l cut (earExtend l cut ab axes) hbound
  have hread : (earExtend l cut ab axes).getD (shift cut i) false = axes.getD i false :=
    earState_old l cut axes _ _ hbound
  rw [hread] at hr
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] using hr

private theorem upper_bounds {l : PortLayout} (hl : PortInventory l) {ab : ℕ × ℕ}
    (hp : ab ∈ l.upperPairs) : ab.1 < l.portCount ∧ ab.2 < l.portCount := by
  constructor
  · exact List.mem_range.mp (hl.upper.mem_iff.mp (List.mem_flatMap.mpr ⟨ab, hp, List.mem_cons_self⟩))
  · exact List.mem_range.mp (hl.upper.mem_iff.mp (List.mem_flatMap.mpr
      ⟨ab, hp, List.mem_cons_of_mem _ List.mem_cons_self⟩))

private theorem upper_endpoints_ne {l : PortLayout} (hl : PortInventory l) {ab : ℕ × ℕ}
    (hp : ab ∈ l.upperPairs) : ab.1 ≠ ab.2 := by
  have hn := (List.nodup_flatMap.mp (hl.upper.nodup_iff.mpr List.nodup_range)).1 ab hp
  simpa only [pairPorts, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_false_eq_true] using hn

private theorem lower_wire_bounds {l : PortLayout} (hl : PortInventory l) {a b : ℕ}
    (hp : LowerGroup.wire a b ∈ l.lowerGroups) : a < l.portCount ∧ b < l.portCount := by
  constructor
  · exact List.mem_range.mp (hl.lower.mem_iff.mp (List.mem_flatMap.mpr
      ⟨.wire a b, hp, List.mem_cons_self⟩))
  · exact List.mem_range.mp (hl.lower.mem_iff.mp (List.mem_flatMap.mpr
      ⟨.wire a b, hp, List.mem_cons_of_mem _ List.mem_cons_self⟩))

private theorem sortPair_supplied (axes : List Bool) (a b : ℕ) :
    (axes.getD (sortPair a b).1 false = true ∨ axes.getD (sortPair a b).2 false = true) ↔
      axes.getD a false = true ∨ axes.getD b false = true := by
  rcases le_total a b with h | h
  · simp only [sortPair, min_eq_left h, max_eq_right h]
  · simp only [sortPair, min_eq_right h, max_eq_left h, or_comm]

private theorem earState_gate_reads {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hs : SafeCut l cut)
    {kind : Shuttle.Kind} {first : ℕ} (hg : LowerGroup.gate kind first ∈ l.lowerGroups)
    (axes : List Bool) (p q : Bool) :
    (earState l cut axes p q).getD (shift cut first) false = axes.getD first false ∧
    (earState l cut axes p q).getD (shift cut first + 1) false = axes.getD (first + 1) false ∧
    (earState l cut axes p q).getD (shift cut first + 2) false = axes.getD (first + 2) false := by
  have hb := inventory_gate_bound hl hg
  obtain ⟨h₁, h₂⟩ := shift_gate (hs kind first hg)
  rw [← h₁, ← h₂]
  exact ⟨earState_old l cut axes p q (by omega), earState_old l cut axes p q (by omega),
    earState_old l cut axes p q (by omega)⟩

/-- The fresh three-constraint chain and the exact old weighted constraints prove legality of the emitted word. -/
theorem earState_legal {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) {axes : List Bool}
    (haxes : l.InputLegal axes) (p q : Bool)
    (ha : axes.getD ab.1 false = true ∨ q = true) (hb : axes.getD ab.2 false = true ∨ p = true)
    (hw : p = false ∨ q = false) : (ear l cut ab).InputLegal (earState l cut axes p q) := by
  have hbound := upper_bounds hl hp
  have hfresh := earState_fresh l cut hc axes p q
  refine ⟨earState_length l cut axes p q, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [ear, List.mem_cons] at hab
    rcases hab with he | he | hold
    · cases he
      apply (sortPair_supplied _ _ _).mpr
      rw [earState_old l cut axes p q hbound.1, hfresh.2]
      exact ha
    · cases he
      apply (sortPair_supplied _ _ _).mpr
      rw [earState_old l cut axes p q hbound.2, hfresh.1]
      exact hb
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases he
      have hm := List.mem_of_mem_erase hmem
      have hbounds := upper_bounds hl hm
      rw [earState_old l cut axes p q hbounds.1, earState_old l cut axes p q hbounds.2]
      exact haxes.upper _ _ hm
  · intro a b hab
    rcases List.mem_append.mp hab with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | gate kind first => cases he
      | wire x y =>
        simp only [mapGroup, LowerGroup.wire.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hbounds := lower_wire_bounds hl hmem
        rw [earState_old l cut axes p q hbounds.1, earState_old l cut axes p q hbounds.2]
        exact haxes.lower_wire _ _ hmem
    · have he := List.mem_singleton.mp hnew
      cases he
      rw [hfresh.1, hfresh.2]
      exact hw
  · intro first hg
    rcases List.mem_append.mp hg with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | wire a b => cases he
      | gate kind oldFirst =>
        simp only [mapGroup, LowerGroup.gate.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        obtain ⟨h₀, h₁, h₂⟩ := earState_gate_reads hl hs hmem axes p q
        rw [h₀, h₁, h₂]
        exact haxes.or_gate _ hmem
    · cases List.mem_singleton.mp hnew
  · intro first hg
    rcases List.mem_append.mp hg with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | wire a b => cases he
      | gate kind oldFirst =>
        simp only [mapGroup, LowerGroup.gate.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        obtain ⟨h₀, h₁, h₂⟩ := earState_gate_reads hl hs hmem axes p q
        rw [h₀, h₁, h₂]
        exact haxes.and_gate _ hmem
    · cases List.mem_singleton.mp hnew

/-- The literal alternating extension preserves every weighted AND/OR and WIRE constraint. -/
theorem earExtend_legal {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) {axes : List Bool}
    (haxes : l.InputLegal axes) : (ear l cut ab).InputLegal (earExtend l cut ab axes) := by
  apply earState_legal hl hc hs hp haxes _ _ (haxes.upper _ _ hp)
  all_goals cases axes.getD ab.2 false <;> simp

/-- Every actual legal ear configuration restricts to a legal original weighted axis configuration. -/
theorem earRestrict_legal {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hs : SafeCut l cut)
    {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) {axes : List Bool}
    (haxes : (ear l cut ab).InputLegal axes) : l.InputLegal (earRestrict l cut axes) := by
  refine ⟨earRestrict_length l cut axes, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hb := upper_bounds hl hab
    rw [earRestrict_get l cut axes hb.1, earRestrict_get l cut axes hb.2]
    by_cases he : (a, b) = ab
    · subst ab
      have ha := (sortPair_supplied axes (shift cut a) (cut + 1)).mp
        (haxes.upper _ _ List.mem_cons_self)
      have hb := (sortPair_supplied axes (shift cut b) cut).mp
        (haxes.upper _ _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hw := haxes.lower_wire cut (cut + 1) (ear_wire_mem l cut (a, b))
      cases hA : axes.getD (shift cut a) false <;> cases hB : axes.getD (shift cut b) false <;>
        cases hP : axes.getD cut false <;> cases hQ : axes.getD (cut + 1) false <;> simp_all
    · exact haxes.upper _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨(a, b), (List.mem_erase_of_ne he).mpr hab, rfl⟩)))
  · intro a b hab
    have hb := lower_wire_bounds hl hab
    rw [earRestrict_get l cut axes hb.1, earRestrict_get l cut axes hb.2]
    exact haxes.lower_wire _ _ (mapGroup_mem_ear hab)
  · intro first hg
    have hb := inventory_gate_bound hl hg
    obtain ⟨h₁, h₂⟩ := shift_gate (hs .orGate first hg)
    have ht := haxes.or_gate _ (mapGroup_mem_ear hg)
    rw [← h₁, ← h₂] at ht
    rw [earRestrict_get l cut axes (by omega), earRestrict_get l cut axes (by omega),
      earRestrict_get l cut axes (by omega)]
    exact ht
  · intro first hg
    have hb := inventory_gate_bound hl hg
    obtain ⟨h₁, h₂⟩ := shift_gate (hs .andGate first hg)
    have ht := haxes.and_gate _ (mapGroup_mem_ear hg)
    rw [← h₁, ← h₂] at ht
    rw [earRestrict_get l cut axes (by omega), earRestrict_get l cut axes (by omega),
      earRestrict_get l cut axes (by omega)]
    exact ht

end PushPuzzle.Push.Partner
