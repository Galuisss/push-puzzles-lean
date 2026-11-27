/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsReadout
import all Push.PartnerCutsReadout
import all Push.PartnerValidity
import all Push.PartnerInventory

/-! The finite descending common-cut compiler gives actual reader-safe middle-port partners. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS PageLevels

/-- Test whether a gap is outside every actual three-port block. -/
def safeTest (l : PortLayout) (cut : ℕ) : Bool :=
  l.lowerGroups.all fun g => match g with
  | .wire .. => true
  | .gate _ first => decide (cut ≤ first ∨ first + 2 < cut)

theorem safeTest_eq_true (l : PortLayout) (cut : ℕ) : safeTest l cut = true ↔ SafeCut l cut := by
  constructor
  · intro hs kind first hg
    exact of_decide_eq_true (List.all_eq_true.mp hs (.gate kind first) hg)
  · intro hs
    apply List.all_eq_true.mpr
    intro g hg
    cases g with
    | wire a b => rfl
    | gate kind first => exact decide_eq_true (hs kind first hg)

/-- Cut every active upper arc at one safe original gap and retain the complete old-port position table. -/
def cutAt (s : BufferState) (cut : ℕ) : BufferState :=
  if safeTest s.layout cut then
    ⟨compile s.layout cut, s.ports.map (shift cut (active s.layout cut).length)⟩
  else s

theorem cutAt_valid (s : BufferState) (cut : ℕ) (hs : s.layout.pages.Valid) (hc : cut ≤ s.layout.portCount) :
    (cutAt s cut).layout.pages.Valid := by
  unfold cutAt
  split_ifs with hsafe
  · exact compile_valid hs hc ((safeTest_eq_true s.layout cut).mp hsafe)
  · exact hs

theorem cutAt_length (s : BufferState) (cut : ℕ) : (cutAt s cut).ports.length = s.ports.length := by
  unfold cutAt
  split_ifs <;> simp only [List.length_map]

theorem cutAt_count_ge (s : BufferState) (cut : ℕ) : s.layout.portCount ≤ (cutAt s cut).layout.portCount := by
  unfold cutAt
  split_ifs
  · change _ ≤ _ + _
    omega
  · exact le_rfl

private theorem cutAt_noInternal (s : BufferState) (cut : ℕ) (hs : NoInternalPairs s.layout) :
    NoInternalPairs (cutAt s cut).layout := by
  unfold cutAt
  split_ifs with hsafe
  · exact compile_noInternal ((safeTest_eq_true s.layout cut).mp hsafe) hs
  · exact hs

private theorem cutAt_noGateCrossing (s : BufferState) (cut : ℕ) (hs : s.layout.pages.Valid)
    (hprior : NoGateCrossingFrom s.layout (cut + 1)) : NoGateCrossingFrom (cutAt s cut).layout cut := by
  unfold cutAt
  split_ifs with hsafe
  · exact compile_noGateCrossing hs ((safeTest_eq_true s.layout cut).mp hsafe) hprior
  · intro a b hab ha hb k hk hak hkb
    have h := hprior a b hab ha hb k hk hak hkb
    by_contra hnot
    have he : k = cut := by omega
    subst k
    exact hsafe ((safeTest_eq_true s.layout cut).mpr hk)

/-- Execute a finite list of common cuts. -/
def scan (s : BufferState) (positions : List ℕ) : BufferState := positions.foldl cutAt s

theorem scan_length (s : BufferState) (positions : List ℕ) : (scan s positions).ports.length = s.ports.length := by
  induction positions generalizing s with
  | nil => rfl
  | cons cut rest ih => exact (ih (cutAt s cut)).trans (cutAt_length s cut)

private theorem scan_noInternal (s : BufferState) (positions : List ℕ) (hs : NoInternalPairs s.layout) :
    NoInternalPairs (scan s positions).layout := by
  induction positions generalizing s with
  | nil => exact hs
  | cons cut rest ih => exact ih (cutAt s cut) (cutAt_noInternal s cut hs)

private theorem scan_range_valid (s : BufferState) (n : ℕ) (hs : s.layout.pages.Valid)
    (hn : n ≤ s.layout.portCount) : (scan s (List.range n).reverse).layout.pages.Valid := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    have he : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by simp [List.range_succ]
    rw [he]
    have hc : n ≤ s.layout.portCount := by omega
    exact ih (cutAt s n) (cutAt_valid s n hs hc) (hc.trans (cutAt_count_ge s n))

private theorem scan_range_noGateCrossing (s : BufferState) (n : ℕ) (hs : s.layout.pages.Valid)
    (hn : n ≤ s.layout.portCount) (hprior : NoGateCrossingFrom s.layout n) :
    NoGateCrossingFrom (scan s (List.range n).reverse).layout 0 := by
  induction n generalizing s with
  | zero => exact hprior
  | succ n ih =>
    have he : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by simp [List.range_succ]
    rw [he]
    have hc : n ≤ s.layout.portCount := by omega
    exact ih (cutAt s n) (cutAt_valid s n hs hc) (hc.trans (cutAt_count_ge s n))
      (cutAt_noGateCrossing s n hs hprior)

private theorem ordinary_of_not_gatePort {l : PortLayout} (hl : PortInventory l) {i : ℕ}
    (hi : i < l.portCount) (hn : ¬GatePort l i) : Ordinary l i := by
  have hm := hl.lower.mem_iff.mpr (List.mem_range.mpr hi)
  obtain ⟨g, hg, hport⟩ := List.mem_flatMap.mp hm
  cases g with
  | wire a b =>
    refine ⟨a, b, hg, ?_⟩
    simpa only [groupPorts, List.mem_cons, List.not_mem_nil, or_false] using hport
  | gate kind first =>
    apply False.elim
    apply hn
    simp only [groupPorts, List.mem_cons, List.not_mem_nil, or_false] at hport
    exact ⟨kind, first, hg, by omega, by omega⟩

private theorem readerPartners_of_noGateCrossing {l : PortLayout} (hl : l.pages.Valid)
    (hclear : NoInternalPairs l) (hcross : NoGateCrossingFrom l 0) : ReaderPartners l := by
  constructor
  · intro a b hab hmid
    obtain ⟨kind, first, hg, rfl⟩ := hmid
    have hb := page_bound_mem hl.upper (List.mem_map.mpr ⟨(first + 1, b), hab, rfl⟩)
    change first + 1 < b ∧ b < l.portCount at hb
    apply Or.inr
    apply ordinary_of_not_gatePort (inventory_of_pages hl) hb.2
    intro hgate
    by_cases hlow : b < first + 3
    · have he : b = first + 2 := by omega
      subst b
      exact (hclear kind first hg).2 hab
    · have h := hcross (first + 1) b hab ⟨kind, first, hg, by omega, by omega⟩ hgate
        (first + 3) (gate_boundary_safe hl hg).2 (by omega) (by omega)
      omega
  · intro a b hab hmid
    obtain ⟨kind, first, hg, rfl⟩ := hmid
    have hb := page_bound_mem hl.upper (List.mem_map.mpr ⟨(a, first + 1), hab, rfl⟩)
    change a < first + 1 ∧ first + 1 < l.portCount at hb
    apply Or.inr
    apply ordinary_of_not_gatePort (inventory_of_pages hl) (by omega)
    intro hgate
    by_cases hlow : first ≤ a
    · have he : a = first := by omega
      subst a
      exact (hclear kind first hg).1 hab
    · have h := hcross a (first + 1) hab hgate ⟨kind, first, hg, by omega, by omega⟩
        first (gate_boundary_safe hl hg).1 (by omega) (by omega)
      omega

/-- First buffer same-gate pairs, then cut all safe original gaps from right to left. -/
def repair (l : PortLayout) : BufferState :=
  let s := bufferInternal l
  scan s (List.range s.layout.portCount).reverse

theorem repair_valid {l : PortLayout} (hl : l.pages.Valid) : (repair l).layout.pages.Valid :=
  scan_range_valid _ _ (bufferInternal_valid hl) le_rfl

private theorem repair_no_internal {l : PortLayout} (hl : l.pages.Valid) : NoInternalPairs
    (repair l).layout :=
  scan_noInternal _ _ (bufferInternal_no_internal hl)

/-- The actual emitted layout gives every gate-middle incidence an upper partner on an ordinary lower WIRE. -/
theorem repair_readerPartners {l : PortLayout} (hl : l.pages.Valid) : ReaderPartners (repair l).layout := by
  have hs := bufferInternal_valid hl
  have hprior : NoGateCrossingFrom (bufferInternal l).layout (bufferInternal l).layout.portCount := by
    intro a b hab _ _ cut _ _ hcb
    have hb := page_bound_mem hs.upper (List.mem_map.mpr ⟨(a, b), hab, rfl⟩)
    change a < b ∧ b < (bufferInternal l).layout.portCount at hb
    omega
  exact readerPartners_of_noGateCrossing (repair_valid hl) (repair_no_internal hl)
    (scan_range_noGateCrossing _ _ hs le_rfl hprior)

end PushPuzzle.Push.Partner.Cuts
