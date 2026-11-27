/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsUpperValidity
import all Push.PartnerCutsUpperValidity
import all Push.PartnerInventory
import all Push.PartnerUpperValidity

/-! Exact gate and surviving old-arc readout through a common-cut block. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

private theorem mapPair_injective (cut count : ℕ) : Function.Injective (mapPair cut count) := by
  intro a b he
  exact Prod.ext (shift_injective cut count (congrArg Prod.fst he))
    (shift_injective cut count (congrArg Prod.snd he))

/-- Every old-to-old arc in the literal output is an untouched passive original arc. -/
theorem compile_old_pair_mem (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) :
    mapPair cut (active l cut).length ab ∈ (compile l cut).upperPairs ↔ ab ∈ passive l cut := by
  simp only [compile, List.mem_append]
  constructor
  · rintro (hnew | hold)
    · obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hnew
      have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      simp only [upperPiece, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with he | he
      · have hh := congrArg Prod.snd he
        have hf := left_bounds (cut := cut) hj
        exact (shift_ne_fresh cut _ ab.2 ⟨hf.1, by omega⟩ hh).elim
      · have hh := congrArg Prod.fst he
        have hf := right_bounds (cut := cut) hj
        exact (shift_ne_fresh cut _ ab.1 ⟨by omega, hf.2⟩ hh).elim
    · obtain ⟨old, hold, he⟩ := List.mem_map.mp hold
      exact mapPair_injective cut _ he ▸ hold
  · intro hm
    exact Or.inr (List.mem_map.mpr ⟨ab, hm, rfl⟩)

theorem compile_gate_mem (l : PortLayout) (cut : ℕ) (kind : Shuttle.Kind) (first : ℕ) :
    LowerGroup.gate kind first ∈ (compile l cut).lowerGroups ↔
      ∃ old, LowerGroup.gate kind old ∈ l.lowerGroups ∧ first = shift cut (active l cut).length old := by
  simp only [compile, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨g, hg, he⟩ | ⟨p, _, he⟩)
    · cases g with
      | wire a b => cases he
      | gate other old =>
        simp only [mapGroup, LowerGroup.gate.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        exact ⟨old, hg, rfl⟩
    · cases he
  · rintro ⟨old, hg, rfl⟩
    exact Or.inl ⟨.gate kind old, hg, rfl⟩

private def GatePort (l : PortLayout) (i : ℕ) : Prop :=
  ∃ kind first, LowerGroup.gate kind first ∈ l.lowerGroups ∧ first ≤ i ∧ i ≤ first + 2

private theorem gatePort_project {l : PortLayout} {cut : ℕ} (hs : SafeCut l cut) {i : ℕ}
    (hi : GatePort (compile l cut) i) :
    ∃ old, GatePort l old ∧ i = shift cut (active l cut).length old := by
  obtain ⟨kind, first, hg, hlo, hhi⟩ := hi
  obtain ⟨old, hgate, rfl⟩ := (compile_gate_mem l cut kind first).mp hg
  obtain ⟨h₁, h₂⟩ := shift_gate (count := (active l cut).length) (hs kind old hgate)
  have he : i = shift cut (active l cut).length old ∨
      i = shift cut (active l cut).length old + 1 ∨ i = shift cut (active l cut).length old + 2 := by omega
  rcases he with he | he | he
  · exact ⟨old, ⟨kind, old, hgate, le_rfl, by omega⟩, he⟩
  · exact ⟨old + 1, ⟨kind, old, hgate, by omega, by omega⟩, he.trans h₁.symm⟩
  · exact ⟨old + 2, ⟨kind, old, hgate, by omega, le_rfl⟩, he.trans h₂.symm⟩

private theorem compile_gatePair_project {l : PortLayout} {cut : ℕ} (hs : SafeCut l cut)
    {a b : ℕ} (hab : (a, b) ∈ (compile l cut).upperPairs)
    (ha : GatePort (compile l cut) a) (hb : GatePort (compile l cut) b) :
    ∃ x y, (x, y) ∈ passive l cut ∧ GatePort l x ∧ GatePort l y ∧
      a = shift cut (active l cut).length x ∧ b = shift cut (active l cut).length y := by
  obtain ⟨x, hx, rfl⟩ := gatePort_project hs ha
  obtain ⟨y, hy, rfl⟩ := gatePort_project hs hb
  exact ⟨x, y, (compile_old_pair_mem l cut (x, y)).mp hab, hx, hy, rfl, rfl⟩

/-- Safe old gates remain whole when a right-side safe boundary is projected across the inserted block. -/
private theorem safeCut_project_right {l : PortLayout} {cut k : ℕ} (hs : SafeCut l cut)
    (hk : SafeCut (compile l cut) k) (hbound : cut + 2 * (active l cut).length ≤ k) :
    SafeCut l (k - 2 * (active l cut).length) := by
  intro kind first hg
  have hnew := (compile_gate_mem l cut kind (shift cut (active l cut).length first)).mpr ⟨first, hg, rfl⟩
  have hsnew := hk kind _ hnew
  have hsold := hs kind first hg
  unfold shift at hsnew
  split_ifs at hsnew <;> omega

private def NoGateCrossingFrom (l : PortLayout) (bound : ℕ) : Prop :=
  ∀ a b, (a, b) ∈ l.upperPairs → GatePort l a → GatePort l b →
    ∀ cut, SafeCut l cut → a < cut → cut ≤ b → cut < bound

/-- Cutting the current safe boundary removes every gate-to-gate arc crossing it. -/
private theorem compile_noGateCrossing {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hs : SafeCut l cut) (hprior : NoGateCrossingFrom l (cut + 1)) :
    NoGateCrossingFrom (compile l cut) cut := by
  intro a b hab ha hb k hk hak hkb
  obtain ⟨x, y, hpassive, hx, hy, rfl, rfl⟩ := compile_gatePair_project hs hab ha hb
  obtain ⟨hxy, hnot⟩ := (mem_passive l cut (x, y)).mp hpassive
  have hbound := page_bound_mem hl.upper (List.mem_map.mpr ⟨(x, y), hxy, rfl⟩)
  change x < y ∧ y < l.portCount at hbound
  by_contra hkn
  have hge : cut ≤ k := by omega
  have hright : cut ≤ x := by
    unfold shift at hak hkb
    split_ifs at hak hkb <;> omega
  have hyright : ¬y < cut := by omega
  have hxright : ¬x < cut := by omega
  simp only [shift, ite_eq_right hxright, ite_eq_right hyright] at hak hkb
  have hkbnd : cut + 2 * (active l cut).length ≤ k := by omega
  have hsafe := safeCut_project_right hs hk hkbnd
  have h := hprior x y hxy hx hy _ hsafe (by omega) (by omega)
  omega

private theorem compile_noInternal {l : PortLayout} {cut : ℕ} (hs : SafeCut l cut)
    (hclear : NoInternalPairs l) : NoInternalPairs (compile l cut) := by
  intro kind first hg
  obtain ⟨old, hold, rfl⟩ := (compile_gate_mem l cut kind first).mp hg
  obtain ⟨h₁, h₂⟩ := shift_gate (count := (active l cut).length) (hs kind old hold)
  have hclearOld := hclear kind old hold
  constructor
  · intro hm
    have he : (shift cut (active l cut).length old, shift cut (active l cut).length old + 1) =
        mapPair cut (active l cut).length (old, old + 1) := by simp only [mapPair, h₁]
    rw [he, compile_old_pair_mem] at hm
    exact hclearOld.1 ((mem_passive l cut _).mp hm).1
  · intro hm
    have he : (shift cut (active l cut).length old + 1, shift cut (active l cut).length old + 2) =
        mapPair cut (active l cut).length (old + 1, old + 2) := by simp only [mapPair, h₁, h₂]
    rw [he, compile_old_pair_mem] at hm
    exact hclearOld.2 ((mem_passive l cut _).mp hm).1

end PushPuzzle.Push.Partner.Cuts
