/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateSamples
public import Push.AcceptanceGatePublicSamples
public import Push.AcceptanceGateRailSigned
public import PushS.PortCanonicalSignals
import all PushS.PortGateShuttle
import all PushS.ShuttleMacroSegments
import all PushS.PortGateTrains
import all PushS.PortSegments

/-! The canonical physical target's signed shuttle bits and its seven nonzero actual samples. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

/-- Signed target bits read from the actual three canonical gate signal slots. -/
@[expose] def canonicalShuttleTarget (l : PortLayout) (target : List Bool) (g : Placement) : Shuttle.Target where
  heavy := (l.canonical target).internal.getD (g.internal + 1) false
  left := !((l.canonical target).internal.getD g.internal false)
  relay := (l.canonical target).internal.getD (g.internal + 2) false

/-- Native legal target inputs give the signed AND/OR readout legality conditions. -/
theorem canonicalShuttleTarget_legal (l : PortLayout) (target : List Bool) (hlegal : l.InputLegal target)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    (canonicalShuttleTarget l target g).Legal kind := by
  have hread := l.canonical_gate_read target hg hk
  have hin := hlegal.gate_inputs hg hk
  simp only [canonicalShuttleTarget, Shuttle.Target.Legal, hread.1, hread.2.1, hread.2.2]
  refine ⟨fun h => h, ?_⟩
  intro hand hheavy
  subst kind
  simp only [ite_true] at hin
  cases hr : target.getD g.right false <;> simp only [hr, Bool.not_false, Bool.not_true] at hheavy
  · cases hheavy
  · rcases hin with hn | ⟨hl, _⟩
    · simp only [hr] at hn
      cases hn
    · simp only [hl, Bool.not_false]

/-- A signed canonical target work-row hole is a hole of the actual emitted target bitmap. -/
theorem canonicalShuttleTarget_hole_target (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1) {x : ℤ}
    (hx : (q.1.val : ℤ) - p.x (g.left + 1) = x)
    (hhole : (canonicalShuttleTarget l target g).placement.hole kind x) : q ∈ targetHoles l p target := by
  have hx0 := readLength_add_lt_x p (g.left + 1) 0
  have hkpos : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  have hkcast : (kind.kappa.toNat : ℤ) = kind.kappa := by cases kind <;> decide +kernel
  have hcore : q ∈ ShuttleMacro.coreHoles p (l.canonical target) kind g.left g.internal := by
    rw [ShuttleMacro.coreHoles_mem]
    simp only [canonicalShuttleTarget, Shuttle.Target.placement, Shuttle.Placement.hole,
      Shuttle.Placement.leftGap, Shuttle.Placement.rightGap] at hhole
    cases hl : (l.canonical target).internal.getD g.internal false <;>
      cases hh : (l.canonical target).internal.getD (g.internal + 1) false <;>
      cases hr : (l.canonical target).internal.getD (g.internal + 2) false <;>
      simp only [hl, hh, hr, Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true,
        Bool.false_eq_true, ite_true, ite_false] at hhole ⊢ <;> omega
  change q ∈ SegmentRecipe.holes _ _ (l.encodedSegments p (l.canonical target))
  rw [gate_full_split l p (l.canonical target) hg hk]
  exact Finset.mem_union_right _ hcore

/-- All seven nonzero canonical shuttle samples are actual terminal work-row holes. -/
theorem canonical_gate_nonzero_sample_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1) {x : ℤ}
    (hx : (q.1.val : ℤ) - p.x (g.left + 1) = x) (hprobe : x ∈ Shuttle.probes) (hne : x ≠ 0)
    (hhole : (canonicalShuttleTarget l target g).placement.hole kind x) : q ∈ holes t := by
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have ht := canonicalShuttleTarget_hole_target l p target hg hk hy hx hhole
  have hx0 := readLength_add_lt_x p (g.left + 1) 0
  have hp : x = -2 ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 := by
    simp only [Shuttle.probes, Finset.mem_insert, Finset.mem_singleton] at hprobe
    omega
  rcases hp with hm2 | h2 | h4 | h6 | h8 | h10 | h12
  · apply canonical_gate_public_sample_terminal l p hl hM haxes initial target hgate hi hr accepted (hy := hy) (htarget := ht)
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl (by omega)
  · exact canonical_gate_independent_sample_terminal l p hl hM haxes initial target hgate hr accepted hi
      (Or.inl (by omega)) hy ht
  · exact canonical_gate_four_terminal l p hl hM haxes initial target hr accepted hi (by omega) hy
  · apply canonical_gate_public_sample_terminal l p hl hM haxes initial target hgate hi hr accepted (hy := hy) (htarget := ht)
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl (by omega))
  · apply canonical_gate_public_sample_terminal l p hl hM haxes initial target hgate hi hr accepted (hy := hy) (htarget := ht)
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact canonical_gate_independent_sample_terminal l p hl hM haxes initial target hgate hr accepted hi
      (Or.inr (by omega)) hy ht
  · apply canonical_gate_public_sample_terminal l p hl hM haxes initial target hgate hi hr accepted (hy := hy) (htarget := ht)
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr (by omega)))

end PushPuzzle.Push.AcceptanceSoundness
