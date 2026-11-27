/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPublic
public import Push.AcceptanceSoundnessWideSouth
import all Push.AcceptanceSoundnessSupportCoordinatesGuards
import all Push.AcceptanceSoundnessCentral
import all PushS.PortBackground
import all PushS.PortReaderFreeze
import all PushS.PortReaderMidpoints
import all PushS.PortEndpointLocality
import all PushS.PortSignalLocality
import all PushS.PortStreetEnumeration
import all PushS.PortSegments
import all PushS.Scales

/-! Actual ordinary midpoint columns are emitted guards and retain only their canonical target stock. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

/-- An ordinary f-axis midpoint column is an actual guard column, including conditional point rounding. -/
theorem endpoint_midpoint_guard (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    (EndpointStreet.f.column p e + p.x e.port) / 2 ∈ guards l p := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  let c := coordinates p
  let x := ((auxiliary c e).1 + c.x e.port) / 2
  let s := point x (onSide c e.side (readDepth p e.level))
  have hs : s ∈ endpointFixedSegments l c e := by
    simp only [endpointFixedSegments, List.mem_append]
    apply Or.inl ∘ Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨readDepth p e.level, (workingRows_level l p hj hjm).1, ?_⟩
    apply List.mem_append_left
    simp only [show readDepth p e.level ≤ c.depth e.level from le_rfl, ite_true, List.mem_singleton]
    rfl
  have hrow : s.start.2 ∈ streetRows c := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨e.level - 1, List.mem_range.mpr (by change e.level - 1 < p.levels; omega), ?_⟩
    have heq : e.level - 1 + 1 = e.level := by omega
    rw [heq]
    cases hside : e.side <;>
      simp [s, point, PortLayout.segment, onSide, c, coordinates, Coordinates.depth, readDepth, hside]
  have hK : 14 ≤ p.K e.level := by
    have hQ := Scales.Parameters.Q_ge p
    unfold Scales.Parameters.K
    omega
  have hsx : s.start.1 = x := by simp only [s, point, PortLayout.segment, min_self]
  have hfar : ∀ z ∈ streetColumns l c, 14 < Nat.dist s.start.1 z := by
    intro z hz
    have hb := street_column_midpoint_far l p hl hM haxes he hz
    change p.K e.level < Nat.dist z x at hb
    rw [hsx]
    change 14 < Nat.dist x z
    rw [Nat.dist_comm]
    omega
  apply List.mem_toFinset.mpr
  apply (guard_mem_iff l c (l.fixedSegments p) x).mpr
  refine ⟨s, l.endpointFixedSegments_mem_fixed p hl hM e he hs, ?_, hsx⟩
  refine ⟨rfl, ?_, List.contains_iff_mem.mpr hrow, ?_⟩
  · simp only [Bool.not_eq_true', Bool.eq_false_iff]
    intro hb
    have hf := hfar s.start.1 (List.contains_iff_mem.mp hb)
    rw [Nat.dist_self] at hf
    omega
  · exact List.all_eq_true.mpr (fun z hz => decide_eq_true (hfar z hz))

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout AcceptanceProgram

/-- The reader induction invariant, attached to one and the same actual accepted trajectory. -/
abbrev ReaderWalkInvariant (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (j : ℕ) (t : State (p.W + 1) (p.H + 1)) : Prop :=
  ∀ s, Reachable (l.canonicalInstance p hl hM haxes initial target).board none
    (l.canonicalInstance p hl hM haxes initial target).initial s →
    Reachable (l.canonicalInstance p hl hM haxes initial target).board none s t →
    l.readerWalkHoles p j ⊆ PushS.holes s

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

private theorem canonical_reader_between_of_reader {u v t : State (p.W + 1) (p.H + 1)} (j : ℕ)
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (huv : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hR : ReaderWalkInvariant l p hl hM haxes initial target j t) :
    Relation.ReflTransGen (ReaderStep l p j (l.canonicalInstance p hl hM haxes initial target).board) u v := by
  apply enrich_path huv
  intro a b hua hm hbv
  have hIa := hsu.trans hua
  have hbt := hbv.trans hvt
  exact ⟨⟨hm, hR b (hIa.tail hm) hbt⟩,
    canonical_player_on_original l p hl hM haxes initial target hIa
      ((Relation.ReflTransGen.single hm).trans hbt) ha,
    canonical_player_on_original l p hl hM haxes initial target (hIa.tail hm) hbt ha⟩

/-- The complete actual accepted stock on an ordinary midpoint column belongs to its canonical fixed target stock. -/
theorem canonical_midpoint_column_target_stock_of_reader (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hR : ReaderWalkInvariant l p hl hM haxes initial target e.level t)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2)
    (hq : q ∈ PushS.holes t) : q ∈ targetHoles l p target := by
  by_cases hwalk : q ∈ l.readerWalkHoles p e.level
  · exact l.readerWalkHoles_subset_encoded p hl hM e.level (l.canonical target) hwalk
  have hj := (l.endpoints_level_bounds p hl hM he).1
  have hbudget : (PushS.holes (l.canonicalInstance p hl hM haxes initial target).initial \
      l.readerWalkHoles p e.level).card ≤ p.K e.level := by
    rw [canonical_initial_holes l p hl hM haxes initial target]
    exact l.encodedSegments_outside_readerWalk_card_le p hl hM haxes (l.canonical initial) hj
  have hfar := l.endpoint_midpoint_readerExit_far p hl hM haxes he hx
  have hpath := canonical_reader_between_of_reader l p hl hM haxes initial target e.level .refl hr .refl ha hR
  have hsource := Radius.distant_hole_at_from_exits
    (R := ReaderStep l p e.level (l.canonicalInstance p hl hM haxes initial target).board)
    (fun {_ _} h => h.1) (fun {_ _} h hin hout => reader_step_exit l p hl hM h hin hout)
    .refl hpath (hR _ .refl hr)
    (Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target)) hwalk
    (fun a hae => hbudget.trans_lt (hfar a hae)) hq
  have henc : q ∈ targetHoles l p initial := by
    rw [← canonical_initial_holes l p hl hM haxes initial target]
    exact hsource
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp henc
  rcases List.mem_append.mp hs with hs | hs
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩
  · obtain ⟨i, hi, hnear⟩ := l.signalSegments_near_axis p hl (l.canonical initial)
      ((SegmentRecipe.mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    have hstreet := axis_in_streetColumns l p hi
    have hgap := street_column_midpoint_far l p hl hM haxes he hstreet
    have hK : 12 ≤ p.K e.level := by
      have hQ := Scales.Parameters.Q_ge p
      unfold Scales.Parameters.K
      omega
    change Nat.dist q.1.val (p.x i) ≤ 12 at hnear
    rw [← hx, Nat.dist_comm] at hgap
    omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
