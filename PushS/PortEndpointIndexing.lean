/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointCrossing
import all PushS.PortSegments

/-! The actual page-group owners of the emitted endpoint indices. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PageLevels

private theorem endpoint_ext {e f : Endpoint} (hs : e.side = f.side) (hp : e.port = f.port)
    (hi : e.inward = f.inward) (hl : e.level = f.level) (hh : e.internal = f.internal) : e = f := by
  cases e
  cases f
  simp_all

private theorem upper_group_at (l : PortLayout) {a b i : ℕ}
    (hi : ((a, b), i) ∈ l.upperPairs.zipIdx) :
    l.pages.upperPage.group ⟨i, by
      simpa [pages, Pages.upperPage] using List.snd_lt_of_mem_zipIdx hi⟩ = .wire a b := by
  have hr := List.fst_eq_of_mem_zipIdx hi
  simp only [Nat.sub_zero] at hr
  change (l.upperPairs.map fun ab => Group.wire ab.1 ab.2)[i]'(by
    simpa only [List.length_map, Nat.add_zero] using List.snd_lt_of_mem_zipIdx hi) = .wire a b
  rw [List.getElem_map, ← hr]

private theorem lower_group_at (l : PortLayout) {g : LowerGroup} {i : ℕ}
    (hi : (g, i) ∈ l.lowerGroups.zipIdx) :
    l.pages.lowerPage.group ⟨i, by
      simpa [pages, Pages.lowerPage] using List.snd_lt_of_mem_zipIdx hi⟩ = g.shape := by
  have hr := List.fst_eq_of_mem_zipIdx hi
  simp only [Nat.sub_zero] at hr
  change (l.lowerGroups.map LowerGroup.shape)[i]'(by
    simpa only [List.length_map, Nat.add_zero] using List.snd_lt_of_mem_zipIdx hi) = g.shape
  rw [List.getElem_map, ← hr]

private theorem endpoint_side_of_mem {g : Placement} {e : Endpoint}
    (he : e ∈ [⟨g.side, g.left, true, g.level, g.internal⟩,
      ⟨g.side, g.right, false, g.level, g.internal + if g.gate.isSome then 2 else 0⟩]) :
    e.side = g.side := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

private theorem upper_endpoint_owner (l : PortLayout) (hl : l.pages.Valid) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .upper) :
    ∃ i : l.pages.upperPage.Index,
      e.port ∈ (l.pages.upperPage.group i).ports ∧
      (e.port = (l.pages.upperPage.group i).left ∨ e.port = (l.pages.upperPage.group i).right) ∧
      e.inward = decide (e.port = (l.pages.upperPage.group i).left) ∧
      e.level = l.upperLevel i ∧ e.internal = i := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  have hside := endpoint_side_of_mem (g := g) he
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · let j : l.pages.upperPage.Index := ⟨i, by
      simpa [pages, Pages.upperPage] using List.snd_lt_of_mem_zipIdx hi⟩
    have hj : l.pages.upperPage.group j = .wire a b := upper_group_at l hi
    have hb := hl.upper.bounded j
    simp only [hj, Group.left, Group.right] at hb
    refine ⟨j, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp [hj, Group.ports, Group.left, Group.right, j]
    · have hne : b ≠ a := by omega
      simp [hj, Group.ports, Group.left, Group.right, j, hne]
  · have hgside : (encLowerGroup_elim lower
        (fun ab => (⟨.lower, ab.1, ab.2, l.lowerLevel i, l.lowerOffset i, none⟩ : Placement))
        (fun ka => ⟨.lower, ka.2, ka.2 + 2, l.lowerLevel i, l.lowerOffset i, some ka.1⟩)).side = .lower := by
      cases lower <;> simp [encLowerGroup_elim, encLowerGroup_toSum]
    have hc := hgside.symm.trans (hside.symm.trans hs)
    cases hc

private theorem lower_endpoint_owner (l : PortLayout) (hl : l.pages.Valid) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .lower) :
    ∃ i : l.pages.lowerPage.Index,
      e.port ∈ (l.pages.lowerPage.group i).ports ∧
      (e.port = (l.pages.lowerPage.group i).left ∨ e.port = (l.pages.lowerPage.group i).right) ∧
      e.inward = decide (e.port = (l.pages.lowerPage.group i).left) ∧
      e.level = l.lowerLevel i ∧
      e.internal = l.lowerOffset i + if e.inward then 0 else
        2 * (l.pages.lowerPage.group i).middles.card := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  have hside := endpoint_side_of_mem (g := g) he
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · have hc : Side.upper = .lower := hside.symm.trans hs
    cases hc
  · let j : l.pages.lowerPage.Index := ⟨i, by
      simpa [pages, Pages.lowerPage] using List.snd_lt_of_mem_zipIdx hi⟩
    have hj : l.pages.lowerPage.group j = lower.shape := lower_group_at l hi
    have hb := hl.lower.bounded j
    simp only [hj] at hb
    refine ⟨j, ?_⟩
    cases lower with
    | wire a b =>
      simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl] at he
      simp only [LowerGroup.shape, Group.left, Group.right] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp [hj, LowerGroup.shape, Group.ports, Group.left, Group.right, j]
      · have hne : b ≠ a := by omega
        simp [hj, LowerGroup.shape, Group.ports, Group.left, Group.right, Group.middles, j, hne]
    | gate kind a =>
      simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;>
        simp [hj, LowerGroup.shape, Group.ports, Group.left, Group.right, Group.middles, j]

private theorem port_bound (page : Page) (hp : page.Valid) (i : page.Index) {k : ℕ}
    (hk : k ∈ (page.group i).ports) : k < page.portCount := by
  have hb := hp.bounded i
  cases hg : page.group i <;> simp [hg, Group.ports, Group.left, Group.right] at hk hb <;> omega

private theorem port_owner_unique (page : Page) (hp : page.Valid) {i j : page.Index} {k : ℕ}
    (hi : k ∈ (page.group i).ports) (hj : k ∈ (page.group j).ports) : i = j :=
  (hp.partition k (port_bound page hp i hi)).unique hi hj

/-- The actual endpoint page and port determine all its physical data. -/
theorem endpoints_key_injective (l : PortLayout) (hl : l.pages.Valid) {e f : Endpoint}
    (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints) (hs : e.side = f.side) (hp : e.port = f.port) :
    e = f := by
  cases hside : e.side with
  | upper =>
    obtain ⟨i, hi, _, hei, hel, heh⟩ := upper_endpoint_owner l hl he hside
    obtain ⟨j, hj, _, hfi, hfl, hfh⟩ := upper_endpoint_owner l hl hf (hs.symm.trans hside)
    rw [hp] at hi
    have hij := port_owner_unique l.pages.upperPage hl.upper hi hj
    subst j
    have hin : e.inward = f.inward := by rw [hei, hfi, hp]
    exact endpoint_ext hs hp hin (hel.trans hfl.symm) (heh.trans hfh.symm)
  | lower =>
    obtain ⟨i, hi, _, hei, hel, heh⟩ := lower_endpoint_owner l hl he hside
    obtain ⟨j, hj, _, hfi, hfl, hfh⟩ := lower_endpoint_owner l hl hf (hs.symm.trans hside)
    rw [hp] at hi
    have hij := port_owner_unique l.pages.lowerPage hl.lower hi hj
    subst j
    have hin : e.inward = f.inward := by rw [hei, hfi, hp]
    apply endpoint_ext hs hp hin (hel.trans hfl.symm)
    rw [heh, hfh, hin]

/-- Every actual endpoint fixed piece is disjoint from every actual endpoint signal piece. -/
theorem endpoints_fixed_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) {fixed signal : Endpoint}
    (hf : fixed ∈ l.endpoints) (hs : signal ∈ l.endpoints) :
    Disjoint (SegmentRecipe.pointHoles (endpointFixedSegments l (coordinates p) fixed))
      (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state signal)) := by
  by_cases hp : fixed.port = signal.port
  · by_cases hside : fixed.side = signal.side
    · have heq := l.endpoints_key_injective hl hf hs hside hp
      subst signal
      have hj := l.endpoints_level_bounds p hl hM hf
      exact endpointFixedSegments_disjoint l p state fixed hj.1 hj.2
    · exact endpointFixedSegments_disjoint_of_side_ne l p state fixed signal hside
  · exact endpointFixedSegments_disjoint_of_port_ne l p state fixed signal hp

/-- The two actual endpoint flatMaps in the fixed and signal emitters have disjoint hole unions. -/
theorem endpointsFixed_disjoint_endpointsSignals (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    Disjoint (SegmentRecipe.pointHoles (l.endpoints.flatMap (endpointFixedSegments l (coordinates p))))
      (SegmentRecipe.pointHoles (l.endpoints.flatMap (endpointSegments (coordinates p) state))) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  obtain ⟨sf, hsf, hqf⟩ := (SegmentRecipe.mem_pointHoles _ q).mp hfixed
  obtain ⟨ss, hss, hqs⟩ := (SegmentRecipe.mem_pointHoles _ q).mp hsignal
  obtain ⟨fixed, hf, hsf⟩ := List.mem_flatMap.mp hsf
  obtain ⟨signal, hs, hss⟩ := List.mem_flatMap.mp hss
  have hd := l.endpoints_fixed_disjoint p hl hM state hf hs
  exact Finset.disjoint_left.mp hd
    ((SegmentRecipe.mem_pointHoles _ q).mpr ⟨sf, hsf, hqf⟩)
    ((SegmentRecipe.mem_pointHoles _ q).mpr ⟨ss, hss, hqs⟩)

/-- A lower gate's actual middle port is never an ordinary lower endpoint. -/
theorem endpoints_lower_ne_gate_middle (l : PortLayout) (hl : l.pages.Valid)
    {kind : Shuttle.Kind} {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .lower) : e.port ≠ first + 1 := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  let j : l.pages.lowerPage.Index := ⟨i, by
    simp [pages, Pages.lowerPage]⟩
  have hj : l.pages.lowerPage.group j = .triple first := by
    change (l.lowerGroups.map LowerGroup.shape)[i.val]'(by
      simpa only [List.length_map] using i.isLt) = .triple first
    rw [List.getElem_map]
    change (l.lowerGroups.get i).shape = .triple first
    rw [hi]
    rfl
  obtain ⟨k, hk, hout, _, _, _⟩ := lower_endpoint_owner l hl he hs
  intro hport
  rw [hport] at hk hout
  have hm : first + 1 ∈ (l.pages.lowerPage.group j).ports := by simp [hj, Group.ports]
  have hkj := port_owner_unique l.pages.lowerPage hl.lower hk hm
  subst k
  simp only [hj, Group.left, Group.right] at hout
  omega

/-- Every actual endpoint port is within the supplied page partition. -/
theorem endpoints_port_lt (l : PortLayout) (hl : l.pages.Valid) {e : Endpoint}
    (he : e ∈ l.endpoints) : e.port < l.portCount := by
  cases hs : e.side with
  | upper =>
    obtain ⟨i, hi, _, _, _, _⟩ := upper_endpoint_owner l hl he hs
    exact port_bound l.pages.upperPage hl.upper i hi
  | lower =>
    obtain ⟨i, hi, _, _, _, _⟩ := lower_endpoint_owner l hl he hs
    exact port_bound l.pages.lowerPage hl.lower i hi

end PushPuzzle.PushS.PortLayout
