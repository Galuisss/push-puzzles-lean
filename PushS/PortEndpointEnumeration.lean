/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointIndexing
import all PushS.PortEndpointIndexing
import all PushS.PortSegments
import all PushS.PortEndpointCrossing
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import Mathlib.Data.List.Nodup

/-! Enumeration of the actual physical endpoint keys. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PageLevels

private def outerPorts (g : Group) : List ℕ := [g.left, g.right]

private theorem outer_mem {g : Group} {k : ℕ} (hk : k ∈ outerPorts g) : k ∈ g.ports := by
  cases g <;> simp [outerPorts, Group.left, Group.right, Group.ports] at hk ⊢ <;> omega

private theorem groups_nodup (page : Page) (hp : page.Valid) : page.groups.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  change page.group i = page.group j at hij
  have hi : (page.group i).left ∈ (page.group i).ports := by
    cases page.group i <;> simp [Group.left, Group.ports]
  exact port_owner_unique page hp hi (by simpa only [hij] using hi)

private theorem page_parts_pairwise (page : Page) (hp : page.Valid) (f : Group → List ℕ)
    (hmem : ∀ g k, k ∈ f g → k ∈ g.ports) :
    page.groups.Pairwise (fun g h => List.Disjoint (f g) (f h)) := by
  refine List.Pairwise.imp_of_mem (fun {g h} hg hh hne => ?_) (groups_nodup page hp)
  apply List.disjoint_left.mpr
  intro k hkg hkh
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hh
  change page.group i = g at hi
  change page.group j = h at hj
  have hij := port_owner_unique page hp (by rw [hi]; exact hmem g k hkg)
    (by rw [hj]; exact hmem h k hkh)
  exact hne (hi.symm.trans (congrArg page.group hij) |>.trans hj)

private theorem outerPorts_nodup (page : Page) (hp : page.Valid) :
    (page.groups.flatMap outerPorts).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    have hb := hp.bounded i
    simp only [outerPorts, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, not_false_eq_true, and_true]
    exact Nat.ne_of_lt hb.1
  · exact page_parts_pairwise page hp outerPorts (fun _ _ hk => outer_mem hk)

private theorem flatMap_zipIdx_ignore {α β : Type} (xs : List α) (f : α → List β) :
    xs.zipIdx.flatMap (fun p => f p.1) = xs.flatMap f := by
  have h := congrArg (fun as : List α => as.flatMap f) (List.zipIdx_map_fst 0 xs)
  simpa only [List.flatMap_map, Function.comp_def] using h

private def placementKeys (g : Placement) : List (Side × ℕ) :=
  [(g.side, g.left), (g.side, g.right)]

private theorem endpoint_keys (l : PortLayout) :
    l.endpoints.map (fun e => (e.side, e.port)) = (placements l).flatMap placementKeys := by
  simp only [endpoints, List.map_flatMap]
  congr 1

private theorem page_keys (l : PortLayout) :
    (placements l).flatMap placementKeys =
      ((l.pages.upperPage.groups.flatMap outerPorts).map fun k => (Side.upper, k)) ++
      ((l.pages.lowerPage.groups.flatMap outerPorts).map fun k => (Side.lower, k)) := by
  simp only [placements, pages, Pages.upperPage, Pages.lowerPage, List.flatMap_append,
    List.flatMap_map, List.map_flatMap]
  apply congrArg₂ (· ++ ·)
  · rw [← flatMap_zipIdx_ignore l.upperPairs (fun a =>
      (outerPorts (.wire a.1 a.2)).map fun k => (Side.upper, k))]
    congr 1
  · rw [← flatMap_zipIdx_ignore l.lowerGroups (fun a =>
      (outerPorts a.shape).map fun k => (Side.lower, k))]
    congr 1
    funext a
    rcases a with ⟨g, i⟩
    cases g <;> simp [placementKeys, outerPorts, LowerGroup.shape, Group.left,
      Group.right, encLowerGroup_elim, encLowerGroup_toSum]

/-- The actual ordered endpoint enumeration has no repeated side/port key. -/
theorem endpoints_keys_nodup (l : PortLayout) (hl : l.pages.Valid) :
    (l.endpoints.map fun e => (e.side, e.port)).Nodup := by
  rw [endpoint_keys, page_keys]
  apply List.Nodup.append
  · exact (outerPorts_nodup l.pages.upperPage hl.upper).map
      (fun _ _ h => congrArg Prod.snd h)
  · exact (outerPorts_nodup l.pages.lowerPage hl.lower).map
      (fun _ _ h => congrArg Prod.snd h)
  · apply List.disjoint_left.mpr
    intro key hu hl
    obtain ⟨u, _, heU⟩ := List.mem_map.mp hu
    obtain ⟨v, _, heL⟩ := List.mem_map.mp hl
    have he : Side.upper = .lower := congrArg Prod.fst (heU.trans heL.symm)
    cases he

/-- The actual endpoint data are enumerated once each. -/
theorem endpoints_nodup (l : PortLayout) (hl : l.pages.Valid) : l.endpoints.Nodup :=
  List.Nodup.of_map (fun e => (e.side, e.port)) (l.endpoints_keys_nodup hl)

/-- Every port has its actual upper-page endpoint. -/
theorem endpoints_upper_exists (l : PortLayout) (hl : l.pages.Valid) {k : ℕ}
    (hk : k < l.portCount) : ∃ e ∈ l.endpoints, e.side = .upper ∧ e.port = k := by
  obtain ⟨i, hi, _⟩ := hl.upper.partition k hk
  have houter : k ∈ outerPorts (l.pages.upperPage.group i) := by
    obtain ⟨a, b, hg⟩ := hl.upper_wire i
    simpa [outerPorts, hg, Group.ports, Group.left, Group.right] using hi
  have hmem : k ∈ l.pages.upperPage.groups.flatMap outerPorts :=
    List.mem_flatMap.mpr ⟨l.pages.upperPage.group i, List.get_mem _ _, houter⟩
  have hkey : (Side.upper, k) ∈ l.endpoints.map (fun e => (e.side, e.port)) := by
    rw [endpoint_keys, page_keys]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k, hmem, rfl⟩)
  obtain ⟨e, he, hk⟩ := List.mem_map.mp hkey
  exact ⟨e, he, congrArg Prod.fst hk, congrArg Prod.snd hk⟩

private theorem lower_endpoint_of_outer (l : PortLayout) {k : ℕ}
    (hk : k ∈ l.pages.lowerPage.groups.flatMap outerPorts) :
    ∃ e ∈ l.endpoints, e.side = .lower ∧ e.port = k := by
  have hkey : (Side.lower, k) ∈ l.endpoints.map (fun e => (e.side, e.port)) := by
    rw [endpoint_keys, page_keys]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  obtain ⟨e, he, hk⟩ := List.mem_map.mp hkey
  exact ⟨e, he, congrArg Prod.fst hk, congrArg Prod.snd hk⟩

/-- Every lower-page port is an actual ordinary endpoint or the actual middle of a gate. -/
theorem endpoints_lower_or_gate (l : PortLayout) (hl : l.pages.Valid) {k : ℕ}
    (hk : k < l.portCount) :
    (∃ e ∈ l.endpoints, e.side = .lower ∧ e.port = k) ∨
      ∃ kind first, .gate kind first ∈ l.lowerGroups ∧ k = first + 1 := by
  obtain ⟨i, hi, _⟩ := hl.lower.partition k hk
  have hmem := List.get_mem l.pages.lowerPage.groups i
  change l.pages.lowerPage.group i ∈ l.pages.lowerPage.groups at hmem
  cases hg : l.pages.lowerPage.group i with
  | wire a b =>
    left
    apply lower_endpoint_of_outer l
    apply List.mem_flatMap.mpr
    refine ⟨l.pages.lowerPage.group i, hmem, ?_⟩
    simpa [outerPorts, hg, Group.ports, Group.left, Group.right] using hi
  | triple a =>
    by_cases hm : k = a + 1
    · right
      rw [hg] at hmem
      change Group.triple a ∈ l.lowerGroups.map LowerGroup.shape at hmem
      obtain ⟨g, hg, hshape⟩ := List.mem_map.mp hmem
      cases g with
      | wire x y => simp [LowerGroup.shape] at hshape
      | gate kind first =>
        have he : first = a := by simpa [LowerGroup.shape] using hshape
        subst first
        exact ⟨kind, a, hg, hm⟩
    · left
      apply lower_endpoint_of_outer l
      apply List.mem_flatMap.mpr
      refine ⟨l.pages.lowerPage.group i, hmem, ?_⟩
      simp [outerPorts, hg, Group.ports, Group.left, Group.right] at hi ⊢
      omega

private theorem signal_span (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ SegmentRecipe.pointHoles (endpointSegments (coordinates p) state e)) :
    p.x e.port - 2 ≤ q.1 ∧ q.1 ≤ p.x e.port + 2 := by
  have hn := endpoint_near p state e hq
  change (coordinates p).x e.port - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x e.port + 2
  cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at hn <;> omega

private theorem signals_disjoint_port (p : Scales.Parameters) (state : SignalState)
    (e f : Endpoint) (hp : e.port ≠ f.port) :
    Disjoint (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state e))
      (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state f)) := by
  apply Finset.disjoint_left.mpr
  intro q he hf
  have hE := signal_span p state e he
  have hF := signal_span p state f hf
  rcases lt_or_gt_of_ne hp with hp | hp
  · have hx := axes_separated p hp
    omega
  · have hx := axes_separated p hp
    omega

private theorem signals_disjoint_side (p : Scales.Parameters) (state : SignalState)
    (e f : Endpoint) (hs : e.side ≠ f.side) :
    Disjoint (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state e))
      (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state f)) := by
  apply Finset.disjoint_left.mpr
  intro q he hf
  have hE := signal_endpoint_page p state e he
  have hF := signal_endpoint_page p state f hf
  cases hse : e.side <;> cases hsf : f.side <;> simp [hse, hsf] at hs hE hF <;> omega

/-- Distinct positions in the actual endpoint enumeration have disjoint signal-hole unions. -/
theorem endpoints_signals_pairwise (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) : l.endpoints.Pairwise fun e f =>
      Disjoint (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state e))
        (SegmentRecipe.pointHoles (endpointSegments (coordinates p) state f)) := by
  refine List.Pairwise.imp_of_mem (fun {e f} he hf hne => ?_) (l.endpoints_nodup hl)
  by_cases hp : e.port = f.port
  · by_cases hs : e.side = f.side
    · exact (hne (l.endpoints_key_injective hl he hf hs hp)).elim
    · exact signals_disjoint_side p state e f hs
  · exact signals_disjoint_port p state e f hp

private theorem pointHoles_flatMap_card {α : Type} {xs : List α}
    {f : α → List PushFS.Reduction.Segment}
    (hp : xs.Pairwise fun a b => Disjoint (SegmentRecipe.pointHoles (f a))
      (SegmentRecipe.pointHoles (f b))) :
    (SegmentRecipe.pointHoles (xs.flatMap f)).card =
      (xs.map fun a => (SegmentRecipe.pointHoles (f a)).card).sum := by
  induction hp with
  | nil => simp [SegmentRecipe.pointHoles]
  | @cons a xs hdis hrest ih =>
    have hd : Disjoint (SegmentRecipe.pointHoles (f a))
        (SegmentRecipe.pointHoles (xs.flatMap f)) := by
      apply Finset.disjoint_left.mpr
      intro q ha hxs
      obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_pointHoles _ q).mp hxs
      obtain ⟨b, hb, hs⟩ := List.mem_flatMap.mp hs
      exact Finset.disjoint_left.mp (hdis b hb) ha
        ((SegmentRecipe.mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)
    simp only [List.flatMap_cons, SegmentRecipe.pointHoles_append,
      Finset.card_union_of_disjoint hd, List.map_cons, List.sum_cons, ih]

/-- Exact cardinality of the full actual endpoint-signal flatMap, counted once per physical hole. -/
theorem endpointsSignals_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    (SegmentRecipe.pointHoles (l.endpoints.flatMap (endpointSegments (coordinates p) state))).card =
      (l.endpoints.map fun e => 3 +
        (if e.side = .upper then state.axes.getD e.port false else !(state.axes.getD e.port false)).toNat +
        (if e.inward then state.internal.getD e.internal false
          else !(state.internal.getD e.internal false)).toNat).sum := by
  rw [pointHoles_flatMap_card (l.endpoints_signals_pairwise p hl state)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have hj := l.endpoints_level_bounds p hl hM he
  exact endpointSegments_card p state e hj.1 hj.2

end PushPuzzle.PushS.PortLayout
