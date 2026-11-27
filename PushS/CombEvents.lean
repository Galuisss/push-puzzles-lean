/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombIntersection
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
import Mathlib.Data.List.Sigma
import Mathlib.Data.List.GetD

/-! Literal comb-crossing records retain their original edge, segment, and tooth identities. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal Turing.MultiTapeTM

/-- A genuine segment/tooth encounter, before sorting or contour-port numbering. -/
@[ext] structure Crossing where
  /-- Position in the original route array. -/
  edge : ℕ
  /-- Position in that original route's consecutive-segment list. -/
  segment : ℕ
  /-- Position of the original vertex whose tooth is crossed. -/
  vertex : ℕ
  /-- The computed integer height on the prepared tooth. -/
  height : ℤ
  /-- The original route traverses the prepared segment towards larger columns. -/
  forward : Bool
  deriving DecidableEq

/-- Native list-position encodings and the standard signed-binary intersection height. -/
enc_structure encCrossing : Crossing where
  edge : encUnary, segment : encUnary, vertex : encUnary, height : encIntBin, forward : encBool

/-- Test and emit the actual strict interior crossing below one vertex tip. -/
@[expose] def crossingAt (edge segment vertex : ℕ) (a b site : Point) : Option Crossing :=
  let height := cutHeight a b site.1
  if ((a.1 < site.1 ∧ site.1 < b.1) ∨ (b.1 < site.1 ∧ site.1 < a.1)) ∧ height < site.2 then
    some ⟨edge, segment, vertex, height, decide (a.1 < b.1)⟩
  else none

/-- Scan the same prepared route and vertex arrays, retaining every actual source position. -/
@[expose] def crossings (width : ℕ) (d : Graph.OrthogonalDrawing) : List Crossing :=
  let prepared := prepare width d
  prepared.2.zipIdx.flatMap fun re =>
    re.1.consecutivePairs.zipIdx.flatMap fun abj =>
      prepared.1.zipIdx.filterMap fun sv =>
        crossingAt re.2 abj.2 sv.2 abj.1.1 abj.1.2 sv.1

/-- The scanner emits precisely the closed record with these source identities and strict tests. -/
private theorem crossingAt_eq_some_iff (edge segment vertex : ℕ) (a b site : Point) (c : Crossing) :
    crossingAt edge segment vertex a b site = some c ↔
      (((a.1 < site.1 ∧ site.1 < b.1) ∨ (b.1 < site.1 ∧ site.1 < a.1)) ∧ cutHeight a b site.1 < site.2) ∧
        c = ⟨edge, segment, vertex, cutHeight a b site.1, decide (a.1 < b.1)⟩ := by
  dsimp only [crossingAt]
  split_ifs <;> simp_all [eq_comm]

/-- Every emitted record reads its exact original route, segment, and vertex positions. -/
theorem mem_crossings_iff (width : ℕ) (d : Graph.OrthogonalDrawing) (c : Crossing) :
    c ∈ crossings width d ↔ ∃ r ab site,
      (prepare width d).2[c.edge]? = some r ∧
      r.consecutivePairs[c.segment]? = some ab ∧
      (prepare width d).1[c.vertex]? = some site ∧
      (((ab.1.1 < site.1 ∧ site.1 < ab.2.1) ∨ (ab.2.1 < site.1 ∧ site.1 < ab.1.1)) ∧
        cutHeight ab.1 ab.2 site.1 < site.2) ∧
      c.height = cutHeight ab.1 ab.2 site.1 ∧ c.forward = decide (ab.1.1 < ab.2.1) := by
  constructor
  · intro hc
    obtain ⟨⟨r, edge⟩, hr, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨ab, segIndex⟩, hs, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨site, vertex⟩, hv, hc⟩ := List.mem_filterMap.mp hc
    obtain ⟨htest, rfl⟩ := (crossingAt_eq_some_iff _ _ _ _ _ _ _).mp hc
    exact ⟨r, ab, site, List.mem_zipIdx_iff_getElem?.mp hr,
      List.mem_zipIdx_iff_getElem?.mp hs, List.mem_zipIdx_iff_getElem?.mp hv, htest, rfl, rfl⟩
  · rintro ⟨r, ab, site, hr, hs, hv, htest, hh, hf⟩
    apply List.mem_flatMap.mpr
    refine ⟨(r, c.edge), List.mem_zipIdx_iff_getElem?.mpr hr, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨(ab, c.segment), List.mem_zipIdx_iff_getElem?.mpr hs, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨(site, c.vertex), List.mem_zipIdx_iff_getElem?.mpr hv, ?_⟩
    apply (crossingAt_eq_some_iff _ _ _ _ _ _ _).mpr
    exact ⟨htest, Crossing.ext rfl rfl rfl hh hf⟩

private theorem crossingAt_fields {edge slot vertex : ℕ} {a b site : Point} {c : Crossing}
    (h : crossingAt edge slot vertex a b site = some c) :
    c.edge = edge ∧ c.segment = slot ∧ c.vertex = vertex := by
  obtain ⟨_, rfl⟩ := (crossingAt_eq_some_iff _ _ _ _ _ _ _).mp h
  exact ⟨rfl, rfl, rfl⟩

private theorem indexed_flatMap_nodup {α β : Type} (xs : List α)
    (f : α × ℕ → List β) (key : β → ℕ)
    (hchild : ∀ x ∈ xs.zipIdx, (f x).Nodup)
    (hkey : ∀ x ∈ xs.zipIdx, ∀ b ∈ f x, key b = x.2) :
    (xs.zipIdx.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hchild, ?_⟩
  have hindices : xs.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := by
    simpa only [List.Nodup, List.pairwise_map] using List.nodup_zipIdx_map_snd xs
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hne => ?_) hindices
  apply List.disjoint_left.mpr
  intro c hca hcb
  exact hne ((hkey a ha c hca).symm.trans (hkey b hb c hcb))

private theorem sites_scan_nodup (edge slot : ℕ) (a b : Point) (sites : List Point) :
    (sites.zipIdx.filterMap fun sv => crossingAt edge slot sv.2 a b sv.1).Nodup := by
  rw [List.filterMap_eq_flatMap_toList]
  apply indexed_flatMap_nodup sites _ Crossing.vertex
  · intro sv _
    cases crossingAt edge slot sv.2 a b sv.1 <;> simp
  · intro sv _ c hc
    have h := (Option.mem_toList.mp hc)
    exact (crossingAt_fields h).2.2

/-- Each source edge/segment/tooth triple emits at most one occurrence in the actual scan. -/
theorem crossings_nodup (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (crossings width d).Nodup := by
  unfold crossings
  apply indexed_flatMap_nodup _ _ Crossing.edge
  · intro re _
    apply indexed_flatMap_nodup _ _ Crossing.segment
    · intro abj _
      exact sites_scan_nodup re.2 abj.2 abj.1.1 abj.1.2 _
    · intro abj _ c hc
      obtain ⟨sv, _, hc⟩ := List.mem_filterMap.mp hc
      exact (crossingAt_fields hc).2.1
  · intro re _ c hc
    obtain ⟨abj, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨sv, _, hc⟩ := List.mem_filterMap.mp hc
    exact (crossingAt_fields hc).1

/-- The original edge/segment/tooth identity determines the complete emitted record. -/
theorem crossings_key_injective (width : ℕ) (d : Graph.OrthogonalDrawing)
    {c c' : Crossing} (hc : c ∈ crossings width d) (hc' : c' ∈ crossings width d)
    (he : c.edge = c'.edge) (hs : c.segment = c'.segment) (hv : c.vertex = c'.vertex) : c = c' := by
  obtain ⟨r, ab, site, hr, hab, hsite, _, hh, hf⟩ := (mem_crossings_iff width d c).mp hc
  obtain ⟨r', ab', site', hr', hab', hsite', _, hh', hf'⟩ := (mem_crossings_iff width d c').mp hc'
  rw [← he] at hr'
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  rw [← hs] at hab'
  have habb : ab = ab' := Option.some.inj (hab.symm.trans hab')
  subst ab'
  rw [← hv] at hsite'
  have hss : site = site' := Option.some.inj (hsite.symm.trans hsite')
  subst site'
  exact Crossing.ext he hs hv (hh.trans hh'.symm) (hf.trans hf'.symm)

/-- Source incidence identities are retained without repeated occurrence in the table. -/
theorem crossings_keys_nodup (width : ℕ) (d : Graph.OrthogonalDrawing) :
    ((crossings width d).map fun c => (c.edge, c.segment, c.vertex)).Nodup := by
  apply List.Nodup.map_on _ (crossings_nodup width d)
  intro c hc c' hc' h
  have he := congrArg Prod.fst h
  have hs := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) h
  have hv := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) h
  exact crossings_key_injective width d hc hc' he hs hv

/-- The actual crossing point, retaining the table's original vertex lookup and height. -/
@[expose] def Crossing.location (width : ℕ) (d : Graph.OrthogonalDrawing) (c : Crossing) : Point :=
  (((prepare width d).1.getD c.vertex (0, 0)).1, c.height)

/-- Every crossing retains an in-bounds position in the actual source edge array. -/
theorem crossing_edge_lt (width : ℕ) (d : Graph.OrthogonalDrawing) {c : Crossing}
    (hc : c ∈ crossings width d) : c.edge < d.2.length := by
  obtain ⟨r, _, _, hr, _⟩ := (mem_crossings_iff width d c).mp hc
  have hz : (r, c.edge) ∈ (prepare width d).2.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hr
  have hi := List.snd_lt_of_mem_zipIdx hz
  simpa only [prepare, List.length_map, Nat.add_zero] using hi

/-- Every actual event lies on its exact original consecutive segment. -/
theorem crossing_location_segment (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {c : Crossing} (hc : c ∈ crossings width d) :
    ∃ ab, ((prepare width d).2.getD c.edge []).consecutivePairs[c.segment]? = some ab ∧
      realPoint (c.location width d) ∈ segment ab.1 ab.2 := by
  obtain ⟨r, ab, site, hr, hab, hsite, htest, hh, _⟩ := (mem_crossings_iff width d c).mp hc
  have hroute : (prepare width d).2.getD c.edge [] = r := by
    simp only [List.getD_eq_getElem?_getD, hr, Option.getD_some]
  have hvertex : (prepare width d).1.getD c.vertex (0, 0) = site := by
    simp only [List.getD_eq_getElem?_getD, hsite, Option.getD_some]
  have hlength := crossing_edge_lt width d hc
  have hi : c.edge < G.edges.length := by rw [← hd.edgeCount]; exact hlength
  have hmem : ab ∈ r.consecutivePairs := by
    have hz : (ab, c.segment) ∈ r.consecutivePairs.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hab
    exact List.fst_mem_of_mem_zipIdx hz
  have hshape := map_segment_slopes width (hd.orthogonal c.edge hi) ab
  have hseg : ab ∈ ((d.2.getD c.edge []).map (point width)).consecutivePairs := by
    rw [← route_prepare, hroute]
    exact hmem
  have hbetween : min ab.1.1 ab.2.1 ≤ site.1 ∧ site.1 ≤ max ab.1.1 ab.2.1 := by
    rcases htest.1 with h | h <;> omega
  have hpoint := cutPoint_mem_segment ab.1 ab.2 (hshape hseg) site.1 hbetween
  refine ⟨ab, ?_, ?_⟩
  · rw [hroute]
    exact hab
  · simpa only [Crossing.location, hvertex, hh, cutPoint] using hpoint

/-- Every emitted event of an actual standard drawing lies on its exact source edge support. -/
theorem crossing_location_supported (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {c : Crossing} (hc : c ∈ crossings width d) :
    realPoint (c.location width d) ∈ support ((prepare width d).2.getD c.edge []) := by
  obtain ⟨ab, hab, hp⟩ := crossing_location_segment width hd hc
  apply Or.inr
  have hz : (ab, c.segment) ∈ ((prepare width d).2.getD c.edge []).consecutivePairs.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hab
  exact ⟨ab, List.fst_mem_of_mem_zipIdx hz, hp⟩

/-- A strict crossing is never the prepared image of an integer grid point in the strip. -/
theorem crossing_location_ne_point (width : ℕ) (d : Graph.OrthogonalDrawing)
    (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width) {c : Crossing}
    (hc : c ∈ crossings width d) (p : Point) (hp : 0 ≤ p.1 ∧ p.1 ≤ width) :
    c.location width d ≠ point width p := by
  obtain ⟨r, ab, site, _, _, hsite, htest, hh, _⟩ := (mem_crossings_iff width d c).mp hc
  have hsiteMem : site ∈ (prepare width d).1 := by
    have hz : (site, c.vertex) ∈ (prepare width d).1.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hsite
    exact List.fst_mem_of_mem_zipIdx hz
  obtain ⟨pv, hpv, hmap⟩ := List.mem_map.mp hsiteMem
  have hlookup : (prepare width d).1.getD c.vertex (0, 0) = site := by
    simp only [List.getD_eq_getElem?_getD, hsite, Option.getD_some]
  intro heq
  have hcol : (point width pv).1 = (point width p).1 := by
    simpa only [Crossing.location, hlookup, ← hmap] using congrArg Prod.fst heq
  have hpp := point_column_injective width (hvertices pv hpv) hp hcol
  subst p
  have hheight : c.height = site.2 := by
    simpa only [Crossing.location, hmap] using congrArg Prod.snd heq
  omega

/-- Constructor computation preserves the standard record encoding, without geometric assumptions. -/
@[fun_prop] theorem computableInPolyTime_crossingAt {α : Type} {enc : α ↪ List Bool}
    {edge segment vertex : α → ℕ} {a b site : α → Point}
    (he : ComputableInPolyTime edge enc encUnary)
    (hs : ComputableInPolyTime segment enc encUnary)
    (hv : ComputableInPolyTime vertex enc encUnary)
    (ha : ComputableInPolyTime a enc encPoint)
    (hb : ComputableInPolyTime b enc encPoint)
    (hp : ComputableInPolyTime site enc encPoint) :
    ComputableInPolyTime (fun x => crossingAt (edge x) (segment x) (vertex x) (a x) (b x) (site x))
      enc (encOption encCrossing) := by
  have hheight := computableInPolyTime_cutHeight.comp
    (show ComputableInPolyTime (fun x => ((a x, b x), (site x).1)) enc
      (encPair (encPair encPoint encPoint) encIntBin) from by unfold encPoint at ha hb hp ⊢; fun_prop)
  dsimp only [crossingAt]
  unfold encPoint at ha hb hp
  fun_prop

@[local fun_prop] private theorem optionToList_polyTime {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (Option.toList (α := α)) (encOption enc) (encList enc) :=
  (ComputableInDegree.optionToList enc).computableInPolyTime

@[local fun_prop] private theorem consecutivePairs_polyTime :
    ComputableInPolyTime (List.consecutivePairs (α := Point)) encRoute (encList (encPair encPoint encPoint)) := by
  unfold List.consecutivePairs encRoute
  fun_prop

/-- Reading a retained crossing location is polynomial-time in the same native array encodings. -/
@[fun_prop] theorem computableInPolyTime_location (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × Crossing => p.2.location width p.1)
      (encPair Graph.encOrthogonalDrawing encCrossing) encPoint := by
  have hprep := computableInPolyTime_prepare width
  unfold Crossing.location Graph.encOrthogonalDrawing encPoint at *
  fun_prop

/-- The complete source-position-preserving crossing table is emitted in standard polynomial time. -/
@[fun_prop] theorem computableInPolyTime_crossings (width : ℕ) :
    ComputableInPolyTime (crossings width) Graph.encOrthogonalDrawing (encList encCrossing) := by
  have hprep := computableInPolyTime_prepare width
  have hr : ComputableInPolyTime (fun d => (prepare width d).2.zipIdx)
      Graph.encOrthogonalDrawing (encList (encPair encRoute encUnary)) := by
    unfold Graph.encOrthogonalDrawing at hprep
    fun_prop
  unfold crossings
  apply ComputableInPolyTime.flatMapWithInput hr
  have hsegments : ComputableInPolyTime
      (fun p : Graph.OrthogonalDrawing × (Route × ℕ) => p.2.1.consecutivePairs.zipIdx)
      (encPair Graph.encOrthogonalDrawing (encPair encRoute encUnary))
      (encList (encPair (encPair encPoint encPoint) encUnary)) := by fun_prop
  apply ComputableInPolyTime.flatMapWithInput hsegments
  simp only [List.filterMap_eq_flatMap_toList]
  have hsites : ComputableInPolyTime
      (fun p : (Graph.OrthogonalDrawing × (Route × ℕ)) × ((Point × Point) × ℕ) =>
        (prepare width p.1.1).1.zipIdx)
      (encPair (encPair Graph.encOrthogonalDrawing (encPair encRoute encUnary))
        (encPair (encPair encPoint encPoint) encUnary))
      (encList (encPair encPoint encUnary)) := by
    unfold Graph.encOrthogonalDrawing at hprep
    fun_prop
  apply ComputableInPolyTime.flatMapWithInput hsites
  fun_prop

end PushPuzzle.PushS.Comb
