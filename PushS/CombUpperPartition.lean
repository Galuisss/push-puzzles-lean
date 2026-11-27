/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombUpperVisits
public import PushS.CombNumbering
import all PushS.CombUpperVisits
import all PushS.CombPartition
import all PushS.CombTopology
import all PushS.CombCore
import all PushS.CombNumbering

/-! The actual original-edge fragments and local rotations partition the upper contour. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

private def pairTokens (pair : Token × Token) : List Token := [pair.1, pair.2]

private def markSides (c : Crossing) : List Token := [c.token false, c.token true]

private theorem crossingWord_perm (c : Crossing) : (crossingWord c).Perm (markSides c) := by
  cases hc : c.forward <;> simp only [crossingWord, hc, Bool.false_eq_true, ite_false, ite_true, markSides]
  · exact List.Perm.swap _ _ _
  · exact .refl _

private theorem edgeVisits_perm (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeVisits width d edge).Perm
      ([.tip edge false, .tip edge true] ++ (edgeCrossings width d edge).flatMap markSides) := by
  have hp := (List.Perm.flatMap_left (edgeCrossings width d edge) (fun c _ => crossingWord_perm c)).append_right
    [Token.tip edge true]
  have hs : ((edgeCrossings width d edge).flatMap markSides ++ [Token.tip edge true]).Perm
      (Token.tip edge true :: (edgeCrossings width d edge).flatMap markSides) := List.perm_append_comm
  exact (hp.trans hs).cons (.tip edge false)

private theorem core_order_perm (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    (hlen : ports.length = 3) :
    (coreTemplate vertex ports).order.Perm
      (ports.map (fun p => incidenceToken p.1) ++ (coreTemplate vertex ports).upper.flatMap pairTokens) := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  unfold coreTemplate
  extract_lets pa pb pc kind ta tb tc inside outside
  split_ifs <;> simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    pairTokens, List.append_nil, List.cons_append, List.nil_append]
  · exact .refl _
  · exact (show ([outside, inside] ++ [ta, tb, tc]).Perm ([ta, tb, tc] ++ [outside, inside]) from
      List.perm_append_comm)
  · exact .refl _

private theorem vertex_order_perm (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    {v : ℕ} (hv : v < input.graph.vertices.length) :
    (vertexBlock width input v).order.Perm
      ((input.graph.vertices.getD v ⟨[], 0⟩).ports.map (fun p => incidenceToken p.1) ++
        (toothCrossings width input.drawing v).flatMap markSides ++
        (vertexBlock width input v).upper.flatMap pairTokens) := by
  let hits := toothCrossings width input.drawing v
  let core := coreBlock width input v
  have hc := core_order_perm v (fan width input v) (fan_length width input hg hv)
  have hf := (fan_perm width input v).map (fun p => incidenceToken p.1)
  have hc' := hc.trans (hf.append_right (core.upper.flatMap pairTokens))
  have hm := paired_tokens_perm hits (fun c => c.token false) (fun c => c.token true)
  apply Multiset.coe_eq_coe.mp
  have he := Multiset.coe_eq_coe.mpr hc'
  have hm' := Multiset.coe_eq_coe.mpr hm
  change (↑(hits.map (fun c => c.token false) ++ core.order ++ hits.reverse.map (fun c => c.token true)) : Multiset Token) = _
  simp only [← Multiset.coe_add] at he hm' ⊢
  change (↑core.order : Multiset Token) = _ at he
  rw [he]
  change _ = (↑((input.graph.vertices.getD v ⟨[], 0⟩).ports.map (fun p => incidenceToken p.1)) : Multiset Token) +
    ↑(hits.flatMap markSides) + ↑(core.upper.flatMap pairTokens)
  rw [show (↑(hits.flatMap markSides) : Multiset Token) =
      ↑(hits.map (fun c => c.token false)) + ↑(hits.reverse.map (fun c => c.token true)) from hm']
  ac_rfl

private theorem vertex_reads_perm {α : Type} (width : ℕ) (d : Graph.OrthogonalDrawing)
    (xs : List α) (default : α) (hlen : xs.length = d.1.length) :
    ((vertexOrder width d).map fun sv => xs.getD sv.2 default).Perm xs := by
  have hp := (vertexOrder_perm width d).map (fun sv => xs.getD sv.2 default)
  have hl : xs.length = (prepare width d).1.length := by simpa only [prepare, List.length_map] using hlen
  rw [List.map_getD_zipIdx _ xs default hl] at hp
  exact hp

/-- Regrouping all actual crossing occurrences by their sorted teeth retains the exact table. -/
theorem toothCrossings_flatMap_perm (width : ℕ) (d : Graph.OrthogonalDrawing) :
    ((vertexOrder width d).flatMap fun sv => toothCrossings width d sv.2).Perm (crossings width d) := by
  have hp := (vertexOrder_perm width d).flatMap_right (fun sv => toothCrossings width d sv.2)
  apply hp.trans
  have hfilter := List.Perm.flatMap_left (prepare width d).1.zipIdx
    (fun sv _ => toothCrossings_perm width d sv.2)
  apply hfilter.trans
  have hi := congrArg
    (List.flatMap fun v => (crossings width d).filter fun c => decide (c.vertex = v))
    (List.zipIdx_map_snd (l := (prepare width d).1) 0)
  simp only [List.flatMap_map] at hi
  rw [hi]
  have hp := filter_range_perm Crossing.vertex (crossings width d) d.1.length
  have he : (crossings width d).filter (fun c => decide (c.vertex < d.1.length)) = crossings width d := by
    apply List.filter_eq_self.mpr
    intro c hc
    exact decide_eq_true (crossing_vertex_lt width d hc)
  simpa only [prepare, List.length_map, ← List.range_eq_range', he] using hp

private def nativeTips (input : Input) : List Token :=
  (input.graph.vertices.flatMap NCL.Vertex.ports).map fun p => incidenceToken p.1

private def rotationTokens (width : ℕ) (input : Input) : List Token :=
  (vertexOrder width input.drawing).flatMap fun sv => (vertexBlock width input sv.2).upper.flatMap pairTokens

private theorem cut_order_perm (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) :
    (cut width input).order.Perm
      (nativeTips input ++ (crossings width input.drawing).flatMap markSides ++ rotationTokens width input) := by
  let vs := vertexOrder width input.drawing
  let tips := fun sv : Cslib.Orthogonal.Point × ℕ =>
    (input.graph.vertices.getD sv.2 ⟨[], 0⟩).ports.map fun p => incidenceToken p.1
  let marks := fun sv : Cslib.Orthogonal.Point × ℕ =>
    (toothCrossings width input.drawing sv.2).flatMap markSides
  let rotations := fun sv : Cslib.Orthogonal.Point × ℕ => (vertexBlock width input sv.2).upper.flatMap pairTokens
  have hp := List.Perm.flatMap_left vs (fun sv hsv => vertex_order_perm width input hg (v := sv.2) (by
    have hi := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hsv)
    simp only [prepare, List.length_map, Nat.add_zero] at hi
    omega))
  have hs := ((List.flatMap_append_perm vs tips marks).append_right (vs.flatMap rotations)).trans
    (List.flatMap_append_perm vs (fun sv => tips sv ++ marks sv) rotations)
  have hp' := hp.trans hs.symm
  have ht := (vertex_reads_perm width input.drawing input.graph.vertices ⟨[], 0⟩ hcount.symm).flatMap_right
    (fun v => v.ports.map fun p => incidenceToken p.1)
  simp only [List.flatMap_map, ← List.map_flatMap] at ht
  have hm := (toothCrossings_flatMap_perm width input.drawing).flatMap_right markSides
  simp only [List.flatMap_assoc] at hm
  have hlast : (vs.flatMap tips ++ vs.flatMap marks ++ vs.flatMap rotations).Perm
      (nativeTips input ++ (crossings width input.drawing).flatMap markSides ++ rotationTokens width input) := by
    simpa only [tips, marks, vs, rotations, nativeTips, rotationTokens, List.map_flatMap] using
      ((ht.append hm).append (.refl (vs.flatMap rotations)))
  simpa only [cut, List.flatMap_map, vs] using hp'.trans hlast

private theorem nativeTips_perm_range (input : Input) (hg : NCL.SourceValid input.graph) :
    (nativeTips input).Perm
      ((List.range input.graph.edgeCount).flatMap fun edge => [.tip edge false, .tip edge true]) := by
  have hr : (List.ofFn fun e : Fin input.graph.edgeCount => [Token.tip e.val false, Token.tip e.val true]) =
      (List.range input.graph.edgeCount).map (fun edge => [Token.tip edge false, Token.tip edge true]) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  have hp := native_tips_perm input.graph hg
  rw [hr] at hp
  simpa only [← List.flatMap_def, nativeTips] using hp

private theorem allEdgeVisits_perm (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hedges : input.drawing.2.length = input.graph.edgeCount) :
    ((List.range input.drawing.2.length).flatMap fun edge => edgeVisits width input.drawing edge).Perm
      (nativeTips input ++ (crossings width input.drawing).flatMap markSides) := by
  let edges := List.range input.drawing.2.length
  have hp := List.Perm.flatMap_left edges (fun edge _ => edgeVisits_perm width input.drawing edge)
  have hs := List.flatMap_append_perm edges (fun edge => [Token.tip edge false, Token.tip edge true])
    (fun edge => (edgeCrossings width input.drawing edge).flatMap markSides)
  have hm := (edgeCrossings_flatMap_perm width input.drawing).flatMap_right markSides
  simp only [List.flatMap_assoc] at hm
  have ht := nativeTips_perm_range input hg
  rw [← hedges] at ht
  exact (hp.trans hs.symm).trans (ht.symm.append hm)

/-- The same actual upper groups cover the complete computed contour token inventory. -/
theorem cut_upper_tokens_perm (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount) :
    ((cut width input).upper.flatMap fun p => [p.1, p.2]).Perm (cut width input).order := by
  have hp := (allEdgeVisits_perm width input hg hedges).append_right (rotationTokens width input)
  have ht := hp.trans (cut_order_perm width input hg hcount).symm
  change ((input.drawing.2.zipIdx.flatMap (fun re => pairOff (edgeVisits width input.drawing re.2)) ++
    ((vertexOrder width input.drawing).map fun sv => vertexBlock width input sv.2).flatMap Block.upper).flatMap
    (fun p => [p.1, p.2])).Perm (cut width input).order
  rw [List.flatMap_append, allUpperFragments_tokens]
  simp only [rotationTokens] at ht
  unfold pairTokens at ht
  simpa only [List.flatMap_map, List.flatMap_assoc] using ht

/-- Both ends of every actual upper fragment belong to the same computed contour. -/
theorem cut_upper_pair_mem (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    {a b : Token} (hab : (a, b) ∈ (cut width input).upper) :
    a ∈ (cut width input).order ∧ b ∈ (cut width input).order := by
  have hp := cut_upper_tokens_perm width input hg hcount hedges
  exact ⟨hp.mem_iff.mp (List.mem_flatMap.mpr ⟨(a, b), hab, by simp⟩),
    hp.mem_iff.mp (List.mem_flatMap.mpr ⟨(a, b), hab, by simp⟩)⟩

/-- No emitted upper group repeats one contour port at its two ends. -/
theorem cut_upper_pair_distinct (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    {a b : Token} (hab : (a, b) ∈ (cut width input).upper) : a ≠ b := by
  have hn := (cut_upper_tokens_perm width input hg hcount hedges).nodup_iff.mpr
    (cut_order_nodup width input hg hcount)
  simpa using (List.nodup_flatMap.mp hn).1 (a, b) hab

/-- Every actual contour token occurs in exactly one indexed upper pair. -/
theorem cut_upper_unique (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount) {token : Token}
    (ht : token ∈ (cut width input).order) :
    ∃! i : Fin (cut width input).upper.length,
      token = ((cut width input).upper.get i).1 ∨ token = ((cut width input).upper.get i).2 := by
  have hp := cut_upper_tokens_perm width input hg hcount hedges
  simpa using unique_flatMap_index _ _
    (hp.nodup_iff.mpr (cut_order_nodup width input hg hcount)) (hp.mem_iff.mpr ht)

private theorem upper_pair_at (c : Cut) (i : c.toLayout.pages.upperPage.Index) :
    c.toLayout.pages.upperPage.group i =
      .wire (min (c.rank (c.upper.get ⟨i.val, by simpa [Cut.toLayout, PortLayout.pages,
        PageLevels.Pages.upperPage] using i.isLt⟩).1)
          (c.rank (c.upper.get ⟨i.val, by simpa [Cut.toLayout, PortLayout.pages,
        PageLevels.Pages.upperPage] using i.isLt⟩).2))
        (max (c.rank (c.upper.get ⟨i.val, by simpa [Cut.toLayout, PortLayout.pages,
        PageLevels.Pages.upperPage] using i.isLt⟩).1)
          (c.rank (c.upper.get ⟨i.val, by simpa [Cut.toLayout, PortLayout.pages,
        PageLevels.Pages.upperPage] using i.isLt⟩).2)) := by
  have hi : i.val < c.upper.length := by
    simpa [Cut.toLayout, PortLayout.pages, PageLevels.Pages.upperPage] using i.isLt
  change ((c.upper.map (fun p => (min (c.rank p.1) (c.rank p.2), max (c.rank p.1) (c.rank p.2)))).map
    (fun p => PageLevels.Group.wire p.1 p.2))[i.val]'(by simpa using hi) = _
  simp only [List.getElem_map, List.get_eq_getElem]

/-- The same actual compiled upper page has bounded, nondegenerate intervals. -/
theorem compile_upper_bounded (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (i : (compile width input).pages.upperPage.Index) :
    ((compile width input).pages.upperPage.group i).left <
        ((compile width input).pages.upperPage.group i).right ∧
      ((compile width input).pages.upperPage.group i).right < (compile width input).portCount := by
  let c := cut width input
  let j : Fin c.upper.length := ⟨i.val, by
    simpa [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.upperPage] using i.isLt⟩
  have hp := cut_upper_pair_mem width input hg hcount hedges (List.get_mem c.upper j)
  have hn := cut_upper_pair_distinct width input hg hcount hedges (List.get_mem c.upper j)
  have ha := c.rank_lt hp.1
  have hb := c.rank_lt hp.2
  have hne : c.rank (c.upper.get j).1 ≠ c.rank (c.upper.get j).2 :=
    fun h => hn (c.rank_injective hp.1 h)
  change (c.toLayout.pages.upperPage.group i).left < (c.toLayout.pages.upperPage.group i).right ∧
    (c.toLayout.pages.upperPage.group i).right < c.order.length
  rw [upper_pair_at c i]
  dsimp only [PageLevels.Group.left, PageLevels.Group.right]
  change min (c.rank (c.upper.get j).1) (c.rank (c.upper.get j).2) <
      max (c.rank (c.upper.get j).1) (c.rank (c.upper.get j).2) ∧
    max (c.rank (c.upper.get j).1) (c.rank (c.upper.get j).2) < c.order.length
  omega

/-- The actual numbered upper page partitions every emitted port exactly once. -/
theorem compile_upper_partition (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (k : ℕ) (hk : k < (compile width input).portCount) :
    ∃! i : (compile width input).pages.upperPage.Index,
      k ∈ ((compile width input).pages.upperPage.group i).ports := by
  let c := cut width input
  have hk' : k < c.order.length := hk
  let token := c.order[k]
  have ht : token ∈ c.order := List.getElem_mem hk'
  have hrank : c.rank token = k := (cut_order_nodup width input hg hcount).idxOf_getElem k hk'
  obtain ⟨i, hi, huniq⟩ := cut_upper_unique width input hg hcount hedges ht
  let j : (compile width input).pages.upperPage.Index :=
    ⟨i.val, by simpa only [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.upperPage,
      List.length_map] using i.isLt⟩
  have port_mem (j' : (compile width input).pages.upperPage.Index) :
      k ∈ ((compile width input).pages.upperPage.group j').ports ↔
        c.rank (c.upper.get ⟨j'.val, by simpa [compile, Cut.toLayout, PortLayout.pages,
          PageLevels.Pages.upperPage] using j'.isLt⟩).1 = k ∨
        c.rank (c.upper.get ⟨j'.val, by simpa [compile, Cut.toLayout, PortLayout.pages,
          PageLevels.Pages.upperPage] using j'.isLt⟩).2 = k := by
    change k ∈ (c.toLayout.pages.upperPage.group j').ports ↔ _
    rw [upper_pair_at c j']
    simp only [PageLevels.Group.ports, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hj : k ∈ ((compile width input).pages.upperPage.group j).ports := by
    apply (port_mem j).mpr
    rcases hi with hi | hi
    · exact Or.inl (hi ▸ hrank)
    · exact Or.inr (hi ▸ hrank)
  refine ⟨j, hj, ?_⟩
  intro j' hj'
  let i' : Fin c.upper.length :=
    ⟨j'.val, by simpa [compile, Cut.toLayout, PortLayout.pages, PageLevels.Pages.upperPage] using j'.isLt⟩
  have hi' : token = (c.upper.get i').1 ∨ token = (c.upper.get i').2 := by
    rcases (port_mem j').mp hj' with hfirst | hlast
    · exact Or.inl (c.rank_injective ht (hrank.trans hfirst.symm))
    · exact Or.inr (c.rank_injective ht (hrank.trans hlast.symm))
  have heq : i' = i := huniq i' hi'
  apply Fin.ext
  exact congrArg (fun x : Fin c.upper.length => x.val) heq

end PushPuzzle.PushS.Comb
