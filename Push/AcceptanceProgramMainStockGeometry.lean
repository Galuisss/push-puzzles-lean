/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramColumns
public import PushS.PortAxisFixed
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all PushS.PortAxisClear
import all PushS.PortEndpointCounts
import all PushS.PortOrdinaryAxis
import all PushS.PortSignalLocality
import all PushS.PortEndpointSeparation
import all PushS.PortCoreCrossing
import all PushS.PortWireGeometry
import all PushS.PortSegments

/-! Each genuine endpoint's literal main prefix contains precisely its first two canonical axis cells. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem axis_injective (p : Scales.Parameters) {i j : ℕ} (he : p.x i = p.x j) : i = j := by
  have hD : 0 < p.D := by have := p.outer_distance; omega
  have hm := Nat.mul_right_cancel hD he
  omega

/-- On the endpoint's actual column, the entire same-page main block is exactly its own prefix. -/
theorem mainRound_column_region (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x e.port) :
    q ∈ (mainRound l p e.side).region ↔ pageDepth p e.side q < p.Y e.level + 2 := by
  constructor
  · intro hr
    obtain ⟨_, hreq, hcol, hpos⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hreq
    obtain ⟨hf, hs⟩ := List.mem_filter.mp hf
    have hs : f.side = e.side := by simpa only [beq_iff_eq] using hs
    have hport : f.port = e.port := by
      apply axis_injective p
      have hcol : q.1.val = p.x f.port := by cases hside : e.side <;>
        simpa only [hside, ite_true, reduceCtorEq, ite_false, Direction.lane] using hcol
      exact hcol.symm.trans hx
    have hef := l.endpoints_key_injective hl hf he hs hport
    rw [hef] at hpos
    cases hside : e.side <;>
      simpa only [hside, pageDepth, prefixRank, Nat.add_sub_cancel, ite_true, reduceCtorEq, ite_false] using hpos
  · exact endpoint_main_region l p e he hx

private theorem own_axis_first_two (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x e.port)
    (hy : pageDepth p e.side q = p.Y e.level ∨ pageDepth p e.side q = p.Y e.level + 1) :
    q ∈ targetHoles l p target := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hd := readDepth_eq p hj hjm
  have hY := readDepth_add_lt_H p e.level
  have hrow := q.2.isLt
  have haxis : (q.1.val, q.2.val) ∈ pointHoles
      ((endpointSegments (coordinates p) (l.canonical target) e).take 1) := by
    apply (axis_mem p (l.canonical target) e _).mpr
    refine ⟨hx, ?_⟩
    have hb := Bool.toNat_le (if e.side = .upper then (l.canonical target).axes.getD e.port false
      else !((l.canonical target).axes.getD e.port false))
    cases hs : e.side <;>
      simp only [pageDepth, onSide, hs, ite_true, reduceCtorEq, ite_false, coordinates] at hy ⊢ <;> omega
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp haxis
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, List.mem_of_mem_take hs⟩)), hc⟩

private theorem source_main_front_depth (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ targetHoles l p target)
    (hx : q.1.val = p.x e.port) (hy0 : 0 < pageDepth p e.side q)
    (hy : pageDepth p e.side q < p.Y e.level + 2) :
    pageDepth p e.side q = p.Y e.level ∨ pageDepth p e.side q = p.Y e.level + 1 := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hY := readDepth_add_lt_D p e.level
  rw [readDepth_eq p hj hjm] at hY
  have hh : p.H = 2 * p.D := rfl
  have hrow := q.2.isLt
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · have hfixed := l.fixedSegments_on_main_axis p hl hM haxes (l.endpoints_port_lt hl he)
      ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hx
    have hY1 := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hY1
    rcases hfixed with hzero | hend | ⟨hcenter, hhalf⟩
    · cases hside : e.side <;> simp only [pageDepth, hside, ite_true, reduceCtorEq, ite_false] at hy0 hy <;> omega
    · cases hside : e.side <;> simp only [pageDepth, hside, ite_true, reduceCtorEq, ite_false] at hy0 hy <;> omega
    · rw [readDepth_eq p le_rfl p.levels_pos] at hhalf
      cases hside : e.side with
      | upper => simp only [pageDepth, hside, ite_true] at hy; omega
      | lower =>
        obtain ⟨kind, first, hg, hp⟩ := center_gate_mem l hcenter
        exact False.elim (l.endpoints_lower_ne_gate_middle hl hg he hside hp)
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨f, hf, hs⟩ := List.mem_flatMap.mp hs
      have hsignal : (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) (l.canonical target) f) :=
        (mem_pointHoles _ _).mpr ⟨s, hs, hc⟩
      have hport : f.port = e.port := by
        by_contra hn
        exact off_axis_of_span p hn (r := 2)
          (by have := readDepth_readLength_margin p 0 0; omega) (signal_span p (l.canonical target) f hsignal) hx
      have hside : f.side = e.side := by
        by_contra hn
        have hband := acceptanceEndpointSignalBand p (l.canonical target) f hsignal
        have hfD := readDepth_add_lt_D p f.level
        cases hfs : f.side <;> cases hes : e.side <;>
          simp only [hfs, hes, reduceCtorEq, not_true_eq_false, pageDepth, ite_true, ite_false] at hn hy0 hy hband <;> omega
      have hef := l.endpoints_key_injective hl hf he hside hport
      subst f
      rw [← List.take_append_drop 1 (endpointSegments (coordinates p) (l.canonical target) e),
        pointHoles_append, Finset.mem_union] at hsignal
      rcases hsignal with haxis | hhorizontal
      · have haxis := (axis_mem p (l.canonical target) e _).mp haxis
        rw [readDepth_eq p hj hjm] at haxis
        cases hside : e.side <;>
          simp only [hside, pageDepth, onSide, ite_true, reduceCtorEq, ite_false, coordinates] at haxis hy0 hy ⊢ <;> omega
      · exact False.elim (horizontal_near_off_axis p (l.canonical target) e hhorizontal hx)
    · obtain ⟨g, hg, hs⟩ := List.mem_flatMap.mp hs
      cases hk : g.gate with
      | none => simp only [tripleSignal, hk, Option.elim_none, List.not_mem_nil] at hs
      | some kind =>
        have hgate : (q.1.val, q.2.val) ∈ pointHoles
            (gateSegments (coordinates p) (l.canonical target) kind g.left g.internal) :=
          (mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hk, Option.elim_some] using hs, hc⟩
        cases hside : e.side with
        | upper =>
          have hb := gate_signal_page p (l.canonical target) kind g.left g.internal hgate
          simp only [pageDepth, hside, ite_true] at hy
          omega
        | lower =>
          have hn : g.left + 1 ≠ e.port := gate_middle_ne l hl he hside (center_of_gate l (placement_gate_mem l hg hk))
          exact False.elim (off_axis_of_span p hn (r := 12)
            (by have := readDepth_readLength_margin p 0 0; omega)
            (by have := gate_signal_span p (l.canonical target) kind g.left g.internal hgate; omega) hx)

/-- The canonical strict-interior front of one actual main-axis read. -/
@[expose] def mainSourceFront (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (e : Endpoint) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (targetHoles l p target \ Boundary.frame).filter fun q =>
    q.1.val = p.x e.port ∧ pageDepth p e.side q < p.Y e.level + 2

/-- Both sides have exactly the two literal first-axis cells in their canonical main-read front. -/
theorem mem_mainSourceFront (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ mainSourceFront l p target e ↔ q.1.val = p.x e.port ∧
      (pageDepth p e.side q = p.Y e.level ∨ pageDepth p e.side q = p.Y e.level + 1) := by
  constructor
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp hq
    have hy0 : 0 < pageDepth p e.side q := by
      by_contra hn
      have hrow := q.2.isLt
      have hz : pageDepth p e.side q = 0 := by omega
      apply hf
      cases hside : e.side with
      | upper =>
        apply (Boundary.mem_frame q).mpr
        refine ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa only [pageDepth, hside, ite_true] using hz
      | lower =>
        apply (Boundary.mem_frame q).mpr
        refine ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simp only [pageDepth, hside, reduceCtorEq, ite_false] at hz
        omega
    exact ⟨hx, source_main_front_depth l p hl hM haxes target e he ht hx hy0 hy⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
    have hY := readDepth_add_lt_H p e.level
    rw [readDepth_eq p hj hjm] at hY
    have hpos := p.Y_ge e.level
    have hx0 := readLength_add_lt_x p e.port 0
    have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le haxes) 0
    have hrow := q.2.isLt
    have hf : q ∉ Boundary.frame := by
      intro hframe
      obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hframe
      cases hside : e.side <;> cases d <;>
        simp only [pageDepth, hside, ite_true, reduceCtorEq, ite_false, Boundary.edge,
          Finset.mem_filter, Finset.mem_univ, true_and] at hy hd <;> omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
      ⟨own_axis_first_two l p hl hM target e he hx hy, hf⟩, hx, by rcases hy with h | h <;> omega⟩

/-- Every genuine endpoint contributes exactly two canonical holes to its main-axis prefix. -/
theorem mainSourceFront_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) :
    (mainSourceFront l p target e).card = 2 := by
  classical
  have hcard : (mainSourceFront l p target e).card = ({p.Y e.level, p.Y e.level + 1} : Finset ℕ).card := by
    apply Finset.card_bij (fun q _ => pageDepth p e.side q)
    · intro q hq
      have hy := ((mem_mainSourceFront l p hl hM haxes target e he q).mp hq).2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
    · intro q hq r hr heq
      have hqx := ((mem_mainSourceFront l p hl hM haxes target e he q).mp hq).1
      have hrx := ((mem_mainSourceFront l p hl hM haxes target e he r).mp hr).1
      apply Prod.ext (Fin.ext (hqx.trans hrx.symm))
      apply Fin.ext
      have hqH := q.2.isLt
      have hrH := r.2.isLt
      cases hside : e.side <;>
        simp only [pageDepth, hside, ite_true, reduceCtorEq, ite_false] at heq <;> omega
    · intro v hv
      have hv' : v = p.Y e.level ∨ v = p.Y e.level + 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
      have hY := readDepth_add_lt_H p e.level
      rw [readDepth_eq p hj hjm] at hY
      have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le haxes) 0
      let q : Cell (p.W + 1) (p.H + 1) :=
        (⟨p.x e.port, by omega⟩, ⟨if e.side = .upper then v else p.H - v, by split <;> omega⟩)
      have hdepth : pageDepth p e.side q = v := by
        cases hside : e.side <;> simp only [q, pageDepth, hside, ite_true, reduceCtorEq, ite_false]
        omega
      refine ⟨q, (mem_mainSourceFront l p hl hM haxes target e he q).mpr ⟨rfl, ?_⟩, hdepth⟩
      simpa only [hdepth] using hv'
  rw [hcard]
  simp

end PushPuzzle.Push.AcceptanceProgram
