/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramProbeStockSurvival
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments

/-! Exact target-independent fixed inventory plus true-axis bits on the actual R13 probe rows. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProbe
open scoped BigOperators

/-- The literal thirteen-block prefix, with its actual canonical interior inventory. -/
@[expose] def probePrefix (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  preparation l p (targetHoles l p target \ Boundary.frame).card

/-- The actual canonical target stock on the selected upper probe rows after preparation. -/
@[expose] def probeReference (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (emit (probePrefix l p target) (targetHoles l p target)).remaining.filter fun q => q.2.val ∈ probeRows l p

/-- The literal fixed-segment bitmap remaining on probe rows under the all-false canonical prefix mask. -/
@[expose] def probeFixedStock (l : PortLayout) (p : Scales.Parameters) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (emit (probePrefix l p []) (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p))).remaining.filter
    fun q => q.2.val ∈ probeRows l p

private theorem probePrefix_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    probePrefix l p target = probePrefix l p [] := by
  have htotal := l.encodedSegments_holes_card_eq p hl hM haxes (l.canonical target) (l.canonical [])
  have ht := Finset.card_sdiff_add_card_eq_card (l.encodedSegments_frame_subset p (l.canonical target))
  have hz := Finset.card_sdiff_add_card_eq_card (l.encodedSegments_frame_subset p (l.canonical []))
  unfold probePrefix
  apply congrArg (preparation l p)
  change (targetHoles l p target).card = (targetHoles l p []).card at htotal
  change (targetHoles l p target \ Boundary.frame).card + Boundary.frame.card = (targetHoles l p target).card at ht
  change (targetHoles l p [] \ Boundary.frame).card + Boundary.frame.card = (targetHoles l p []).card at hz
  omega

/-- The full actual R13 probe stock is its literal fixed background and exactly its true original-axis points. -/
theorem probeReference_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    probeReference l p target = probeFixedStock l p ∪ probeSignalStock l p hl hM haxes target := by
  have hprefix := probePrefix_eq l p hl hM haxes target
  have hsurvive := probeSignalStock_preparation_remaining l p hl hM haxes target
  change probeSignalStock l p hl hM haxes target ⊆ (emit (probePrefix l p target) (targetHoles l p target)).remaining at hsurvive
  rw [hprefix] at hsurvive
  ext q
  simp only [probeReference, probeFixedStock, hprefix, emit_remaining, Finset.mem_filter,
    Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hq, hmask⟩, hrows⟩
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    rcases List.mem_append.mp hs with hfixed | hsignal
    · exact Or.inl ⟨⟨(SegmentRecipe.mem_holes _ q).mpr ⟨s, hfixed, hc⟩, hmask⟩, hrows⟩
    · exact Or.inr ((signal_probe_rows l p hl hM haxes target).mp
        ⟨(mem_pointHoles _ _).mpr ⟨s, hsignal, hc⟩, hrows⟩)
  · rintro (hfixed | hsignal)
    · obtain ⟨⟨hq, hmask⟩, hrows⟩ := hfixed
      obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
      exact ⟨⟨(SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩, hmask⟩, hrows⟩
    · exact ⟨Finset.mem_sdiff.mp (by simpa only [emit_remaining] using hsurvive hsignal),
        ((signal_probe_rows l p hl hM haxes target).mpr hsignal).2⟩

/-- Fixed probe stock and target-bit probe points are genuinely disjoint in the actual emitted geometry. -/
private theorem probeFixedStock_disjoint_signal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    Disjoint (probeFixedStock l p) (probeSignalStock l p hl hM haxes target) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  have hfixed := emit_remaining_subset _ _ (Finset.mem_filter.mp hfixed).1
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hfixed
  exact Finset.disjoint_left.mp (l.fixedSegments_disjoint_signalSegments p hl hM haxes (l.canonical target))
    ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) (((signal_probe_rows l p hl hM haxes target).mpr hsignal).1)

/-- Each actual allocated probe row pays one fixed computed background plus its same-level target bits. -/
theorem probeReference_row_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    ((probeReference l p target).filter fun q => q.2.val = p.Y j + 2).card =
      ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2).card +
        ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j),
          (target.getD i.val false).toNat := by
  rw [probeReference_eq l p hl hM haxes target, Finset.filter_union]
  have hd : Disjoint ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2)
      ((probeSignalStock l p hl hM haxes target).filter fun q => q.2.val = p.Y j + 2) :=
    (probeFixedStock_disjoint_signal l p hl hM haxes target).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [Finset.card_union_of_disjoint hd, probeSignalStock_row_card l p hl hM haxes target hj hjm]

/-- The literal R13 boundary is exactly the end of all preparation blocks. -/
private theorem schedule_take_thirteen (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    (schedule l p k).take 13 = preparation l p k := by
  change (preparation l p k ++ _).take 13 = _
  rw [← preparation_length l p k, List.take_left]

/-- The actual program's R13 probe-row bitmap is the same fixed background plus its true-axis probe image. -/
theorem schedule_probe_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    ((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 13)
      (targetHoles l p target)).remaining.filter fun q => q.2.val ∈ probeRows l p) =
      probeFixedStock l p ∪ probeSignalStock l p hl hM haxes target := by
  rw [schedule_take_thirteen]
  exact probeReference_eq l p hl hM haxes target

/-- On any actually selected allocated probe row, the unmasked R13 reference count has the exact fixed-plus-bit ledger. -/
theorem schedule_probe_row_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hrow : p.Y j + 2 ∈ probeRows l p) :
    (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 13)
      (targetHoles l p target)).remaining).filter fun q => q.2.val = p.Y j + 2).card =
      ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2).card +
        ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j),
          (target.getD i.val false).toNat := by
  have he := probeReference_row_card l p hl hM haxes target hj hjm
  rw [schedule_take_thirteen]
  have hfilter : ((probeReference l p target).filter fun q => q.2.val = p.Y j + 2) =
      ((emit (probePrefix l p target) (targetHoles l p target)).remaining.filter fun q => q.2.val = p.Y j + 2) := by
    ext q
    simp only [probeReference, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hrow⟩, h.2⟩⟩
  exact (congrArg Finset.card hfilter).symm.trans he

end PushPuzzle.Push.AcceptanceProgram
