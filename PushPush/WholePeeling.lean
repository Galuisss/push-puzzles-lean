/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeCleanup
public import Push.CyclicPeelingProgram

/-! A complete cyclic whole-run continuation projects back to its original source program. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell State Direction)
open Push.Cyclic
open WholeScan

/-- New dock rows retain their zero lower-bound reads in a loose execution. -/
def paddingRows (r : Push.ColumnScan.Input) : List ℕ :=
  (List.range ((dock r).outputHeight - (wideReader r).outputHeight)).map
    fun j => (wideReader r).outputHeight + j

def paddedUnturned (r : Push.ColumnScan.Input) (rows : List ℕ)
    (tail : List (Push.Scan.Instruction r.width r.height)) :
    List (Push.Scan.Instruction (dock r).outputWidth (dock r).outputHeight) :=
  (Push.Scan.lines .west (Push.Scan.ofQuotas rows)).map (sourceInstruction r) ++
    rowProgram (auxiliaryRows r) (r.width + 2) ++ rowProgram (paddingRows r) 0 ++
      tail.map (sourceInstruction r)

theorem paddedUnturned_turned (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height)) :
    turnProgram (paddedUnturned r rows tail) =
      Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail := by
  have hw : r.height ≤ (wideReader r).outputHeight := by
    change r.height ≤ r.height + (wideReader r).length
    omega
  have hsum : r.height + ((wideReader r).outputHeight - r.height) =
      (wideReader r).outputHeight := by omega
  simp only [paddedUnturned, turnProgram, List.map_append, nextTail,
    nextQuotas, Push.Scan.ofQuotas_append, Push.Scan.columns, Push.Scan.lines,
    List.length_append, List.length_replicate, hlen, hsum, List.mapIdx_replicate,
    rowProgram, auxiliaryRows, paddingRows, List.map_map]
  rfl

theorem paddedUnturned_bounded (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i) : Push.Scan.Bounded (paddedUnturned r rows tail) := by
  intro i hi
  simp only [paddedUnturned, List.mem_append] at hi
  have hold := unturnedProgram_bounded r rows hlen tail hbound
  rcases hi with ((hsource | hclean) | hpad) | htail
  · exact hold i (List.mem_append_left _ (List.mem_append_left _ hsource))
  · exact hold i (List.mem_append_left _ (List.mem_append_right _ hclean))
  · obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hpad
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj := List.mem_range.mp hj
    change (wideReader r).outputHeight + j < (dock r).outputHeight
    omega
  · exact hold i (List.mem_append_right _ htail)

private theorem paddedUnturned_sound (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    {E G : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    (H : LooseExec (paddedUnturned r rows tail) E G) :
    LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows) ++ tail)
      (sourceData r E) (sourceData r G) := by
  change LooseExec (((Push.Scan.lines .west (Push.Scan.ofQuotas rows)).map (sourceInstruction r) ++
    rowProgram (auxiliaryRows r) (r.width + 2) ++ rowProgram (paddingRows r) 0) ++
      tail.map (sourceInstruction r)) E G at H
  obtain ⟨J, hprefix, htail⟩ := (LooseExec.append_iff _ _ _ _).mp H
  obtain ⟨F, hbefore, hpadding⟩ := (LooseExec.append_iff _ _ _ _).mp hprefix
  obtain ⟨D, hsource, hcleanup⟩ := (LooseExec.append_iff _ _ _ _).mp hbefore
  have hDE := hsource.subset
  have hFD := hcleanup.subset
  have hJF := hpadding.subset
  have hrowSource := hsource.source_rows r rows hlen hrows
  have hcleanData := hcleanup.rowProgram_sourceData r (by
    intro row hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    omega)
  have hpadData := hpadding.rowProgram_sourceData r (by
    intro row hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    have hh : r.height ≤ (wideReader r).outputHeight := by
      change r.height ≤ r.height + (wideReader r).length
      omega
    omega)
  have horth := hcleanup.cleanup_orthogonal r (fun q hq hy => hsouth q (hDE hq) hy)
  have htailSource := htail.source r tail
    (fun q hq hy => hrows q (hDE (hFD (hJF hq))) hy) (by
      intro i hi
      apply sourceOff_of_orthogonal r _ _ i (hbound i hi)
      intro q hq
      obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
      exact horth q (Finset.mem_filter.mpr ⟨hJF hq, hy⟩))
  rw [hpadData, hcleanData] at htailSource
  exact hrowSource.append htailSource

/-- The actual dense next-column vector, including all overpayments, transports backward. -/
private theorem next_loose_sound (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    (E : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    {G : Finset (Cell (dock r).outputHeight (dock r).outputWidth)}
    (H : LooseExec (Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail)
      (E.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) G) :
    ∃ F, LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows) ++ tail) (sourceData r E) F := by
  rw [← paddedUnturned_turned r rows hlen tail] at H
  obtain ⟨F, hF, _⟩ := H.unturn _ (paddedUnturned_bounded r rows hlen tail hbound) E
  exact ⟨sourceData r F, paddedUnturned_sound r rows hlen tail hbound hrows hsouth hF⟩

/-- A genuine turned dock observation retains the entire later whole-run source suffix. -/
theorem next_loose_finish (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    (finish : State (dock r).outputWidth (dock r).outputHeight)
    (hrows : ∀ q ∈ PushS.holes finish, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hsouth : ∀ q ∈ PushS.holes finish, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    {G : Finset (Cell (dock r).outputHeight (dock r).outputWidth)}
    (H : LooseExec (Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail)
      (PushS.holes ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state finish)) G) :
    ∃ F, LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows) ++ tail)
      (originalHoles r finish) F := by
  have hmap : PushS.holes ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state finish) =
      (PushS.holes finish).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight) := by
    ext q
    obtain ⟨p, rfl⟩ := (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells.surjective q
    simp only [PushS.mem_holes, PushFS.GridIsometry.mem_boxes, Finset.mem_map, turnEmbedding,
      Equiv.toEmbedding_apply, (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells.injective.eq_iff,
      exists_eq_right]
  rw [hmap] at H
  exact next_loose_sound r rows hlen tail hbound (PushS.holes finish) hrows hsouth H

end PushPuzzle.PushPush.Cyclic
