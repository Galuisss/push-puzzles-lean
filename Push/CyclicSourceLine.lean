/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicCommitSource
public import Push.ScanEmbedding
public import Mathlib.Data.List.Nodup

/-! Exact ordered source-line enumerations inside the larger physical cyclic board. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- The literal source rectangle as an injective cell map into the dock. -/
def sourceEmbedding (r : ColumnScan.Input) : Cell r.width r.height ↪
    Cell (dock r).outputWidth (dock r).outputHeight :=
  ⟨unturnedSourceEmbed r, fun _ _ he => (wideReader r).embed_injective ((dock r).embed_injective he)⟩

@[simp] theorem sourceEmbedding_x (r : ColumnScan.Input) (p : Cell r.width r.height) :
    ((sourceEmbedding r) p).1.val = p.1.val + 2 := rfl

@[simp] theorem sourceEmbedding_y (r : ColumnScan.Input) (p : Cell r.width r.height) :
    ((sourceEmbedding r) p).2.val = p.2.val := rfl

/-- Select exactly original source cells in the enlarged rectangle. -/
def sourceKeep (r : ColumnScan.Input) (p : Cell (dock r).outputWidth (dock r).outputHeight) : Bool :=
  decide (2 ≤ p.1.val ∧ p.1.val < r.width + 2 ∧ p.2.val < r.height)

/-- Columns translate by two; rows keep their coordinates. -/
def sourceLane (side : Direction) (lane : ℕ) : ℕ :=
  match side with
  | .north | .south => lane + 2
  | .east | .west => lane

private def positionShift : Direction → ℤ
  | .north | .south => 0
  | .east => 2
  | .west => -2

private theorem source_position (r : ColumnScan.Input) (side : Direction) (p : Cell r.width r.height) :
    side.position ((sourceEmbedding r) p) = side.position p + positionShift side := by
  cases side <;> simp only [Direction.position, sourceEmbedding_x, sourceEmbedding_y, positionShift] <;> omega

theorem sourceEmbedding_lane (r : ColumnScan.Input) (side : Direction) (p : Cell r.width r.height) :
    side.lane ((sourceEmbedding r) p) = sourceLane side (side.lane p) := by
  cases side <;> rfl

private theorem filtered_mem (r : ColumnScan.Input) (side : Direction) (lane : ℕ)
    (q : Cell (dock r).outputWidth (dock r).outputHeight) :
    q ∈ (Scan.lineCells side (sourceLane side lane)).filter (sourceKeep r) ↔
      q ∈ (Scan.lineCells (w := r.width) (h := r.height) side lane).map (sourceEmbedding r) := by
  constructor
  · intro hq
    obtain ⟨hline, hkeep⟩ := List.mem_filter.mp hq
    have hcoords := of_decide_eq_true hkeep
    have hlane := (Scan.mem_lineCells side _ q).mp hline
    let p : Cell r.width r.height :=
      (⟨q.1.val - 2, by omega⟩, ⟨q.2.val, hcoords.2.2⟩)
    have he : (sourceEmbedding r) p = q := by
      apply Prod.ext <;> apply Fin.ext
      · change q.1.val - 2 + 2 = q.1.val
        omega
      · rfl
    refine List.mem_map.mpr ⟨p, (Scan.mem_lineCells side lane p).mpr ?_, he⟩
    cases side <;> simp only [Direction.lane, sourceLane] at hlane ⊢ <;> dsimp [p] <;> omega
  · intro hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    apply List.mem_filter.mpr
    refine ⟨(Scan.mem_lineCells side _ _).mpr ?_, ?_⟩
    · rw [sourceEmbedding_lane, (Scan.mem_lineCells side lane p).mp hp]
    · apply decide_eq_true_eq.mpr
      have hx := p.1.isLt
      have hy := p.2.isLt
      change 2 ≤ p.1.val + 2 ∧ p.1.val + 2 < r.width + 2 ∧ p.2.val < r.height
      omega

/-- Filtering a physical line to the source rectangle preserves its precise original read order. -/
theorem source_line_filter (r : ColumnScan.Input) (side : Direction) (lane : ℕ) :
    (Scan.lineCells (w := (dock r).outputWidth) (h := (dock r).outputHeight)
      side (sourceLane side lane)).filter (sourceKeep r) =
      (Scan.lineCells (w := r.width) (h := r.height) side lane).map (sourceEmbedding r) := by
  have hp := List.perm_ext_iff_of_nodup
    ((Scan.lineCells_nodup side (sourceLane side lane)).filter (sourceKeep r))
    (List.Nodup.map (sourceEmbedding r).injective (Scan.lineCells_nodup side lane))
  have hperm := hp.mpr (filtered_mem r side lane)
  apply List.Perm.eq_of_pairwise (le := fun a b => side.position b < side.position a) _ _ _ hperm
  · intro a b ha hb hab hba
    omega
  · exact (Scan.lineCells_pairwise side _).filter (sourceKeep r)
  · apply (Scan.lineCells_pairwise side lane).map
    intro a b hab
    have hpa := source_position r side a
    have hpb := source_position r side b
    omega

end PushPuzzle.Push.Cyclic
