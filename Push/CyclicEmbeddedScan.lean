/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicSourceLine

/-! Static source reads and clears ignore auxiliary holes outside their selected source lines. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem sourceKeep_embedding (r : ColumnScan.Input) (p : Cell r.width r.height) :
    sourceKeep r ((sourceEmbedding r) p) = true := by
  apply decide_eq_true_eq.mpr
  have hx := p.1.isLt
  have hy := p.2.isLt
  change 2 ≤ p.1.val + 2 ∧ p.1.val + 2 < r.width + 2 ∧ p.2.val < r.height
  omega

/-- Exact source-line consumption commutes with the actual translated rectangle embedding. -/
private theorem consume_source_line (r : ColumnScan.Input) (side : Direction) (lane quota : ℕ)
    (E : Finset (Cell r.width r.height)) :
    Scan.consume (Scan.lineCells side (sourceLane side lane)) quota (E.map (sourceEmbedding r)) =
      (Scan.consume (Scan.lineCells side lane) quota E).map (Finset.map (sourceEmbedding r)) := by
  have hfilter := Scan.consume_filter (sourceKeep r)
    (Scan.lineCells side (sourceLane side lane)) quota (E.map (sourceEmbedding r)) (by
      intro q hline hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      exact sourceKeep_embedding r p)
  rw [source_line_filter] at hfilter
  exact hfilter.symm.trans (Scan.consume_map (sourceEmbedding r) _ _ _)

/-- A translated source read leaves all off-line auxiliary holes unchanged. -/
theorem read_source_with_aux (r : ColumnScan.Input) (side : Direction) (lane quota : ℕ)
    (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : ∀ q ∈ A, side.lane q ≠ sourceLane side lane) :
    (Scan.Instruction.read side (sourceLane side lane) quota).eval (E.map (sourceEmbedding r) ∪ A) =
      ((Scan.Instruction.read side lane quota).eval E).map (fun F => F.map (sourceEmbedding r) ∪ A) := by
  change Scan.consume (Scan.lineCells side (sourceLane side lane)) quota _ = _
  rw [Scan.consume_union _ _ _ _ (by
    intro q hq ha
    exact hA q ha ((Scan.mem_lineCells side _ q).mp hq))]
  rw [consume_source_line, Option.map_map]
  rfl

private theorem sourceLane_injective (side : Direction) : Function.Injective (sourceLane side) := by
  intro a b hab
  cases side <;> simp only [sourceLane] at hab <;> omega

/-- Clearing translated source lines also leaves off-line auxiliary inventory unchanged. -/
private theorem clear_source_with_aux (r : ColumnScan.Input) (side : Direction) (lanes : Finset ℕ)
    (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : ∀ q ∈ A, side.lane q ∉ lanes.image (sourceLane side)) :
    (Scan.Instruction.clear side (lanes.image (sourceLane side))).eval (E.map (sourceEmbedding r) ∪ A) =
      ((Scan.Instruction.clear side lanes).eval E).map (fun F => F.map (sourceEmbedding r) ∪ A) := by
  change some ((E.map (sourceEmbedding r) ∪ A).filter _) = some _
  congr 1
  rw [Finset.filter_union, Finset.filter_map]
  have haux : A.filter (fun q => side.lane q ∉ lanes.image (sourceLane side)) = A :=
    Finset.filter_eq_self.mpr hA
  rw [haux]
  congr 1
  congr 1
  ext q
  simp only [Finset.mem_filter, Function.comp_apply, sourceEmbedding_lane, Finset.mem_image,
    (sourceLane_injective side).eq_iff, exists_eq_right]

/-- Translate every selected original source line into its actual dock coordinate. -/
def sourceInstruction (r : ColumnScan.Input) : Scan.Instruction r.width r.height →
    Scan.Instruction (dock r).outputWidth (dock r).outputHeight
  | .read side lane quota => .read side (sourceLane side lane) quota
  | .clear side lanes => .clear side (lanes.image (sourceLane side))

/-- No auxiliary hole lies on a line selected by this original source instruction. -/
def SourceOff (r : ColumnScan.Input) (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight)) :
    Scan.Instruction r.width r.height → Prop
  | .read side lane _ => ∀ q ∈ A, side.lane q ≠ sourceLane side lane
  | .clear side lanes => ∀ q ∈ A, side.lane q ∉ lanes.image (sourceLane side)

/-- The number of original source lines perpendicular to a given reading direction. -/
def sourceLaneBound (r : ColumnScan.Input) : Direction → ℕ
  | .north | .south => r.width
  | .east | .west => r.height

/-- The source instruction names actual source rows or columns. -/
def SourceBounded (r : ColumnScan.Input) : Scan.Instruction r.width r.height → Prop
  | .read side lane _ => lane < sourceLaneBound r side
  | .clear side lanes => ∀ lane ∈ lanes, lane < sourceLaneBound r side

/-- Auxiliary holes lie on neither an original source row nor an original source column. -/
def SourceOrthogonal (r : ColumnScan.Input)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight)) : Prop :=
  ∀ q ∈ A, r.height ≤ q.2.val ∧ (q.1.val < 2 ∨ r.width + 2 ≤ q.1.val)

private theorem source_read_off (r : ColumnScan.Input)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : SourceOrthogonal r A) (side : Direction) (lane : ℕ) (hl : lane < sourceLaneBound r side) :
    ∀ q ∈ A, side.lane q ≠ sourceLane side lane := by
  intro q hq he
  obtain ⟨hy, hx⟩ := hA q hq
  cases side <;> simp only [sourceLaneBound, Direction.lane, sourceLane] at hl he <;> omega

/-- Orthogonal auxiliary inventory is off every line of every bounded source instruction. -/
theorem sourceOff_of_orthogonal (r : ColumnScan.Input)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : SourceOrthogonal r A) (i : Scan.Instruction r.width r.height) (hi : SourceBounded r i) :
    SourceOff r A i := by
  cases i with
  | read side lane quota => exact source_read_off r A hA side lane hi
  | clear side lanes =>
    intro q hq hm
    obtain ⟨lane, hl, he⟩ := Finset.mem_image.mp hm
    exact source_read_off r A hA side lane (hi lane hl) q hq he.symm

/-- An entire static source program transports with the same untouched auxiliary inventory. -/
theorem source_program_eval (r : ColumnScan.Input) (program : List (Scan.Instruction r.width r.height))
    (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : ∀ i ∈ program, SourceOff r A i) :
    Scan.eval (program.map (sourceInstruction r)) (E.map (sourceEmbedding r) ∪ A) =
      (Scan.eval program E).map (fun F => F.map (sourceEmbedding r) ∪ A) := by
  induction program generalizing E with
  | nil => rfl
  | cons i rest ih =>
    have hi : (sourceInstruction r i).eval (E.map (sourceEmbedding r) ∪ A) =
        (i.eval E).map (fun F => F.map (sourceEmbedding r) ∪ A) := by
      cases i with
      | read side lane quota => exact read_source_with_aux r side lane quota E A (hA _ (List.mem_cons_self ..))
      | clear side lanes => exact clear_source_with_aux r side lanes E A (hA _ (List.mem_cons_self ..))
    simp only [List.map_cons, Scan.eval]
    rw [hi]
    cases he : i.eval E with
    | none => simp only [Option.map_none, Option.bind_none]
    | some F =>
      simp only [Option.map_some, Option.bind_some]
      exact ih F (fun j hj => hA j (List.mem_cons_of_mem i hj))

/-- Acceptance depends only on the source data once auxiliary holes avoid the selected lines. -/
theorem source_program_accepts_iff (r : ColumnScan.Input)
    (program : List (Scan.Instruction r.width r.height)) (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : ∀ i ∈ program, SourceOff r A i) :
    Scan.Accepts (program.map (sourceInstruction r)) (E.map (sourceEmbedding r) ∪ A) ↔
      Scan.Accepts program E := by
  unfold Scan.Accepts
  rw [source_program_eval r program E A hA]
  cases he : Scan.eval program E <;> simp

end PushPuzzle.Push.Cyclic
