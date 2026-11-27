/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombConfiguration
import all PushS.CombConfiguration
public import PushS.CombNumbering
public import PushS.CombUpperVisits
import all PushS.CombUpperVisits

/-!
# Exact original direction readout in the actual contour

The actual segment query returns each crossing's original traversal direction. Contour ranks
read the exact emitted token bits, so original incidences and the two sides of each genuine
crossing retain their intended source directions.

## Main results

* `Comb.ConfigurationInput.axes_rank`: exact emitted direction at the actual contour rank.
* `Comb.ConfigurationInput.tokenBit_crossing`: same original direction and actual crossing side.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

/-- The runtime prepared-segment query is exactly an actual crossing's traversal direction. -/
private theorem segmentForward_crossing (width : ℕ) (d : Graph.OrthogonalDrawing)
    {c : Crossing} (hc : c ∈ crossings width d) (g : NCL.AndOrGraph) :
    segmentForward width ⟨g, d⟩ c.edge c.segment = c.forward := by
  obtain ⟨r, ab, site, hr, hab, _, _, _, hf⟩ := (mem_crossings_iff width d c).mp hc
  unfold segmentForward
  rw [List.getD_eq_getElem?_getD, hr, Option.getD_some]
  dsimp only
  rw [List.getD_eq_getElem?_getD, hab, Option.getD_some]
  exact hf.symm

/-- The original native port receives inflow exactly when its emitted core axis is false. -/
theorem ConfigurationInput.portBit_eq_false (x : ConfigurationInput) (p : NCL.Port ℕ) :
    x.portBit p = false ↔ x.bits.getD p.edge false = p.dir := by
  unfold ConfigurationInput.portBit
  cases x.bits.getD p.edge false <;> cases p.dir <;> decide

/-- A genuine crossing side carries the same original native direction and its actual side. -/
theorem ConfigurationInput.tokenBit_crossing (width : ℕ) (x : ConfigurationInput)
    {c : Crossing} (hc : c ∈ crossings width x.input.drawing) (side : Bool) :
    x.tokenBit width (c.token side) = (x.bits.getD c.edge false ^^ (c.forward ^^ side)) := by
  change (x.bits.getD c.edge false ^^
    (segmentForward width x.input c.edge c.segment ^^ side)) = _
  have h := segmentForward_crossing width x.input.drawing hc x.input.graph
  exact congrArg (fun b => x.bits.getD c.edge false ^^ (b ^^ side)) h

/-- The two actual sides of the same genuine tooth crossing carry complementary axis bits. -/
theorem ConfigurationInput.tokenBit_crossing_sides (width : ℕ) (x : ConfigurationInput)
    {c : Crossing} (hc : c ∈ crossings width x.input.drawing) :
    x.tokenBit width (c.token false) = !(x.tokenBit width (c.token true)) := by
  rw [x.tokenBit_crossing width hc false, x.tokenBit_crossing width hc true]
  cases x.bits.getD c.edge false <;> cases c.forward <;> rfl

/-- The actual emitted contour rank reads precisely its same original token bit. -/
theorem ConfigurationInput.axes_rank (width : ℕ) (x : ConfigurationInput) {token : Token}
    (ht : token ∈ (cut width x.input).order) :
    (x.axes width).getD ((cut width x.input).rank token) false = x.tokenBit width token := by
  have hi := (cut width x.input).rank_lt ht
  unfold ConfigurationInput.axes
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
  simp only [List.getElem_map, Cut.rank]
  exact congrArg (x.tokenBit width) (List.getElem_idxOf hi)

/-- In original traversal order, every actual crossing contributes the complementary then
original source direction. -/
private theorem ConfigurationInput.crossingWord_bits (width : ℕ) (x : ConfigurationInput)
    {c : Crossing} (hc : c ∈ crossings width x.input.drawing) :
    ((if c.forward then [c.token false, c.token true] else [c.token true, c.token false]).map
      (x.tokenBit width)) = [!(x.bits.getD c.edge false), x.bits.getD c.edge false] := by
  cases hf : c.forward <;>
    simp only [hf, Bool.false_eq_true, ite_false, ite_true, List.map_cons, List.map_nil,
      x.tokenBit_crossing width hc false, x.tokenBit_crossing width hc true] <;>
    cases x.bits.getD c.edge false <;> rfl

private theorem alternating (b : Bool) (n : ℕ) :
    (b :: (List.replicate n [!b, b]).flatten ++ [!b]).IsChain (· ≠ ·) := by
  induction n with
  | zero => cases b <;> simp
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append]
    exact List.isChain_cons_cons.mpr ⟨by cases b <;> decide,
      List.isChain_cons_cons.mpr ⟨by cases b <;> decide, ih⟩⟩

/-- The entire actual original-edge visit word alternates its same native direction bits. -/
theorem ConfigurationInput.edgeVisits_alternate (width : ℕ) (x : ConfigurationInput) (edge : ℕ) :
    (edgeVisits width x.input.drawing edge).IsChain
      (fun a b => x.tokenBit width a ≠ x.tokenBit width b) := by
  let bit := x.bits.getD edge false
  let hits := edgeCrossings width x.input.drawing edge
  have hc (c : Crossing) (hm : c ∈ hits) :
      (crossingWord c).map (x.tokenBit width) = [!bit, bit] := by
    obtain ⟨hm, he⟩ := List.mem_filter.mp ((edgeCrossings_perm width x.input.drawing edge).mem_iff.mp hm)
    have hb := x.crossingWord_bits width hm
    simpa only [crossingWord, of_decide_eq_true he] using hb
  have hflat (cs : List Crossing)
      (hcs : ∀ c ∈ cs, (crossingWord c).map (x.tokenBit width) = [!bit, bit]) :
      (cs.flatMap crossingWord).map (x.tokenBit width) =
        (List.replicate cs.length [!bit, bit]).flatten := by
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.flatMap_cons, List.map_append, List.length_cons, List.replicate_succ,
        List.flatten_cons, hcs c List.mem_cons_self]
      rw [ih (fun c hm => hcs c (List.mem_cons_of_mem _ hm))]
  have hm : (edgeVisits width x.input.drawing edge).map (x.tokenBit width) =
      bit :: (List.replicate hits.length [!bit, bit]).flatten ++ [!bit] := by
    change (([Token.tip edge false] ++ hits.flatMap crossingWord ++ [Token.tip edge true]).map
      (x.tokenBit width)) = _
    simp only [List.map_append, List.map_cons, List.map_nil, hflat hits hc,
      ConfigurationInput.tokenBit, ConfigurationInput.portBit, Bool.xor_false, Bool.xor_true,
      List.singleton_append]
    rfl
  rw [← List.isChain_map, hm]
  exact alternating bit hits.length

private theorem pairOff_supplied (value : Token → Bool) (tokens : List Token)
    (hc : tokens.IsChain (fun a b => value a ≠ value b)) (he : tokens.length % 2 = 0) :
    ∀ pair ∈ pairOff tokens, value pair.1 = true ∨ value pair.2 = true := by
  induction tokens using List.twoStepInduction with
  | nil => simp [pairOff]
  | singleton a => simp at he
  | cons_cons a b tail ih =>
    rw [pairOff_cons_cons]
    intro pair hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have hn := hc.rel
      cases ha : value a <;> cases hb : value b <;> simp_all
    · have het : tail.length % 2 = 0 := by simp only [List.length_cons] at he; omega
      exact ih hc.tail.tail het pair hp

/-- Every actual upper fragment receives supply from at least one of its two original axes. -/
theorem ConfigurationInput.upperFragment_supplied (width : ℕ) (x : ConfigurationInput) (edge : ℕ)
    {pair : Token × Token} (hp : pair ∈ pairOff (edgeVisits width x.input.drawing edge)) :
    x.tokenBit width pair.1 = true ∨ x.tokenBit width pair.2 = true :=
  pairOff_supplied (x.tokenBit width) _ (x.edgeVisits_alternate width edge)
    (edgeVisits_length_even width x.input.drawing edge) pair hp

end PushPuzzle.PushS.Comb
