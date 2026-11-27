/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortPublicWalkBudget
public import PushS.PortStreetSupport
import all PushS.PortPublicWalkBudget
import all PushS.EndpointMacros
import all PushS.PortSegments
import all PushS.PortStreetSupport
import all PushS.PortEndpointCounts
import all PushS.PortLayoutCoordinates
import all PushS.Support
import all PushS.Scales
import all PushS.PortCentralStrip
import all PushS.PortEndpointCrossing

/-! Every departure from an actual public corridor is on the frame or near a selected row. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The frame and the selected rows with their immediate vertical neighbours. -/
@[expose] def publicWalkExitSet (l : PortLayout) (p : Scales.Parameters) :
    Set (Cell (p.W + 1) (p.H + 1)) :=
  {a | a ∈ Boundary.frame ∨ ∃ y ∈ l.workingRowSet p, Nat.dist a.2.val y.val ≤ 1}

private theorem vertical_public_segment_exit (l : PortLayout) (p : Scales.Parameters)
    (side : Side) (x limit : ℕ) (hlo : 1 ≤ limit) (hhi : limit + 1 < p.H)
    (hmem : segment x (onSide (coordinates p) side 1) x (onSide (coordinates p) side limit) ∈
      l.allPublicWalkSegments p)
    {a b : Cell (p.W + 1) (p.H + 1)} {d : Direction} (hd : d = .north ∨ d = .south)
    (hac : (segment x (onSide (coordinates p) side 1) x (onSide (coordinates p) side limit)).Contains
      (a.1.val, a.2.val)) (hadj : Adjacent d a b) (hout : b ∉ l.allPublicWalkHoles p) :
    a.2.val = onSide (coordinates p) side limit ∧
      b.2.val = onSide (coordinates p) side (limit + 1) := by
  have hc := (vertical_contains _ _ _ _).mp hac
  have hbx : b.1.val = x := by
    rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.1).trans hc.1
  have hnot : ¬(min (onSide (coordinates p) side 1) (onSide (coordinates p) side limit) ≤ b.2.val ∧
      b.2.val ≤ max (onSide (coordinates p) side 1) (onSide (coordinates p) side limit)) := by
    intro h
    apply hout
    exact Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ b).mpr
      ⟨_, hmem, (vertical_contains _ _ _ _).mpr ⟨hbx, h⟩⟩)
  have hb0 : b.2.val ≠ 0 := by
    intro hy
    apply hout (Finset.mem_union_left _ ((Boundary.mem_frame b).mpr ⟨.north, ?_⟩))
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hy]
  have hbH : b.2.val ≠ p.H := by
    intro hy
    apply hout (Finset.mem_union_left _ ((Boundary.mem_frame b).mpr ⟨.south, ?_⟩))
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hy]
  have hH : (coordinates p).H = p.H := rfl
  have haH := a.2.isLt
  have hbH' := b.2.isLt
  rcases hd with rfl | rfl <;> cases hs : side <;>
    simp only [Adjacent, onSide, hs, reduceCtorEq, ite_true, ite_false, hH] at hadj hc hnot ⊢ <;> omega

private theorem vertical_allPublic_exit (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    {a b : Cell (p.W + 1) (p.H + 1)} {d : Direction} (hd : d = .north ∨ d = .south)
    (hadj : Adjacent d a b) (hin : a ∈ l.allPublicWalkHoles p) (hout : b ∉ l.allPublicWalkHoles p) :
    a ∈ l.publicWalkExitSet p := by
  rcases Finset.mem_union.mp hin with hf | hw
  · exact Or.inl hf
  obtain ⟨s, hs, hac⟩ := (SegmentRecipe.mem_holes _ a).mp hw
  have hmem := hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
    have hY := readDepth_ge p hj hm
    have hH := readDepth_add_lt_H p e.level
    have hrows := workingRows_level l p hj hm
    simp only [endpointFixedSegments, List.cons_append, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · have he := vertical_public_segment_exit l p e.side _ (readDepth p e.level + 2)
        (by omega) (by omega) hmem hd hac hadj hout
      exact Or.inr ⟨a.2, l.mem_workingRowSet_of_onSide p hrows.2 e.side a.2 he.1, by simp⟩
    · have he := vertical_public_segment_exit l p e.side _ (readDepth p e.level - 1)
        (by omega) (by omega) hmem hd hac hadj hout
      have hy : b.2.val = onSide (coordinates p) e.side (readDepth p e.level) := by
        have hh : readDepth p e.level - 1 + 1 = readDepth p e.level := by omega
        simpa only [hh] using he.2
      refine Or.inr ⟨b.2, l.mem_workingRowSet_of_onSide p hrows.1 e.side b.2 hy, ?_⟩
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> simp only [Nat.dist] <;> omega
    · have hy := (horizontal_contains _ _ _ _ |>.mp hac).1
      exact Or.inr ⟨a.2, l.mem_workingRowSet_of_onSide p hrows.2 e.side a.2 hy, by simp⟩
  · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    let c := coordinates p
    have hs' : s ∈ ([c.x i - 2, c.x i + 6, c.x i + 8, c.x i + 12].map fun col =>
        segment col (onSide c .lower 1) col (onSide c .lower (c.depth 1 - 1))) := by
      simpa only [gateFixedSegments, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.take_succ_cons, List.take_zero] using hs
    obtain ⟨col, _, rfl⟩ := List.mem_map.mp hs'
    have hY := readDepth_ge p (j := 1) le_rfl p.levels_pos
    have hH := readDepth_add_lt_H p 1
    have he := vertical_public_segment_exit l p .lower col (readDepth p 1 - 1)
      (by omega) (by omega) hmem hd hac hadj hout
    have hy : b.2.val = p.H - readDepth p 1 := by
      have hh : readDepth p 1 - 1 + 1 = readDepth p 1 := by omega
      simpa only [hh] using (show b.2.val = p.H - (readDepth p 1 - 1 + 1) from he.2)
    refine Or.inr ⟨b.2, l.mem_workingRowSet_of_onSide p (workingRows_level l p le_rfl p.levels_pos).1
      .lower b.2 hy, ?_⟩
    rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> simp only [Nat.dist] <;> omega

/-- An actual supported step leaving all public walks departs at the frame or within one
vertical cell of an actual selected row. -/
theorem step_allPublicWalk_exit (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hm : Step B cap s t)
    (hs : s.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p))
    (ht : t.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p))
    (hin : s.player ∈ l.allPublicWalkHoles p) (hout : t.player ∉ l.allPublicWalkHoles p) :
    s.player ∈ l.publicWalkExitSet p := by
  obtain ⟨d, hmove⟩ := hm
  have hadj := players_adjacent hmove
  cases d with
  | north => exact vertical_allPublic_exit l p hl hM (Or.inl rfl) hadj hin hout
  | south => exact vertical_allPublic_exit l p hl hM (Or.inr rfl) hadj hin hout
  | east =>
    have hy := Support.horizontal_row (l.streetColumnSet_separated p) hs ht hadj.2 hadj.1.symm
    exact Or.inr ⟨s.player.2, hy, by simp⟩
  | west =>
    have hy := Support.horizontal_row (l.streetColumnSet_separated p) ht hs hadj.2.symm hadj.1
    exact Or.inr ⟨t.player.2, hy, by simp only [hadj.2, Nat.dist_self]; omega⟩

private theorem workingDepth_first_bound (l : PortLayout) (p : Scales.Parameters) {v : ℕ}
    (hv : v ∈ l.workingDepthCoordinates p) : 8 * p.Q - 2 ≤ v := by
  change v ∈ workingRows l (coordinates p) at hv
  obtain ⟨i, hi, hv⟩ := List.mem_flatMap.mp hv
  have hiM : i + 1 ≤ p.levels := by
    have hi := List.mem_range.mp hi
    change i < p.levels at hi
    omega
  have hraw : 8 * p.Q ≤ (coordinates p).depth (i + 1) := by
    change 8 * p.Q ≤ readDepth p (i + 1)
    rw [readDepth_eq p (by omega) hiM]
    exact p.Y_ge_A (i + 1)
  dsimp only at hv
  split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega

/-- Every actual public departure is farther than the final hole budget from the lower
half-depth row near any real port axis. -/
theorem publicWalkExitSet_halfDepth_far (l : PortLayout) (p : Scales.Parameters)
    (ha : l.portCount ≤ p.axes) {i : ℕ} (hi : i < l.portCount)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : p.x i - 12 ≤ q.1.val ∧ q.1.val ≤ p.x i + 12)
    (hy : q.2.val = p.H - readDepth p 1 / 2) :
    ∀ a ∈ l.publicWalkExitSet p, p.Q < distance a q := by
  have hY : readDepth p 1 = 8 * p.Q := by
    rw [readDepth_eq p le_rfl p.levels_pos]
    simp only [Scales.Parameters.Y, Scales.Parameters.A, show 2 * 1 - 2 = 0 by decide,
      pow_zero, Nat.mul_one]
  have hhalf : readDepth p 1 / 2 = 4 * p.Q := by omega
  rw [hhalf] at hy
  have hQ := p.Q_ge
  have hA := p.Y_ge_A p.levels
  change 8 * p.Q ≤ p.Y p.levels at hA
  have hmul := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
    (show 1 ≤ 8 * (p.axes + 1) by omega)
  simp only [Nat.one_mul] at hmul
  have hb : p.Y p.levels + 2 ≤ p.b p.levels := by unfold Scales.Parameters.b; omega
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  intro a haE
  rcases haE with hf | ⟨y, hrow, hnear⟩
  · have hleft : p.D ≤ p.x i := by
      have h := Nat.mul_le_mul_right p.D (show 1 ≤ i + 1 by omega)
      simpa only [Nat.one_mul, Scales.Parameters.x] using h
    have hright : p.x i + p.D ≤ p.W := by
      have h := axis_spacing p (hi.trans_le ha)
      simpa only [Scales.Parameters.x, Scales.Parameters.W] using h
    obtain ⟨d, hd⟩ := (Boundary.mem_frame a).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;>
      simp only [distance, Nat.dist_eq_max_sub_min] <;> omega
  · rcases (l.workingRowSet_iff p y).mp hrow with h0 | htop | ⟨v, hv, hvy⟩
    · simp only [Nat.dist, h0] at hnear
      simp only [distance, Nat.dist_eq_max_sub_min]
      omega
    · simp only [Nat.dist, htop] at hnear
      simp only [distance, Nat.dist_eq_max_sub_min]
      omega
    · have hvmin := workingDepth_first_bound l p hv
      have hvmax := workingRows_le_last l p hv
      rcases hvy with hvy | hvy <;> simp only [Nat.dist, hvy] at hnear <;>
        simp only [distance, Nat.dist_eq_max_sub_min] <;> omega

end PushPuzzle.PushS.PortLayout
