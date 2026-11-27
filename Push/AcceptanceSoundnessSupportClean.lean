/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramLayout
import all Push.Scan

/-! Zero-clear-loss actual traces preserve unread holes and remove all side-band alternatives. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Whole-line membership for an actual positive read block, independent of its target prefix spans. -/
def ReadTouches {w h : ℕ} (stage : Template) (q : Cell w h) : Prop :=
  match stage with
  | .read side requests => ∃ a ∈ requests, side.lane q = a.1
  | .clear .. => False

private theorem clean_card {w h : ℕ} {word : List (Scan.Instruction w h)} {E F : Finset (Cell w h)}
    (hc : Scan.ClearsEmpty word E) (he : Scan.eval word E = some F) : F.card + Scan.quota word = E.card := by
  induction word generalizing E with
  | nil => exact (Option.some.inj he) ▸ rfl
  | cons i rest ih =>
    obtain ⟨G, hi, hclear, htail⟩ := hc
    have ht : Scan.eval rest G = some F := by simpa only [Scan.eval, hi, Option.bind_some] using he
    have htailcard := ih htail ht
    have hhead : G.card + i.quota = E.card := by
      cases i with
      | read => exact Scan.consume_card hi
      | clear side lanes =>
        have hge : G = E := by
          apply Finset.Subset.antisymm (Scan.Instruction.eval_subset hi)
          intro q hq
          have hq' : q ∈ E.filter fun q => side.lane q ∉ lanes := Finset.mem_filter.mpr ⟨hq, hclear q hq⟩
          exact (Option.some.inj hi) ▸ hq'
        rw [hge]
        rfl
    simp only [Scan.quota, List.map_cons, List.sum_cons]
    change F.card + (i.quota + Scan.quota rest) = E.card
    omega

/-- If no preceding read uses a hole's whole line, zero-loss clears retain that hole. -/
theorem clean_unread_survives {w h : ℕ} (stages : List Template) (T E F : Finset (Cell w h))
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E)
    (he : Scan.eval (instructions (emit stages T).rounds) E = some F)
    {q : Cell w h} (hq : q ∈ E) (hunread : ∀ stage ∈ stages, ¬ReadTouches stage q) : q ∈ F := by
  induction stages generalizing T E with
  | nil => exact (Option.some.inj he) ▸ hq
  | cons stage rest ih =>
    have hinst : instructions (w := w) (h := h) (emit (stage :: rest) T).rounds =
        instructions (emit [stage] T).rounds ++ instructions (emit rest (emit [stage] T).remaining).rounds := by
      rw [show stage :: rest = [stage] ++ rest from rfl, emit_rounds_append, instructions, List.flatMap_append]
      rfl
    rw [hinst] at hc he
    obtain ⟨G, hG, hfirst, hrest⟩ := clean_append _ _ E hc
    rw [eval_append, hG, Option.bind_some] at he
    have hqG : q ∈ G := by
      cases stage with
      | read side requests =>
        by_contra hnot
        exact hunread _ List.mem_cons_self (read_block_removed_lane side requests T E G hG hq hnot)
      | clear side lanes =>
        have hkeep := clean_stage_keeps (.clear side lanes) T E hfirst hq
        exact (Option.some.inj hG) ▸ Finset.mem_filter.mpr ⟨hq, hkeep⟩
    exact ih _ G hrest he hqG (fun stage hm => hunread stage (List.mem_cons_of_mem _ hm))

/-- The first actual side-band clear deletes no input holes, so only the frame was removed. -/
theorem program_sideClear_remaining (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    sideClearHoles l p target (PushS.holes t) = PushS.holes t \ Boundary.frame := by
  have hfull := (program_clean_execution l p hl hM haxes initial target hr hs ha).2
  have hprefix : ∃ rest, schedule l p (targetHoles l p target \ Boundary.frame).card =
      sideClearSchedule l p target ++ rest := by
    unfold schedule preparation sideClearSchedule
    simp only [List.append_assoc, List.singleton_append]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hrest⟩ := hprefix
  unfold program at hfull
  rw [hrest, emit_rounds_append, instructions, List.flatMap_append] at hfull
  obtain ⟨F, hF, hclean, _⟩ := clean_append _ _ (PushS.holes t) hfull
  have hside := program_sideClear_eval l p target ha
  simp only [instructions] at hside
  have heq : F = sideClearHoles l p target (PushS.holes t) := Option.some.inj (hF.symm.trans hside)
  have hc := clean_card hclean hF
  have hquota : Scan.quota (instructions (w := p.W + 1) (h := p.H + 1)
      (emit (sideClearSchedule l p target) (targetHoles l p target)).rounds) =
      (Boundary.frame (w := p.W + 1) (h := p.H + 1)).card := by
    rw [sideClearSchedule, emit_rounds_append, instructions, List.flatMap_append]
    simp only [Scan.quota, List.map_append, List.sum_append]
    change Scan.quota (instructions (emit (frameSchedule p.W p.H) (targetHoles l p target)).rounds) + 0 = _
    rw [Nat.add_zero, (target_frame l p target).2]
    have hD : 0 < p.D := by have := p.outer_distance; omega
    exact (frame_card (Nat.mul_pos (by omega) hD) (by change 1 ≤ 2 * p.D; omega)).symm
  have hpart := Finset.card_sdiff_add_card_eq_card (program_accepts_frame l p target ha)
  have hsub : sideClearHoles l p target (PushS.holes t) ⊆ PushS.holes t \ Boundary.frame := Finset.filter_subset _ _
  apply Finset.eq_of_subset_of_card_le hsub
  change F.card + Scan.quota (instructions (w := p.W + 1) (h := p.H + 1)
      (emit (sideClearSchedule l p target) (targetHoles l p target)).rounds) = (PushS.holes t).card at hc
  rw [heq, hquota] at hc
  omega

/-- Away from the frame, the four new marker rows have no other accepted endpoint holes. -/
theorem program_new_rows_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t) (hf : q ∉ Boundary.frame)
    (hy : q.2.val ∈ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ)) : q ∈ newCentralMarkers l p := by
  have hq' : q ∈ sideClearHoles l p target (PushS.holes t) := by
    rw [program_sideClear_remaining l p hl hM haxes initial target hr hs ha]
    exact Finset.mem_sdiff.mpr ⟨hq, hf⟩
  have hD := p.outer_distance
  have hm := sideClearHoles_central_stock l p hl hM haxes initial target hr hp hs ha hq'
    (by simp only [Finset.mem_insert, Finset.mem_singleton] at hy; omega)
    (by simp only [Finset.mem_insert, Finset.mem_singleton] at hy; omega)
  apply Finset.mem_filter.mpr
  refine ⟨hm, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  omega

end PushPuzzle.Push.AcceptanceSoundness
