/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgram
public import PushS.Boundary
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFrame
import all Push.AcceptanceProgramRounds
import all Push.Scan

/-! The literal first two reader rounds force an arbitrary accepted hole set to contain the frame. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

private theorem read_support {w h : ℕ} {program : List (Scan.Instruction w h)}
    {E F region : Finset (Cell w h)}
    (hs : ∀ i ∈ program, ∃ side lane quota, i = .read side lane quota ∧
      ∀ q ∈ Scan.lineCells (w := w) (h := h) side lane, q ∈ region)
    (hp : Scan.eval program E = some F) :
    F ⊆ E ∧ F.card + Scan.quota program = E.card ∧ E \ F ⊆ region := by
  induction program generalizing E with
  | nil =>
    simp only [Scan.eval, Option.some.injEq] at hp
    subst F
    exact ⟨Finset.Subset.refl _, by rfl, by simp⟩
  | cons i program ih =>
    obtain ⟨side, lane, quota, rfl, hline⟩ := hs i List.mem_cons_self
    obtain ⟨G, hi, ht⟩ := Option.bind_eq_some_iff.mp hp
    have htail := ih (fun j hj => hs j (List.mem_cons_of_mem _ hj)) ht
    have hG := Scan.consume_subset hi
    have hc := Scan.consume_card hi
    refine ⟨htail.1.trans hG, ?_, ?_⟩
    · simp only [Scan.quota, List.map_cons, List.sum_cons, Scan.Instruction.quota]
      change F.card + (quota + Scan.quota program) = E.card
      omega
    · intro q hq
      obtain ⟨hqE, hqF⟩ := Finset.mem_sdiff.mp hq
      by_cases hqG : q ∈ G
      · exact htail.2.2 (Finset.mem_sdiff.mpr ⟨hqG, hqF⟩)
      · apply hline q
        by_contra hnot
        exact hqG ((Scan.consume_outside hi hnot).mpr hqE)

private theorem frame_read_support (W H : ℕ) (T : Finset (Cell (W + 1) (H + 1))) :
    ∀ i ∈ instructions (w := W + 1) (h := H + 1) (emit (frameSchedule W H) T).rounds,
      ∃ side lane quota, i = Scan.Instruction.read side lane quota ∧
        ∀ q ∈ Scan.lineCells (w := W + 1) (h := H + 1) side lane, q ∈ Boundary.frame := by
  intro i hi
  simp only [frameSchedule, emit, emitReads, instructions, Round.instructions, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, _, _, rfl, ?_⟩
  all_goals
    intro q hq
    have hh := (Scan.mem_lineCells _ _ q).mp hq
    simp only [Direction.lane] at hh
    simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- Paying the actual two frame rounds forces every frame cell to be an input hole. -/
theorem frame_eval_remainder {W H : ℕ} (hW : 1 ≤ W) (hH : 1 ≤ H)
    {T E : Finset (Cell (W + 1) (H + 1))} (hT : Boundary.frame ⊆ T)
    {F : Finset (Cell (W + 1) (H + 1))}
    (hF : Scan.eval (instructions (emit (frameSchedule W H) T).rounds) E = some F) :
    F = E \ Boundary.frame ∧ Boundary.frame ⊆ E := by
  have hs := read_support (frame_read_support W H T) hF
  have hquota := frame_quota hW hH T hT
  have hcard := Finset.card_sdiff_add_card_eq_card hs.1
  have hframe := frame_card hW hH
  have heq : E \ F = Boundary.frame := Finset.eq_of_subset_of_card_le hs.2.2 (by omega)
  constructor
  · ext q
    rw [← heq]
    simp only [Finset.mem_sdiff]
    constructor
    · intro hq
      exact ⟨hs.1 hq, by tauto⟩
    · tauto
  · intro q hq
    exact (Finset.mem_sdiff.mp (heq.symm ▸ hq)).1

/-- Any successful execution of the actual two frame rounds starts with the full frame. -/
private theorem frame_subset_of_accepts {W H : ℕ} (hW : 1 ≤ W) (hH : 1 ≤ H)
    {T E : Finset (Cell (W + 1) (H + 1))} (hT : Boundary.frame ⊆ T)
    (haccept : Scan.Accepts (instructions (emit (frameSchedule W H) T).rounds) E) :
    Boundary.frame ⊆ E := by
  obtain ⟨F, hF⟩ := haccept
  exact (frame_eval_remainder hW hH hT hF).2

private theorem emit_rounds_append {w h : ℕ} (left right : List Template) (T : Finset (Cell w h)) :
    (emit (left ++ right) T).rounds =
      (emit left T).rounds ++ (emit right (emit left T).remaining).rounds := by
  induction left generalizing T with
  | nil => rfl
  | cons stage left ih =>
    cases stage <;> simpa only [List.cons_append, emit] using (congrArg (List.cons _) (ih _))

private theorem accepts_emitted_prefix {w h : ℕ} (left right : List Template)
    (T E : Finset (Cell w h))
    (ha : Scan.Accepts (instructions (emit (left ++ right) T).rounds) E) :
    Scan.Accepts (instructions (emit left T).rounds) E := by
  obtain ⟨F, hF⟩ := ha
  rw [emit_rounds_append, instructions, List.flatMap_append, eval_append] at hF
  obtain ⟨G, hG, _⟩ := Option.bind_eq_some_iff.mp hF
  exact ⟨G, hG⟩

/-- Acceptance by the full literal program already pays its frame prefix. -/
theorem program_accepts_frame (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {E : Finset (Cell (p.W + 1) (p.H + 1))}
    (ha : Scan.Accepts (instructions (program l p target).rounds) E) : Boundary.frame ⊆ E := by
  have hprefix : ∃ rest, schedule l p (targetHoles l p target \ Boundary.frame).card =
      frameSchedule p.W p.H ++ rest := by
    unfold schedule preparation
    simp only [List.append_assoc]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hrest⟩ := hprefix
  unfold program at ha
  rw [hrest] at ha
  have hD : 0 < p.D := by have := p.outer_distance; omega
  have hW : 1 ≤ p.W := Nat.mul_pos (by omega) hD
  have hH : 1 ≤ p.H := by change 1 ≤ 2 * p.D; omega
  exact frame_subset_of_accepts hW hH (l.encodedSegments_frame_subset p (l.canonical target))
    (accepts_emitted_prefix _ _ _ _ ha)

/-- An arbitrary terminal configuration accepted by the actual reader has no frame box. -/
theorem program_frame_empty (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Disjoint t.boxes Boundary.frame := by
  apply Finset.disjoint_left.mpr
  intro q hbox hframe
  exact (PushS.mem_holes _).mp (program_accepts_frame l p target ha hframe) hbox

/-- The frame is empty at the start of every suffix ending in an accepted configuration. -/
private theorem reachable_frame_empty (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {u t : State (p.W + 1) (p.H + 1)}
    (hut : Reachable B cap u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Disjoint u.boxes Boundary.frame :=
  Boundary.reachable_frame_empty hut (program_frame_empty l p target ha)

/-- The genuine canonical physical play keeps the complete frame empty at every solution prefix. -/
theorem canonical_frame_empty_at (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {u t : State (p.W + 1) (p.H + 1)}
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Disjoint u.boxes Boundary.frame := reachable_frame_empty l p target hut ha

end PushPuzzle.Push.AcceptanceSoundness
