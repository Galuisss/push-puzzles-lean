/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportTrace
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgram
import all Push.Scan

/-! Genuine first-payment attribution by actual compact schedule blocks. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- The literal coordinate restriction of a preceding compact clear block. -/
def RoundClearKeeps {w h : ℕ} (stage : Template) (q : Cell w h) : Prop :=
  match stage with
  | .read .. => True
  | .clear side lanes => side.lane q ∉ lanes

private theorem clean_append {w h : ℕ} (left right : List (Scan.Instruction w h)) (E : Finset (Cell w h))
    (hc : Scan.ClearsEmpty (left ++ right) E) :
    ∃ F, Scan.eval left E = some F ∧ Scan.ClearsEmpty left E ∧ Scan.ClearsEmpty right F := by
  induction left generalizing E with
  | nil => exact ⟨E, rfl, trivial, hc⟩
  | cons i left ih =>
    obtain ⟨F, hi, hclear, htail⟩ := hc
    obtain ⟨G, hG, hcleft, hcright⟩ := ih F htail
    exact ⟨G, by simp only [Scan.eval, hi, Option.bind_some]; exact hG, ⟨F, hi, hclear, hcleft⟩, hcright⟩

private theorem clean_stage_keeps {w h : ℕ} (stage : Template) (T E : Finset (Cell w h))
    (hc : Scan.ClearsEmpty (instructions (emit [stage] T).rounds) E) {q : Cell w h} (hq : q ∈ E) :
    RoundClearKeeps stage q := by
  cases stage with
  | read => trivial
  | clear side lanes =>
    obtain ⟨_, _, hclear, _⟩ := hc
    exact hclear q hq

private theorem read_block_removed_lane {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T E F : Finset (Cell w h)) (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    {q : Cell w h} (hq : q ∈ E) (hqF : q ∉ F) : ∃ request ∈ requests, side.lane q = request.1 := by
  let region : Finset (Cell w h) := Finset.univ.filter fun q => side.lane q ∈ requests.map Prod.fst
  have hsupport : ∀ i ∈ instructions (w := w) (h := h) (emit [.read side requests] T).rounds,
      ∃ side lane quota, i = Scan.Instruction.read side lane quota ∧
        ∀ q ∈ Scan.lineCells (w := w) (h := h) side lane, q ∈ region := by
    intro i hi
    simp only [emit, instructions, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    refine ⟨side, a.1, a.2, rfl, ?_⟩
    intro q hq
    have hm : a.1 ∈ (emitReads side requests T).quotas.map Prod.fst := List.mem_map.mpr ⟨a, ha, rfl⟩
    rw [emitted_lanes] at hm
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Scan.mem_lineCells side a.1 q).mp hq ▸ hm⟩
  have h := read_support hsupport he
  have hmem := (Finset.mem_filter.mp (h.2.2 (Finset.mem_sdiff.mpr ⟨hq, hqF⟩))).2
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
  exact ⟨a, ha, heq.symm⟩

/-- A genuine deleting read round, after its actual preceding execution and all zero-loss clears. -/
structure RoundPayment {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (q : Cell w h) where
  before : List Template
  after : List Template
  side : Direction
  requests : List (ℕ × ℕ)
  input : Finset (Cell w h)
  output : Finset (Cell w h)
  split : stages = before ++ .read side requests :: after
  prefix_eval : Scan.eval (instructions (emit before T).rounds) E = some input
  read_eval : Scan.eval (instructions (emit [.read side requests] (emit before T).remaining).rounds) input = some output
  present : q ∈ input
  removed : q ∉ output
  clears : ∀ stage ∈ before, RoundClearKeeps stage q
  on_line : ∃ request ∈ requests, side.lane q = request.1

/-- Every paid hole is attributed to its actual compact read block and its prior clear restrictions. -/
theorem round_payment {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h))
    (he : Scan.eval (instructions (emit stages T).rounds) E = some ∅)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) {q : Cell w h} (hq : q ∈ E) :
    Nonempty (RoundPayment stages T E q) := by
  induction stages generalizing T E with
  | nil =>
    have heq : E = ∅ := Option.some.inj he
    exact (Finset.notMem_empty q (heq ▸ hq)).elim
  | cons stage rest ih =>
    have hinst : instructions (w := w) (h := h) (emit (stage :: rest) T).rounds =
        instructions (emit [stage] T).rounds ++ instructions (emit rest (emit [stage] T).remaining).rounds := by
      rw [show stage :: rest = [stage] ++ rest from rfl, emit_rounds_append, instructions, List.flatMap_append]
      rfl
    rw [hinst] at hc he
    obtain ⟨F, hF, hfirst, hrest⟩ := clean_append _ _ E hc
    rw [eval_append, hF, Option.bind_some] at he
    by_cases hqF : q ∈ F
    · obtain ⟨pay⟩ := ih _ F he hrest hqF
      have hremain : (emit (stage :: pay.before) T).remaining = (emit pay.before (emit [stage] T).remaining).remaining := by
        exact emit_remaining_append [stage] pay.before T
      refine ⟨{
        before := stage :: pay.before, after := pay.after, side := pay.side, requests := pay.requests,
        input := pay.input, output := pay.output,
        split := congrArg (List.cons stage) pay.split,
        prefix_eval := ?_, read_eval := ?_, present := pay.present, removed := pay.removed,
        clears := ?_, on_line := pay.on_line }⟩
      · rw [show stage :: pay.before = [stage] ++ pay.before from rfl,
          emit_rounds_append, instructions, List.flatMap_append, eval_append]
        have hF' := hF
        simp only [instructions] at hF'
        rw [hF', Option.bind_some]
        exact pay.prefix_eval
      · rw [hremain]
        exact pay.read_eval
      · intro prior hprior
        rcases List.mem_cons.mp hprior with heq | hprior
        · subst prior
          exact clean_stage_keeps stage T E hfirst hq
        · exact pay.clears prior hprior
    · cases stage with
      | read side requests =>
        exact ⟨⟨[], rest, side, requests, E, F, rfl, rfl, hF, hq, hqF, by simp,
          read_block_removed_lane side requests T E F hF hq hqF⟩⟩
      | clear side lanes =>
        have hkeep := clean_stage_keeps (.clear side lanes) T E hfirst hq
        have hrem : F = E.filter fun q => side.lane q ∉ lanes := (Option.some.inj hF).symm
        exact (hqF (hrem ▸ Finset.mem_filter.mpr ⟨hq, hkeep⟩)).elim

private theorem read_lines_before_retained {w h : ℕ} (side : Direction) (quotas : List (ℕ × ℕ))
    {E F : Finset (Cell w h)}
    (he : Scan.eval (quotas.map fun a => Scan.Instruction.read side a.1 a.2) E = some F)
    {a b : Cell w h} (ha : a ∈ F) (hb : b ∈ E) (hbf : b ∉ F) (hlane : side.lane a = side.lane b) :
    prefixRank side b < prefixRank side a := by
  induction quotas generalizing E with
  | nil => exact (hbf ((Option.some.inj he) ▸ hb)).elim
  | cons request rest ih =>
    obtain ⟨G, hhead, htail⟩ := Option.bind_eq_some_iff.mp he
    by_cases hbg : b ∈ G
    · exact ih htail hbg
    · have hag := scan_subset htail ha
      have hblane : side.lane b = request.1 := by
        by_contra hn
        exact hbg ((Scan.Instruction.read_outside hhead hn).mpr hb)
      exact read_deleted_before_retained hhead hag (hlane.trans hblane) hb hbg

/-- A marker retained by a whole same-direction round bounds each real payment on its line. -/
theorem round_deleted_before_retained {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T : Finset (Cell w h)) {E F : Finset (Cell w h)}
    (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    {a b : Cell w h} (ha : a ∈ F) (hb : b ∈ E) (hbf : b ∉ F) (hlane : side.lane a = side.lane b) :
    prefixRank side b < prefixRank side a := by
  simp only [emit, instructions, List.flatMap_cons, List.flatMap_nil, List.append_nil, Round.instructions] at he
  exact read_lines_before_retained side _ he ha hb hbf hlane

/-- The payment's output is the actual residual after its whole deleting round. -/
theorem RoundPayment.output_eval {w h : ℕ} {stages : List Template} {T E : Finset (Cell w h)}
    {q : Cell w h} (pay : RoundPayment stages T E q) :
    Scan.eval (instructions (emit (pay.before ++ [.read pay.side pay.requests]) T).rounds) E = some pay.output := by
  rw [emit_rounds_append, instructions, List.flatMap_append, eval_append]
  have hh := pay.prefix_eval
  simp only [instructions] at hh
  rw [hh, Option.bind_some]
  exact pay.read_eval

end PushPuzzle.Push.AcceptanceSoundness
