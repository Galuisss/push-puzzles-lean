/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentralStock
public import Push.AcceptanceProgramThirdClear
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramRegions
import all Push.AcceptanceProgramRounds
import all Push.Scan

/-! Whole-row quota saturation at a literal stage of the emitted acceptance program. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

private theorem scan_subset {w h : ℕ} {word : List (Scan.Instruction w h)} {E F : Finset (Cell w h)}
    (he : Scan.eval word E = some F) : F ⊆ E := by
  induction word generalizing E with
  | nil => exact (Option.some.inj he) ▸ Finset.Subset.refl _
  | cons i rest ih =>
    obtain ⟨G, hi, ht⟩ := Option.bind_eq_some_iff.mp he
    exact (ih ht).trans (Scan.Instruction.eval_subset hi)

private theorem emitted_split {w h : ℕ} (left right : List Template) (T E : Finset (Cell w h))
    (ha : Scan.Accepts (instructions (emit (left ++ right) T).rounds) E) :
    ∃ F, Scan.eval (instructions (emit left T).rounds) E = some F ∧
      Scan.Accepts (instructions (emit right (emit left T).remaining).rounds) F := by
  obtain ⟨G, hG⟩ := ha
  rw [emit_rounds_append, instructions, List.flatMap_append, eval_append] at hG
  obtain ⟨F, hF, ht⟩ := Option.bind_eq_some_iff.mp hG
  exact ⟨F, hF, G, ht⟩

private theorem emitted_lanes {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T : Finset (Cell w h)) : (emitReads side requests T).quotas.map Prod.fst = requests.map Prod.fst := by
  induction requests generalizing T with
  | nil => rfl
  | cons a rest ih => simp only [emitReads, List.map_cons, ih]

/-- A whole-row target block saturates any current hole stock contained in its target rows. -/
theorem row_saturation (p : Scales.Parameters) (side : Direction) (rows : Finset ℕ)
    (hside : side = .west ∨ side = .east) (T E : Finset (Cell (p.W + 1) (p.H + 1)))
    (hstock : (E.filter fun q => q.2.val ∈ rows) ⊆ T.filter fun q => q.2.val ∈ rows)
    (ha : Scan.Accepts (instructions (emit [readRows p side rows] T).rounds) E) :
    (T.filter fun q => q.2.val ∈ rows) ⊆ E := by
  let region : Finset (Cell (p.W + 1) (p.H + 1)) := Finset.univ.filter fun q => q.2.val ∈ rows
  have hregion : (readRows p side rows).region = region := by
    ext q
    simpa only [region, Finset.mem_filter, Finset.mem_univ, true_and] using readRows_region p side rows hside q
  have hquota : Scan.quota (instructions (w := p.W + 1) (h := p.H + 1) (emit [readRows p side rows] T).rounds) =
      (T.filter fun q => q.2.val ∈ rows).card := by
    have h := emit_accounting [readRows p side rows] T
    rw [emit_remaining] at h
    simp only [allRegions, Finset.union_empty, hregion] at h
    have hpart := Finset.card_filter_add_card_filter_not (s := T) (fun q => q.2.val ∈ rows)
    have hdiff : T \ region = T.filter fun q => q.2.val ∉ rows := by
      ext q
      simp only [region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdiff] at h
    have hd : (emit [readRows p side rows] T).discarded = 0 := rfl
    rw [hd, Nat.add_zero, ← quota_instructions] at h
    omega
  have hsupport : ∀ i ∈ instructions (w := p.W + 1) (h := p.H + 1) (emit [readRows p side rows] T).rounds,
      ∃ side lane quota, i = Scan.Instruction.read side lane quota ∧
        ∀ q ∈ Scan.lineCells (w := p.W + 1) (h := p.H + 1) side lane, q ∈ region := by
    intro i hi
    simp only [readRows, emit, instructions, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    refine ⟨side, a.1, a.2, rfl, ?_⟩
    intro q hq
    have hlane := (Scan.mem_lineCells side a.1 q).mp hq
    have hmem : a.1 ∈ rows := by
      have hm : a.1 ∈ (emitReads side (prefixRequests rows (fun _ => p.W + 1)) T).quotas.map Prod.fst :=
        List.mem_map.mpr ⟨a, ha, rfl⟩
      rw [emitted_lanes] at hm
      simp only [prefixRequests, List.map_map, Function.comp_def] at hm
      simpa using hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hside with rfl | rfl <;> change q.2.val = a.1 at hlane <;> rw [hlane] <;> exact hmem
  obtain ⟨F, hF⟩ := ha
  have h := read_support hsupport hF
  have hlost : E \ F ⊆ E.filter fun q => q.2.val ∈ rows := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq).1, (Finset.mem_filter.mp (h.2.2 hq)).2⟩
  have hlostcard := Finset.card_sdiff_add_card_eq_card h.1
  have hcard : (T.filter fun q => q.2.val ∈ rows).card ≤ (E \ F).card := by omega
  have heq := Finset.eq_of_subset_of_card_le (hlost.trans hstock) hcard
  intro q hq
  exact (Finset.mem_sdiff.mp (heq.symm ▸ hq)).1

private theorem prefix_after_side_subset (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (left : List Template) (E F : Finset (Cell (p.W + 1) (p.H + 1)))
    (hleft : ∃ mid, left = sideClearSchedule l p target ++ mid)
    (ha : Scan.Accepts (instructions (program l p target).rounds) E)
    (hF : Scan.eval (instructions (emit left (targetHoles l p target)).rounds) E = some F) :
    F ⊆ sideClearHoles l p target E := by
  obtain ⟨mid, rfl⟩ := hleft
  rw [emit_rounds_append, instructions, List.flatMap_append, eval_append] at hF
  have hside := program_sideClear_eval l p target ha
  simp only [instructions] at hside
  rw [hside, Option.bind_some] at hF
  exact scan_subset hF

private theorem central_stage_saturation_trace (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (left right : List Template) (side : Direction) (rows : Finset ℕ)
    (hside : side = .west ∨ side = .east)
    (hband : ∀ y ∈ rows, p.D ≤ y + 4 ∧ y ≤ p.D + 4)
    (hschedule : schedule l p (targetHoles l p target \ Boundary.frame).card = left ++ readRows p side rows :: right)
    (hleft : ∃ mid, left = sideClearSchedule l p target ++ mid)
    (hkeep : ∀ q ∈ l.centralMarkers p, q.2.val ∈ rows → q ∈ (emit left (targetHoles l p target)).remaining) :
    ∃ F, Scan.eval (instructions (emit left (targetHoles l p target)).rounds) (PushS.holes t) = some F ∧
      (l.centralMarkers p).filter (fun q => q.2.val ∈ rows) ⊆ F := by
  have hprogram := ha
  unfold program at hprogram
  rw [hschedule] at hprogram
  obtain ⟨F, hF, htail⟩ := emitted_split left _ _ _ hprogram
  have hsub := prefix_after_side_subset l p target left _ _ hleft ha hF
  have hread : Scan.Accepts (instructions (emit [readRows p side rows]
      (emit left (targetHoles l p target)).remaining).rounds) F := accepts_emitted_prefix _ _ _ _ htail
  have hstock : (F.filter fun q => q.2.val ∈ rows) ⊆
      (emit left (targetHoles l p target)).remaining.filter fun q => q.2.val ∈ rows := by
    intro q hq
    obtain ⟨hq, hrow⟩ := Finset.mem_filter.mp hq
    have hb := hband q.2.val hrow
    have hm := sideClearHoles_central_stock l p hl hM haxes initial target hr hp hs ha (hsub hq) hb.1 hb.2
    exact Finset.mem_filter.mpr ⟨hkeep q hm hrow, hrow⟩
  have hsat := row_saturation p side rows hside _ F hstock hread
  refine ⟨F, hF, ?_⟩
  intro q hq
  obtain ⟨hq, hrow⟩ := Finset.mem_filter.mp hq
  exact hsat (Finset.mem_filter.mpr ⟨hkeep q hq hrow, hrow⟩)

private theorem central_stage_saturation (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (left right : List Template) (side : Direction) (rows : Finset ℕ)
    (hside : side = .west ∨ side = .east)
    (hband : ∀ y ∈ rows, p.D ≤ y + 4 ∧ y ≤ p.D + 4)
    (hschedule : schedule l p (targetHoles l p target \ Boundary.frame).card = left ++ readRows p side rows :: right)
    (hleft : ∃ mid, left = sideClearSchedule l p target ++ mid)
    (hkeep : ∀ q ∈ l.centralMarkers p, q.2.val ∈ rows → q ∈ (emit left (targetHoles l p target)).remaining) :
    (l.centralMarkers p).filter (fun q => q.2.val ∈ rows) ⊆ PushS.holes t := by
  obtain ⟨F, hF, hmarkers⟩ := central_stage_saturation_trace l p hl hM haxes initial target hr hp hs ha
    left right side rows hside hband hschedule hleft hkeep
  exact hmarkers.trans (scan_subset hF)

end PushPuzzle.Push.AcceptanceSoundness
