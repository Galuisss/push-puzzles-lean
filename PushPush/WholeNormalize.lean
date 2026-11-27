/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeScan
public import Push.ScanNormalize
public import Push.ScanEmbedding
import all Push.ScanNormalize

/-! Sparse whole-run requests normalize to their dense per-lane lower bounds. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction Adjacent)

variable {w h : ℕ}

def NoSplit (side : Direction) (E F : Finset (Cell w h)) : Prop :=
  ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent side.opposite p q

theorem LooseExec.lines_no_split {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : LooseExec (Push.Scan.lines side requests) E F) : NoSplit side E F := by
  induction requests generalizing E with
  | nil => cases H; simp [NoSplit]
  | cons a rest ih =>
    cases H with
    | @cons _ _ _ _ _ _ G _ _ head tail =>
      intro p hp q hq ha
      obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
      by_cases hpG : p ∈ G
      · exact ih tail p (Finset.mem_sdiff.mpr ⟨hpG, hpF⟩) q hq ha
      · exact head.no_split p (Finset.mem_sdiff.mpr ⟨hpE, hpG⟩) q (tail.subset hq) ha

private theorem LooseExec.lines_actual {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : LooseExec (Push.Scan.lines side requests) E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) :
    ∃ actual : List (ℕ × ℕ),
      List.Forall₂ (fun a b : ℕ × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2) requests actual ∧
      (∀ a ∈ actual, a.1 < Push.Scan.laneCount side w h) ∧
      Exec (Push.Scan.lines side actual) E F := by
  induction requests generalizing E with
  | nil => cases H; exact ⟨[], .nil, by simp, .nil _⟩
  | cons a rest ih =>
    cases H with
    | @cons _ _ _ actual _ _ G _ paid head tail =>
      obtain ⟨as, hrel, habound, hexec⟩ := ih tail
        (fun b hb => hbound b (List.mem_cons_of_mem a hb))
      refine ⟨(a.1, actual) :: as, .cons ⟨rfl, paid⟩ hrel, ?_, .cons head hexec⟩
      intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact hbound a (List.mem_cons_self ..)
      · exact habound b hb

theorem Exec.lines_of_eval {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (hnd : (requests.map Prod.fst).Nodup)
    (he : Push.Scan.eval (Push.Scan.lines side requests) E = some F)
    (hwhole : NoSplit side E F) : Exec (Push.Scan.lines side requests) E F := by
  induction requests generalizing E with
  | nil =>
    have hf : E = F := Option.some.inj he
    exact hf ▸ Exec.nil E
  | cons a rest ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    simp only [Push.Scan.lines, List.map_cons, Push.Scan.eval, Option.bind_eq_some_iff] at he
    obtain ⟨G, hread, htail⟩ := he
    have hGE : G ⊆ E := Push.Scan.eval_subset (program := [.read side a.1 a.2]) (by
      simp only [Push.Scan.eval, hread, Option.bind_some])
    have hFG : F ⊆ G := Push.Scan.eval_subset htail
    refine .cons ⟨hread, ?_⟩ (ih hnd htail ?_)
    · intro p hp q hq ha
      have hpx : side.lane p = a.1 := by
        by_contra hn
        exact (Finset.mem_sdiff.mp hp).2
          ((Push.Scan.Instruction.read_outside hread hn).mpr (Finset.mem_sdiff.mp hp).1)
      have hqx : side.lane q = a.1 := by
        have hl := ha.lane
        have hop : ∀ z : Cell w h, side.opposite.lane z = side.lane z := by cases side <;> intro z <;> rfl
        simpa only [hop, hpx] using hl
      have hqF : q ∈ F := by
        apply (Push.Scan.eval_mem_outside htail ?_).mpr hq
        intro i hi
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
        intro z hz
        have heq : z = q := Finset.mem_singleton.mp hz
        rw [heq]
        intro hn
        apply hnot
        exact List.mem_map.mpr ⟨b, hb, hn.symm.trans hqx⟩
      exact hwhole p (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp).1,
        fun hpF => (Finset.mem_sdiff.mp hp).2 (hFG hpF)⟩) q hqF ha
    · intro p hp q hq ha
      exact hwhole p (Finset.mem_sdiff.mpr ⟨hGE (Finset.mem_sdiff.mp hp).1,
        (Finset.mem_sdiff.mp hp).2⟩) q hq ha

theorem Exec.loosen_lines {side : Direction} {small large : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : Exec (Push.Scan.lines side large) E F)
    (hle : List.Forall₂ (fun a b : ℕ × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2) small large) :
    LooseExec (Push.Scan.lines side small) E F := by
  induction hle generalizing E with
  | nil => cases H; exact .nil _
  | @cons a b small large hab htail ih =>
    cases H with
    | cons head tail => exact .cons hab.2 (by simpa only [hab.1] using head) (ih tail)

private theorem quotaAt_mono {small large : List (ℕ × ℕ)}
    (H : List.Forall₂ (fun a b : ℕ × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2) small large) (lane : ℕ) :
    Push.Scan.quotaAt small lane ≤ Push.Scan.quotaAt large lane := by
  induction H with
  | nil => exact le_rfl
  | @cons a b small large hab _ ih =>
    rw [Push.Scan.quotaAt_cons, Push.Scan.quotaAt_cons, hab.1]
    split <;> omega

private theorem dense_requests_mono (side : Direction) {small large : List (ℕ × ℕ)}
    (H : List.Forall₂ (fun a b : ℕ × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2) small large) :
    List.Forall₂ (fun a b : ℕ × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2)
      (Push.Scan.ofQuotas (Push.Scan.denseQuotas side w h small))
      (Push.Scan.ofQuotas (Push.Scan.denseQuotas side w h large)) := by
  apply List.forall₂_of_length_eq_of_get
  · simp only [Push.Scan.ofQuotas, List.length_ofFn, Push.Scan.denseQuotas_length]
  · intro i hi hj
    simp only [Push.Scan.ofQuotas, List.get_eq_getElem, List.getElem_ofFn,
      Fin.getElem_fin, Push.Scan.denseQuotas]
    exact ⟨trivial, quotaAt_mono H i⟩

/-- Sparse whole reads may be grouped into one whole read per actual board lane,
with each dense lower-bound quota still paid by the same terminal remainder. -/
theorem LooseExec.normalize {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : LooseExec (Push.Scan.lines side requests) E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) :
    LooseExec (Push.Scan.lines side (Push.Scan.ofQuotas (Push.Scan.denseQuotas side w h requests))) E F := by
  obtain ⟨actual, hrel, habound, hexec⟩ := H.lines_actual hbound
  have he := hexec.eval
  rw [Push.Scan.eval_normalize side w h actual habound] at he
  have hdense := Exec.lines_of_eval (Push.Scan.ofQuotas_nodup _) he H.lines_no_split
  exact hdense.loosen_lines (dense_requests_mono side hrel)

end PushPuzzle.PushPush.WholeScan
