/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSourceLift

/-! Replacing the source configuration at equal hole count preserves the reader's literal geometry. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS

variable (r : Input)

/-- Replace the starting source configuration while retaining all column quotas. -/
def withInitial (s : HoleState r.width r.height) (hc : s.empty.card = r.initial.empty.card) : Input where
  width := r.width
  height := r.height
  initial := s
  quotas := r.quotas
  quotas_width := r.quotas_width
  quotas_le := hc.symm ▸ r.quotas_le
  extraWidth := r.extraWidth

/-- The original extension with the new live-source state and the same target player cell. -/
def liftedInstance (s : HoleState r.width r.height) : Push.Instance where
  width := r.outputWidth
  height := r.outputHeight
  initial := r.liftState s.toState
  target := r.target
  player_empty := by
    change r.embed s.player ∉ (r.liftEmpty s.toState)ᶜ
    simp only [Finset.mem_compl, not_not, liftEmpty_embed_mem, s.holes_toState]
    exact s.player_empty

private theorem auxiliaryHoles_eq : r.auxiliaryHoles =
    ({r.door, r.upper, r.bottom} ∪ r.room ∪ r.needles) := by
  have hd : Disjoint r.sourceEmpty ({r.door, r.upper, r.bottom} ∪ r.room ∪ r.needles) := by
    apply Finset.disjoint_left.mpr
    intro q hq ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    have hpx := p.1.isLt
    have hpy := p.2.isLt
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (((he | he | he) | he) | he)
    · have := congrArg (fun q => q.1.val) he
      change p.1.val = r.width at this
      omega
    · have := congrArg (fun q => q.1.val) he
      change p.1.val = r.width at this
      omega
    · have := congrArg (fun q => q.1.val) he
      change p.1.val = r.width at this
      omega
    · have := (Finset.mem_filter.mp he).2.1
      change r.width < p.1.val at this
      omega
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
      have hy := congrArg (fun q => q.2.val) hi
      have hf := r.needle_far_south i
      change (r.needle i).2.val = p.2.val at hy
      omega
  ext q
  simp only [auxiliaryHoles, empty, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hs | ha, hn⟩
    · exact False.elim (hn hs)
    · exact ha
  · intro ha
    exact ⟨Or.inr ha, Finset.disjoint_right.mp hd (by simpa only [Finset.mem_union] using ha)⟩

private theorem state_heq_coords {w h W H : ℕ} (hw : w = W) (hh : h = H)
    (s : State w h) (t : State W H)
    (hx : s.player.1.val = t.player.1.val) (hy : s.player.2.val = t.player.2.val)
    (hb : ∀ p q, p.1.val = q.1.val → p.2.val = q.2.val → (p ∈ s.boxes ↔ q ∈ t.boxes)) :
    HEq s t := by
  subst W
  subst H
  apply heq_of_eq
  apply State.ext
  · apply Prod.ext <;> apply Fin.ext
    · exact hx
    · exact hy
  · ext p
    exact hb p p rfl rfl

private theorem cell_heq_coords {w h W H : ℕ} (hw : w = W) (hh : h = H)
    (p : Cell w h) (q : Cell W H) (hx : p.1.val = q.1.val) (hy : p.2.val = q.2.val) : HEq p q := by
  subst W
  subst H
  apply heq_of_eq
  apply Prod.ext <;> apply Fin.ext
  · exact hx
  · exact hy

/-- Equal source hole counts give exactly the same reader, with only the source state replaced. -/
theorem withInitial_compile (s : HoleState r.width r.height) (hc : s.empty.card = r.initial.empty.card) :
    (r.withInitial s hc).compile = r.liftedInstance s := by
  have hH : (r.withInitial s hc).outputHeight = r.outputHeight := by
    simp only [withInitial, outputHeight, length, quota, sourceHoles, hc]
  simp only [compile, liftedInstance, Push.Instance.mk.injEq]
  refine ⟨rfl, hH, ?_, ?_⟩
  · apply state_heq_coords (w := (r.withInitial s hc).outputWidth) (W := r.outputWidth)
      (h := (r.withInitial s hc).outputHeight) (H := r.outputHeight) rfl hH
    · rfl
    · rfl
    · intro p q hx hy
      change (p ∈ (r.withInitial s hc).emptyᶜ) ↔ q ∈ (r.liftEmpty s.toState)ᶜ
      simp only [Finset.mem_compl, empty, sourceEmpty, liftEmpty, s.holes_toState, r.auxiliaryHoles_eq,
        room, needles, needle,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_image, Prod.ext_iff, Fin.ext_iff]
      simp only [withInitial, embed, door, upper, bottom, needleLevel,
        firstLevel, outputWidth, outputHeight, length, quota, sourceHoles, hc, hx, hy]
      rfl
  · apply cell_heq_coords rfl hH
    · rfl
    · simp only [target, targetLevel, firstLevel, withInitial, outputHeight, length, quota, sourceHoles, hc]

end PushPuzzle.Push.ColumnScan.Input
