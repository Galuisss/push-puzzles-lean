/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasCuts
public import Push.AcceptanceSoundnessSupportTrace
public import Push.ScanEmbedding

/-! A positive whole-run read must pay every cell of its initial contiguous hole chain. -/

public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction Adjacent)
open Push.AcceptanceProgram

variable {w h n quota : ℕ} {side : Direction} {lane : ℕ} {E F : Finset (Cell w h)}

private theorem read_subset
    (hr : (Push.Scan.Instruction.read side lane quota).eval E = some F) : F ⊆ E := by
  apply Push.Scan.eval_subset (program := [.read side lane quota])
  simp only [Push.Scan.eval, hr, Option.bind_some]

private theorem read_deleted_card
    (hr : (Push.Scan.Instruction.read side lane quota).eval E = some F) :
    ((E.filter fun p => side.lane p = lane) \ (F.filter fun p => side.lane p = lane)).card = quota := by
  have hsub : (F.filter fun p => side.lane p = lane) ⊆ E.filter fun p => side.lane p = lane := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨read_subset hr (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  rw [Finset.card_sdiff_of_subset hsub]
  have hc := Push.Scan.Instruction.read_line_card hr
  omega

/-- Bare static consumption plus an uncut-run boundary already forces its entire first chain's payment. -/
theorem whole_read_chain
    (hr : (Push.Scan.Instruction.read side lane quota).eval E = some F) (hq : 0 < quota)
    (hwhole : ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent side.opposite p q)
    (cells : Fin (n + 1) → Cell w h)
    (hempty : ∀ i, cells i ∈ E)
    (hlane : ∀ i, side.lane (cells i) = lane)
    (hadj : ∀ i : Fin n, Adjacent side.opposite (cells i.castSucc) (cells i.succ))
    (hfirst : ∀ p ∈ E, side.lane p = lane → prefixRank side (cells 0) ≤ prefixRank side p) :
    n + 1 ≤ quota := by
  have hcard := read_deleted_card hr
  obtain ⟨deleted, hd⟩ := Finset.card_pos.mp (by rw [hcard]; exact hq)
  obtain ⟨hdE, hdF⟩ := Finset.mem_sdiff.mp hd
  obtain ⟨hdE, hdline⟩ := Finset.mem_filter.mp hdE
  have hdnot : deleted ∉ F := fun h => hdF (Finset.mem_filter.mpr ⟨h, hdline⟩)
  have hzero : cells 0 ∉ F := by
    intro hz
    have ho := Push.AcceptanceSoundness.read_deleted_before_retained hr hz (hlane 0) hdE hdnot
    have hf := hfirst deleted hdE hdline
    omega
  have hnot : ∀ i, cells i ∉ F := by
    intro i
    induction i using Fin.induction with
    | zero => exact hzero
    | succ i ih =>
      intro hp
      exact hwhole _ (Finset.mem_sdiff.mpr ⟨hempty _, ih⟩) _ hp (hadj i)
  have hpos : ∀ i, prefixRank side (cells i) = prefixRank side (cells 0) + i.val := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have he := Layout.adjacent_prefixRank side (hadj i)
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega
  have hinj : Function.Injective cells := by
    intro i j he
    have hi := hpos i
    have hj := hpos j
    rw [he] at hi
    apply Fin.ext
    omega
  have hsub : Finset.univ.image cells ⊆
      (E.filter fun p => side.lane p = lane) \ (F.filter fun p => side.lane p = lane) := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hempty i, hlane i⟩,
      fun h => hnot i (Finset.mem_filter.mp h).1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hcard] at hc
  exact hc

end PushPuzzle.PushPush.Doors
