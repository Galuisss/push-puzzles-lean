/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasFrame
public import PushPush.Doors.ProtectedLayout

/-! Full payment of the first four line requests forces an entirely empty source frame. -/

public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram

private theorem read_capacity {w h : ℕ} (side : Direction) (lane quota : ℕ)
    {E F : Finset (Cell w h)} (allowed : Finset (Cell w h))
    (hread : (Push.Scan.Instruction.read side lane quota).eval E = some F)
    (hsub : (E.filter fun p => side.lane p = lane) ⊆ allowed) (hsize : allowed.card = quota) :
    (E.filter fun p => side.lane p = lane) = allowed ∧
      (F.filter fun p => side.lane p = lane) = ∅ := by
  have hcap := (Push.Scan.Instruction.read_accepts_iff side lane quota E).mp ⟨F, hread⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (hsize ▸ hcap)
  refine ⟨heq, Finset.card_eq_zero.mp ?_⟩
  have hc := Push.Scan.Instruction.read_line_card hread
  rw [heq, hsize] at hc
  omega

private theorem read_subset {w h : ℕ} {side : Direction} {lane quota : ℕ} {E F : Finset (Cell w h)}
    (hread : (Push.Scan.Instruction.read side lane quota).eval E = some F) : F ⊆ E := by
  apply Push.Scan.eval_subset (program := [.read side lane quota])
  simp only [Push.Scan.eval, hread, Option.bind_some]

private theorem full_column_card {w h : ℕ} (x : Fin w) :
    (Finset.univ.filter (fun p : Cell w h => p.1.val = x.val)).card = h := by
  have he : (Finset.univ.filter fun p : Cell w h => p.1.val = x.val) =
      (Push.Scan.lineCells .south x.val).toFinset := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
      Push.Scan.mem_lineCells, Direction.lane]
  rw [he, List.toFinset_card_of_nodup (Push.Scan.lineCells_nodup .south x.val)]
  simp [Push.Scan.lineCells, x.isLt]

/-- Any bitmap accepted by the actual seven-round word has holes on all four true edges. -/
theorem readerRounds_frame (I : Instance)
    (E : Finset (Cell (layout false I).width (layout false I).height))
    (ha : Push.Scan.Accepts (instructions (readerRounds I)) E) :
    ∀ p : Cell (layout false I).width (layout false I).height, Boundary p → p ∈ E := by
  let L := layout false I
  obtain ⟨rest, hword⟩ := readerRounds_frame_prefix I
  obtain ⟨final, he⟩ := ha
  rw [hword] at he
  simp only [instructions, List.flatMap_cons, Round.instructions, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Push.Scan.eval,
    Option.bind_eq_some_iff] at he
  obtain ⟨E₁, h₁, E₂, h₂, E₃, h₃, E₄, h₄, _⟩ := he
  have hsub₁ := read_subset h₁
  have hsub₂ := read_subset h₂
  have hsub₃ := read_subset h₃
  have hleft := read_capacity .south 0 L.height
    (Finset.univ.filter fun p : Cell L.width L.height => p.1.val = 0) h₁
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
    (full_column_card (⟨0, L.width_pos⟩ : Fin L.width))
  have hright := read_capacity .south (L.width - 1) L.height
    (Finset.univ.filter fun p : Cell L.width L.height => p.1.val = L.width - 1) h₂
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
    (full_column_card (⟨L.width - 1, by have := L.width_pos; omega⟩ : Fin L.width))
  have hcolumns (p : Cell L.width L.height) (hp : p ∈ E₂) :
      p.1.val ≠ 0 ∧ p.1.val + 1 ≠ L.width := by
    constructor
    · intro hx
      have hm : p ∈ E₁.filter (fun p => Direction.south.lane p = 0) :=
        Finset.mem_filter.mpr ⟨hsub₂ hp, hx⟩
      rw [hleft.2] at hm
      exact Finset.notMem_empty _ hm
    · intro hx
      have hm : p ∈ E₂.filter (fun p => Direction.south.lane p = L.width - 1) :=
        Finset.mem_filter.mpr ⟨hp, by change p.1.val = L.width - 1; omega⟩
      rw [hright.2] at hm
      exact Finset.notMem_empty _ hm
  let innerTop := (L.referenceHoles \ readRegion .south [(0, L.height), (L.width - 1, L.height)]).filter
    (fun p => p.2.val = 0)
  let innerBottom := (L.referenceHoles \ readRegion .south [(0, L.height), (L.width - 1, L.height)]).filter
    (fun p => p.2.val = L.height - 1)
  have hinner (p : Cell L.width L.height) (hp : p ∈ E₂) (hb : Boundary p) :
      p ∈ L.referenceHoles \ readRegion .south [(0, L.height), (L.width - 1, L.height)] := by
    refine Finset.mem_sdiff.mpr ⟨reference_boundary I p hb, ?_⟩
    rw [frame_columns_region]
    intro he
    rcases (Finset.mem_filter.mp he).2 with hl | hr
    · exact (hcolumns p hp).1 hl
    · exact (hcolumns p hp).2 hr
  have htop := read_capacity .west 0 (L.width - 2) innerTop h₃ (by
    intro p hp
    obtain ⟨hp, hy⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    exact ⟨hinner p hp (Or.inr (Or.inr (Or.inl hy))), hy⟩)
    (frame_inner_row_card I ⟨0, L.height_pos⟩ (Or.inl rfl))
  have hbottom := read_capacity .west (L.height - 1) (L.width - 2) innerBottom h₄ (by
    intro p hp
    obtain ⟨hp, hy⟩ := Finset.mem_filter.mp hp
    have hy' : p.2.val + 1 = L.height := by
      change p.2.val = L.height - 1 at hy
      have := L.height_pos
      omega
    apply Finset.mem_filter.mpr
    exact ⟨hinner p (hsub₃ hp) (Or.inr (Or.inr (Or.inr hy'))), hy⟩)
    (frame_inner_row_card I ⟨L.height - 1, by
      change L.height - 1 < L.height
      have := L.height_pos
      omega⟩ (Or.inr (by change L.height - 1 + 1 = L.height; have := L.height_pos; omega)))
  intro p hp
  by_cases hl : p.1.val = 0
  · have hm : p ∈ E.filter (fun p => Direction.south.lane p = 0) := by
      rw [hleft.1]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
    exact (Finset.mem_filter.mp hm).1
  by_cases hr : p.1.val + 1 = L.width
  · have hm : p ∈ E₁.filter (fun p => Direction.south.lane p = L.width - 1) := by
      rw [hright.1]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change p.1.val = L.width - 1; omega⟩
    exact hsub₁ (Finset.mem_filter.mp hm).1
  have hshared : p ∈ L.referenceHoles \ readRegion .south [(0, L.height), (L.width - 1, L.height)] := by
    refine Finset.mem_sdiff.mpr ⟨reference_boundary I p hp, ?_⟩
    rw [frame_columns_region]
    intro he
    rcases (Finset.mem_filter.mp he).2 with hx | hx
    · exact hl hx
    · exact hr hx
  simp only [Boundary] at hp
  change p.1.val = 0 ∨ p.1.val + 1 = L.width ∨ p.2.val = 0 ∨ p.2.val + 1 = L.height at hp
  rcases hp with hp | hp | ht | hb
  · exact False.elim (hl hp)
  · exact False.elim (hr hp)
  · have hm : p ∈ E₂.filter (fun p => Direction.west.lane p = 0) := by
      rw [htop.1]
      exact Finset.mem_filter.mpr ⟨hshared, ht⟩
    exact hsub₁ (hsub₂ (Finset.mem_filter.mp hm).1)
  · have hm : p ∈ E₃.filter (fun p => Direction.west.lane p = L.height - 1) := by
      rw [hbottom.1]
      exact Finset.mem_filter.mpr ⟨hshared, by change p.2.val = L.height - 1; omega⟩
    exact hsub₁ (hsub₂ (hsub₃ (Finset.mem_filter.mp hm).1))

end PushPuzzle.PushPush.Doors.Source
