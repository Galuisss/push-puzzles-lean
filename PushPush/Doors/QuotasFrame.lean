/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasShape
public import Push.ScanEmbedding

/-! The first two actual rounds read the entire four-sided source frame. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram

private theorem full_front_count {α : Type} [DecidableEq α] (cells : List α) (E : Finset α)
    (span : ℕ) (hspan : cells.length ≤ span) (hn : cells.Nodup)
    (hfull : ∀ p ∈ cells, p ∈ E) :
    (E.filter fun p => p ∈ cells.take span).card = cells.length := by
  rw [List.take_of_length_le hspan]
  have he : (E.filter fun p => p ∈ cells) = cells.toFinset := by
    ext p
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨And.right, fun hp => ⟨hfull p hp, hp⟩⟩
  rw [he, List.toFinset_card_of_nodup hn]

theorem reference_boundary (I : Instance)
    (p : Cell (layout false I).width (layout false I).height) (hp : Boundary p) :
    p ∈ (layout false I).referenceHoles := by
  apply Finset.mem_compl.mpr
  intro hb
  have hi := (layout_fits false I).goalsRaw_interior (((layout false I).mem_raster _ _).mp hb)
  dsimp at hi
  simp only [Boundary] at hp
  omega

private theorem firstRound_quotas (I : Instance) :
    (emitReads .south [(0, (layout false I).height),
      ((layout false I).width - 1, (layout false I).height)] (layout false I).referenceHoles).quotas =
      [(0, (layout false I).height), ((layout false I).width - 1, (layout false I).height)] := by
  let L := layout false I
  let left := Push.Scan.lineCells (w := L.width) (h := L.height) .south 0
  let right := Push.Scan.lineCells (w := L.width) (h := L.height) .south (L.width - 1)
  have hw : 0 < L.width := L.width_pos
  have hrightLen : right.length = L.height := by simp [right, Push.Scan.lineCells, show L.width - 1 < L.width by omega]
  have hright : ∀ p ∈ right, p ∈ L.referenceHoles \ (left.take L.height).toFinset := by
    intro p hp
    have hx := (Push.Scan.mem_lineCells .south (L.width - 1) p).mp hp
    simp only [Direction.lane] at hx
    refine Finset.mem_sdiff.mpr ⟨reference_boundary I p (Or.inr (Or.inl (by
      change p.1.val + 1 = L.width
      omega))), ?_⟩
    intro hleft
    have hm := List.mem_of_mem_take (List.mem_toFinset.mp hleft)
    have hx' := (Push.Scan.mem_lineCells .south 0 p).mp hm
    simp only [Direction.lane] at hx'
    have hw' : 46 ≤ L.width := by dsimp [L]; unfold Layout.width Layout.rackX; omega
    omega
  have hsecond := full_front_count right (L.referenceHoles \ (left.take L.height).toFinset) L.height
    hrightLen.le (Push.Scan.lineCells_nodup .south (L.width - 1)) hright
  rw [hrightLen] at hsecond
  change [(0, _), (L.width - 1, _)] = [(0, L.height), (L.width - 1, L.height)]
  rw [firstQuota_height, hsecond]

/-- The first south round removes exactly the two original side columns. -/
theorem frame_columns_region (I : Instance) :
    readRegion (w := (layout false I).width) (h := (layout false I).height) .south
      [(0, (layout false I).height), ((layout false I).width - 1, (layout false I).height)] =
      Finset.univ.filter (fun p => p.1.val = 0 ∨ p.1.val + 1 = (layout false I).width) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hp
    obtain ⟨request, hr, hl, _⟩ := (mem_readRegion _ _ p).mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hw := p.1.isLt
    rcases hr with rfl | rfl <;> simp only [Direction.lane] at hl <;> omega
  · intro hp
    apply (mem_readRegion _ _ p).mpr
    have hy := p.2.isLt
    rcases hp with hp | hp
    · exact ⟨(0, (layout false I).height), by simp, hp, by simp only [prefixRank]; omega⟩
    · refine ⟨((layout false I).width - 1, (layout false I).height), by simp, ?_, ?_⟩
      · simp only [Direction.lane]
        omega
      · simp only [prefixRank]
        omega

private theorem horizontal_frame_count (I : Instance) (y : Fin (layout false I).height)
    (hy : y.val = 0 ∨ y.val + 1 = (layout false I).height) :
    (((layout false I).referenceHoles \
      readRegion .south [(0, (layout false I).height),
        ((layout false I).width - 1, (layout false I).height)]).filter fun p =>
        p ∈ (Push.Scan.lineCells .west y.val).take (layout false I).width).card =
      (layout false I).width - 2 := by
  let L := layout false I
  let line := Push.Scan.lineCells (w := L.width) (h := L.height) .west y.val
  let left : Cell L.width L.height := (⟨0, L.width_pos⟩, y)
  let right : Cell L.width L.height := (⟨L.width - 1, by have := L.width_pos; omega⟩, y)
  let corners : Finset (Cell L.width L.height) := {left, right}
  have hlen : line.length = L.width := by
    have hy' : y.val < L.height := y.isLt
    simp [line, Push.Scan.lineCells, hy']
  have ht : line.take L.width = line := List.take_of_length_le hlen.le
  have hcorners : corners ⊆ line.toFinset := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact List.mem_toFinset.mpr ((Push.Scan.mem_lineCells .west y.val left).mpr rfl)
    · have he := Finset.mem_singleton.mp hp
      subst p
      exact List.mem_toFinset.mpr ((Push.Scan.mem_lineCells .west y.val right).mpr rfl)
  have hne : left ≠ right := by
    intro he
    have he := congrArg (fun p => p.1.val) he
    have hw : 46 ≤ L.width := by dsimp [L]; unfold Layout.width Layout.rackX; omega
    dsimp [left, right] at he
    omega
  have hcornersCard : corners.card = 2 := by simp [corners, hne]
  rw [frame_columns_region, ht]
  have he : ((L.referenceHoles \ Finset.univ.filter (fun p => p.1.val = 0 ∨ p.1.val + 1 = L.width)).filter
      fun p => p ∈ line) = line.toFinset \ corners := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hl⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, hn⟩ := Finset.mem_sdiff.mp hp
      apply Finset.mem_sdiff.mpr
      refine ⟨List.mem_toFinset.mpr hl, ?_⟩
      intro hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩)
      · have hc := Finset.mem_singleton.mp hc
        subst p
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by dsimp [right]; have := L.width_pos; omega)⟩)
    · intro hp
      obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hp
      have hpy : p.2 = y := Fin.ext ((Push.Scan.mem_lineCells .west y.val p).mp (List.mem_toFinset.mp hl))
      have hb : p ∈ L.referenceHoles := reference_boundary I p (by
        rcases hy with hy | hy
        · exact Or.inr (Or.inr (Or.inl (by rw [hpy]; exact hy)))
        · exact Or.inr (Or.inr (Or.inr (by rw [hpy]; exact hy))))
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨hb, ?_⟩, List.mem_toFinset.mp hl⟩
      intro hc
      rcases (Finset.mem_filter.mp hc).2 with hx | hx
      · apply hn
        apply Finset.mem_insert.mpr
        exact Or.inl (Prod.ext (Fin.ext hx) hpy)
      · apply hn
        apply Finset.mem_insert.mpr
        apply Or.inr
        apply Finset.mem_singleton.mpr
        apply Prod.ext (Fin.ext ?_) hpy
        dsimp [right]
        omega
  rw [he, Finset.card_sdiff_of_subset hcorners,
    List.toFinset_card_of_nodup (Push.Scan.lineCells_nodup .west y.val), hlen, hcornersCard]

private theorem secondRound_quotas (I : Instance) :
    (emitReads .west [(0, (layout false I).width),
      ((layout false I).height - 1, (layout false I).width)]
      (emitReads .south [(0, (layout false I).height),
        ((layout false I).width - 1, (layout false I).height)] (layout false I).referenceHoles).remaining).quotas =
      [(0, (layout false I).width - 2), ((layout false I).height - 1, (layout false I).width - 2)] := by
  let L := layout false I
  let before := (emitReads .south [(0, L.height), (L.width - 1, L.height)] L.referenceHoles).remaining
  let top := (Push.Scan.lineCells (w := L.width) (h := L.height) .west 0).take L.width
  let bottom := (Push.Scan.lineCells (w := L.width) (h := L.height) .west (L.height - 1)).take L.width
  have hbefore : before = L.referenceHoles \ readRegion .south [(0, L.height), (L.width - 1, L.height)] :=
    emitReads_remaining _ _ _
  have htop : (before.filter fun p => p ∈ top).card = L.width - 2 := by
    rw [hbefore]
    exact horizontal_frame_count I ⟨0, L.height_pos⟩ (Or.inl rfl)
  have hbottom : (before.filter fun p => p ∈ bottom).card = L.width - 2 := by
    rw [hbefore]
    exact horizontal_frame_count I ⟨L.height - 1, by
      change L.height - 1 < L.height
      have := L.height_pos
      omega⟩
      (Or.inr (by change L.height - 1 + 1 = L.height; have := L.height_pos; omega))
  have he : ((before \ top.toFinset).filter fun p => p ∈ bottom) = before.filter fun p => p ∈ bottom := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hp, _⟩, hb⟩
      exact ⟨hp, hb⟩
    · rintro ⟨hp, hb⟩
      refine ⟨⟨hp, ?_⟩, hb⟩
      intro ht
      have ht' := List.mem_of_mem_take (List.mem_toFinset.mp ht)
      have hb' := List.mem_of_mem_take hb
      have hyt := (Push.Scan.mem_lineCells .west 0 p).mp ht'
      have hyb := (Push.Scan.mem_lineCells .west (L.height - 1) p).mp hb'
      simp only [Direction.lane] at hyt hyb
      have hh : 31 ≤ L.height := by dsimp [L]; unfold Layout.height Layout.shift; omega
      omega
  change [(0, (before.filter fun p => p ∈ top).card),
      (L.height - 1, ((before \ top.toFinset).filter fun p => p ∈ bottom).card)] = _
  rw [htop, he, hbottom]

/-- The first two emitted blocks have their exact frame-only numerical quotas. -/
theorem readerRounds_frame_prefix (I : Instance) :
    ∃ rest, readerRounds I =
      Round.read .south [(0, (layout false I).height), ((layout false I).width - 1, (layout false I).height)] ::
      Round.read .west [(0, (layout false I).width - 2),
        ((layout false I).height - 1, (layout false I).width - 2)] :: rest := by
  change ∃ rest,
    Round.read .south (emitReads .south [(0, (layout false I).height),
      ((layout false I).width - 1, (layout false I).height)] (layout false I).referenceHoles).quotas ::
      Round.read .west (emitReads .west [(0, (layout false I).width),
        ((layout false I).height - 1, (layout false I).width)]
        (emitReads .south [(0, (layout false I).height),
          ((layout false I).width - 1, (layout false I).height)] (layout false I).referenceHoles).remaining).quotas :: _ = _
  rw [firstRound_quotas, secondRound_quotas]
  exact ⟨_, rfl⟩

/-- The inner part of either horizontal frame row has exactly width minus two cells. -/
theorem frame_inner_row_card (I : Instance) (y : Fin (layout false I).height)
    (hy : y.val = 0 ∨ y.val + 1 = (layout false I).height) :
    (((layout false I).referenceHoles \
      readRegion .south [(0, (layout false I).height),
        ((layout false I).width - 1, (layout false I).height)]).filter fun p => p.2.val = y.val).card =
      (layout false I).width - 2 := by
  have he := horizontal_frame_count I y hy
  convert he using 2
  apply Finset.filter_congr
  intro p _
  rw [mem_line_prefix]
  simp only [Direction.lane, prefixRank]
  exact ⟨fun hp => ⟨hp, p.1.isLt⟩, And.left⟩

end PushPuzzle.PushPush.Doors.Source
