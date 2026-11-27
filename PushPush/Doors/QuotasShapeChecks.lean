/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasVector
public import PushPush.WholeEmission
public import Push.AcceptanceProgramBounded

/-! Every emitted reader round has bounded lanes and at most one positive quota per lane. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram

private theorem quotaTemplates_uniform (I : Instance) :
    ∀ side requests, Template.read side requests ∈ (layout false I).quotaTemplates →
      ∀ a ∈ requests, ∀ b ∈ requests, a.1 = b.1 → a.2 = b.2 := by
  intro side requests hm
  simp only [Layout.quotaTemplates, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with he | he | he | he | he | he | he <;> cases he
  · intro a ha b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl
  · intro a ha b hb _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl
  · simp
  · intro a ha b hb hcol
    simp only [Layout.probeRequests, List.mem_append, List.mem_map] at ha hb
    rcases ha with ⟨ra, hra, rfl⟩ | ⟨ra, hra, rfl⟩ <;>
      rcases hb with ⟨rb, hrb, rfl⟩ | ⟨rb, hrb, rfl⟩
    · rfl
    · change ra = rb at hcol
      exact False.elim (rackProbe_ne_marker I hra (hcol.symm ▸ hrb))
    · change ra = rb at hcol
      exact False.elim (rackProbe_ne_marker I hrb (hcol ▸ hra))
    · rfl
  · simp
  · intro a ha b hb _
    obtain ⟨ra, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨rb, _, rfl⟩ := List.mem_map.mp hb
    rfl
  · intro a ha b hb _
    obtain ⟨ra, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨rb, _, rfl⟩ := List.mem_map.mp hb
    rfl

private theorem quotaTemplates_bounded (I : Instance) :
    ∀ side requests, Template.read side requests ∈ (layout false I).quotaTemplates →
      ∀ a ∈ requests, a.1 < Push.Scan.laneCount side (layout false I).width (layout false I).height := by
  intro side requests hm
  simp only [Layout.quotaTemplates, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with he | he | he | he | he | he | he <;> cases he
  · intro a ha
    have hw := (layout false I).width_pos
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> change _ < (layout false I).width <;> omega
  · intro a ha
    have hh : 0 < (layout false I).height := by dsimp [layout, Layout.height, Layout.shift]; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> change _ < (layout false I).height <;> omega
  · simp
  · intro a ha
    simp only [Layout.probeRequests, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨row, hr, rfl⟩ | ⟨row, hr, rfl⟩
    · have hi := (layout_fits false I).fixed_interior ((layout false I).rackProbe_mem hr)
      change row < (layout false I).height
      dsimp only at hi
      omega
    · have hm := (layout false I).marker_mem hr
      change row < (layout false I).height
      rcases Finset.mem_union.mp hm with hfixed | hstop
      · have hi := (layout_fits false I).fixed_interior hfixed
        dsimp only at hi
        omega
      · have he := congrArg Prod.snd (Finset.mem_singleton.mp hstop)
        have hi := (layout false I).translated_bounds (stop_fit false I)
        dsimp only at he
        omega
  · simp
  · intro a ha
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp ha
    have hi := (layout_fits false I).fixed_interior ((layout false I).dividerNeighbor_mem hr)
    change row < (layout false I).height
    dsimp only at hi
    omega
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mp hx

theorem readerRounds_positive_nodup (I : Instance) :
    ∀ side requests, Round.read side requests ∈ readerRounds I →
      ((requests.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup :=
  WholeScan.emit_rounds_positive_nodup _ _ (quotaTemplates_uniform I)

theorem readerRounds_read_bounded (I : Instance) :
    ∀ side requests, Round.read side requests ∈ readerRounds I →
      ∀ a ∈ requests, a.1 < Push.Scan.laneCount side (layout false I).width (layout false I).height :=
  WholeScan.emit_rounds_read_bounded _ _ (quotaTemplates_bounded I)

theorem readerRounds_bounded (I : Instance) :
    Push.Scan.Bounded (instructions (w := (layout false I).width) (h := (layout false I).height) (readerRounds I)) := by
  intro instruction hi
  obtain ⟨block, hb, hi⟩ := List.mem_flatMap.mp hi
  cases block with
  | read side requests =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    exact readerRounds_read_bounded I side requests hb a ha
  | clear side lanes =>
    have hs : Round.shape (.clear side lanes) ∈ (readerRounds I).map Round.shape :=
      List.mem_map.mpr ⟨.clear side lanes, hb, rfl⟩
    rw [readerRounds_shapes I] at hs
    simp [Round.shape] at hs

end PushPuzzle.PushPush.Doors.Source
