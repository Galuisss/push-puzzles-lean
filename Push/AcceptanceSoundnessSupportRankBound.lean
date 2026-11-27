/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportSouthPayment
import all Push.AcceptanceSoundnessCentralRead
import all Push.Scan
import all PushFS.Grid

/-! Actual positive payments before a retained hole fit its literal coordinate rank. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- A whole real same-direction block retaining a marker loses at most its coordinate rank on that line. -/
theorem round_retained_lane_loss_bound {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ)) (T E F : Finset (Cell w h))
    (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    {a : Cell w h} (ha : a ∈ F) :
    (E.filter fun q => side.lane q = side.lane a).card ≤
      (F.filter fun q => side.lane q = side.lane a).card + prefixRank side a := by
  have hFsub : F ⊆ E := scan_subset he
  have hsub : E.filter (fun q => side.lane q = side.lane a) \ F.filter (fun q => side.lane q = side.lane a) ⊆
      ((Scan.lineCells side (side.lane a)).take (prefixRank side a)).toFinset := by
    intro b hb
    obtain ⟨hbE, hbF⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hbE, hbx⟩ := Finset.mem_filter.mp hbE
    have hbF' : b ∉ F := fun hb => hbF (Finset.mem_filter.mpr ⟨hb, hbx⟩)
    have horder := round_deleted_before_retained side requests T he ha hbE hbF' hbx.symm
    exact List.mem_toFinset.mpr ((mem_line_prefix side (side.lane a) _ b).mpr ⟨hbx, horder⟩)
  have hdiff := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (fun q => side.lane q = side.lane a) hFsub)
  have hcard := Finset.card_le_card hsub
  have hlist := List.toFinset_card_le ((Scan.lineCells (w := w) (h := h) side (side.lane a)).take (prefixRank side a))
  have htake := List.length_take_le (prefixRank side a) (Scan.lineCells (w := w) (h := h) side (side.lane a))
  omega

end PushPuzzle.Push.AcceptanceSoundness
