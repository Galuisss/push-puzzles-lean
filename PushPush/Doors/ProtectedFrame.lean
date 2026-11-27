/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ProtectedLayout

/-! Successful slides never move any rack, divider or endpoint-cap box. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell State Direction Adjacent)

namespace Slide

variable {w h n k P : ℕ} {d : Direction} {s : State w h}

/-- No box in the restored extremal rack can be part of a moving run. -/
private theorem rack_not_before (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hs : Supported .east P s)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hrack : line .south P r.boxes = line .south P s.boxes)
    {p : Cell w h} (hp : p ∈ r.before) : p.1.val ≠ P := by
  by_cases hd : d = .east ∨ d = .west
  · exact r.horizontal_before_not_rack hn hk hd hs ht hrack hp
  · intro hx
    have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
    have hplayer : s.player.1.val = P := (r.vertical_before_lane hdv hp).symm.trans hx
    have hc := r.vertical_column_starts hdv hplayer hn hk hv ht
    rw [hrack] at hc
    omega

/-- A successful slide cannot deposit a box on the isolated divider. -/
private theorem divider_not_after (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hs : Supported .east P s) (ht : ∀ q ∈ r.boxes, ¬ Boundary q)
    {p : Cell w h} (hg : DividerGuard P s p)
    (hp : VerticallyIsolated (State.mk s.player r.boxes) p) : p ∉ r.after := by
  by_cases hd : d = .east ∨ d = .west
  · obtain ⟨e, he, hx, hem⟩ := hg.hole
    exact r.horizontal_after_not_divider hn hk hd hs ht he hx hem
  · intro hpa
    obtain ⟨q, hq, ha⟩ := r.after_neighbor hn ht hpa
    have had : Adjacent .north p q ∨ Adjacent .south p q := by cases d <;> simp_all
    exact hp.2 q had hq

end Slide

namespace Doors.Source

variable {storage : Bool} {I : Instance}

/-- Every protected frame box retains its physical identity throughout a successful move. -/
theorem Protected.slide_avoids_frame
    {s t : PushFS.State (layout storage I).width (layout storage I).height} {d : Direction} {n k : ℕ}
    (hs : Protected storage I s) (ht : Protected storage I t)
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) :
    Disjoint ((layout storage I).raster ((layout storage I).rack ∪ (layout storage I).blockers))
      r.before := by
  have hi : ∀ p ∈ r.boxes, ¬ Boundary p := by simpa only [Interior, hb] using ht.interior
  have hrack : line .south (layout storage I).rackX r.boxes =
      line .south (layout storage I).rackX s.boxes := by
    rw [← hb]
    exact ht.rack.trans hs.rack.symm
  apply Finset.disjoint_left.mpr
  intro p hp hbefore
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have hx := (layout storage I).rack_column hp
    exact r.rack_not_before hn hk hv hs.supported hi hrack hbefore hx
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hpx : p.1.val = (layout storage I).rackX - 1 := (congrArg Prod.fst he).symm
    have hpy : p.2.val = y + (layout storage I).shift := (congrArg Prod.snd he).symm
    rcases List.mem_append.mp hy with hy | hy
    · have hg := (divider_guard storage I hy p hpx hpy).congr hs.rack
      have hpt := ht.dividers y hy p hpx hpy
      have hpt' : VerticallyIsolated (PushFS.State.mk s.player r.boxes) p := by
        simpa only [VerticallyIsolated, hb] using hpt
      have hafter := r.divider_not_after hn hk hs.supported hi hg hpt'
      exact (Finset.mem_sdiff.mp ((Finset.mem_union.mp hpt'.1).resolve_right hafter)).2 hbefore
    · obtain ⟨g, hg, divider, hdx, hdy, hguard⟩ := cap_guard storage I hy p hpx hpy
      have hguard := hguard.congr hs.rack
      have hdsource := hs.dividers g hg divider hdx hdy
      have hdt := ht.dividers g hg divider hdx hdy
      have hdt' : VerticallyIsolated (PushFS.State.mk s.player r.boxes) divider := by
        simpa only [VerticallyIsolated, hb] using hdt
      have hafter := r.cap_not_after hn hk hs.supported hi hguard hdsource hdt'
      have hpt : p ∈ r.boxes := hb ▸ ht.caps y hy p hpx hpy
      exact (Finset.mem_sdiff.mp ((Finset.mem_union.mp hpt).resolve_right hafter)).2 hbefore

end Doors.Source
end PushPuzzle.PushPush
