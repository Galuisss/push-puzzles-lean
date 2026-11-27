/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutFree
public import PushPush.Doors.WireReadoutCorner

/-! Reverse pin slides close into immobile private clusters. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

/-- The new perpendicular line of a horizontal reverse-pin landing is a free private column. -/
theorem horizontal_neighbor_free_line (storage : Bool) (S : Stock I)
    (forward : Direction) (signal landed : Cell (layout storage I).width (layout storage I).height)
    (hd : forward = .east ∨ forward = .west) (ha : Adjacent forward signal landed)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hprivate : landed.1.val < (layout storage I).rackX - 1)
    (hfree : ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val) :
    ∀ (d : Direction) q, q ∈ S.boxes storage → d.lane q = d.lane landed →
      d.lane landed ≠ d.lane signal → False := by
  intro d q hq hl hne
  have hrow : landed.2 = signal.2 := by rcases hd with rfl | rfl <;> exact ha.2
  by_cases hv : d = .north ∨ d = .south
  · have hcol : q.1.val = landed.1.val := by rcases hv with rfl | rfl <;> exact hl
    have hsigx : S.signal.1 ≠ landed.1.val := by
      have hx := congrArg Prod.fst hsignal
      rcases hd with rfl | rfl <;> simp only [Adjacent] at ha <;> dsimp at hx <;> omega
    have hqraw := ((layout storage I).mem_raster _ _).mp hq
    exact S.raw_column_empty storage landed.1.val hprivate hfree hsigx hcol hqraw
  · have hh : d = .east ∨ d = .west := by cases d <;> simp_all
    apply hne
    rcases hh with rfl | rfl <;> exact congrArg Fin.val hrow

/-- A one-pin fault is a complete dead stock whenever its newly opened line is empty.
The other three lines are closed by the original previous/next pins. -/
theorem reverse_corner_deadStock (storage : Bool) (S : Stock I) (forward : Direction)
    (signal previous stop landed : Cell (layout storage I).width (layout storage I).height)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hc : Wire.Corner forward signal previous stop)
    (hprevious : (previous.1.val, previous.2.val) ∈ (layout storage I).pins)
    (hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins)
    (ha : Adjacent forward signal landed)
    (hsignalprivate : signal.1.val < (layout storage I).rackX - 1)
    (hlandprivate : landed.1.val < (layout storage I).rackX - 1)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner,
      insert landed ((S.boxes storage).erase stop)⟩)
    (hother : ∀ (d : Direction) q, q ∈ S.boxes storage → d.lane q = d.lane landed →
      d.lane landed ≠ d.lane signal → False) :
    Wire.DeadStock (insert landed ((S.boxes storage).erase stop)) (Protected storage I) ∧
      stop ∉ insert landed ((S.boxes storage).erase stop) := by
  let F := WireFault.single signal stop landed hstop hsignal
  let cluster : Finset (Cell (layout storage I).width (layout storage I).height) :=
    {signal, previous, landed}
  have hsigne : signal ≠ stop := by
    intro he
    have hp := hc.2.2.2
    rw [he] at hp
    omega
  have hprevne : previous ≠ stop := by
    intro he
    exact hc.2.1 (he ▸ hc.2.2.1)
  have hlandne : stop ≠ landed := by
    intro he
    have hp := hc.2.2.2
    have hl := ha.position
    rw [he] at hp
    omega
  have hsignalbox : signal ∈ S.boxes storage := by
    apply ((layout storage I).mem_raster _ _).mpr
    apply Finset.mem_union_right
    exact Finset.mem_singleton.mpr hsignal
  have hprevbox : previous ∈ S.boxes storage := by
    apply ((layout storage I).mem_raster _ _).mpr
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hprevious)))
  have hsub : cluster ⊆ F.boxes := by
    intro p hp
    rw [WireFault.single_boxes]
    simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with he | he | he
    · subst p
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsigne, hsignalbox⟩)
    · subst p
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hprevne, hprevbox⟩)
    · subst p
      exact Finset.mem_insert_self _ _
  have hanchors : ∀ d p, p ∈ cluster → F.Anchored cluster d p := by
    intro d p hp
    have hpinAnchor : ∀ pin : Cell (layout storage I).width (layout storage I).height,
        (pin.1.val, pin.2.val) ∈ (layout storage I).pins →
        (pin ∈ cluster ∨ pin = stop) → d.lane p = d.lane pin → F.Anchored cluster d p := by
      intro pin hpin hm hl
      exact Or.inl ⟨pin, hpin, hm.imp_right (fun he => by simp [F, WireFault.single, he]), hl⟩
    have hsignalAnchor : d.lane p = d.lane signal → F.Anchored cluster d p := by
      intro hl
      rcases Wire.corner_lane_cover hc d with hprev | hstop'
      · exact hpinAnchor previous hprevious (Or.inl (by simp [cluster])) (hl.trans hprev)
      · exact hpinAnchor stop hstop (Or.inr rfl) (hl.trans hstop')
    simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with he | he | he
    · subst p
      exact hsignalAnchor rfl
    · subst p
      exact hpinAnchor previous hprevious (Or.inl (by simp [cluster])) rfl
    · subst p
      by_cases hl : d.lane landed = d.lane signal
      · exact hsignalAnchor hl
      · exact Or.inr (fun q hq hql => hother d q hq hql hl)
  have hdead := F.deadStock hsignalprivate
    (by intro p hp; have he := Finset.mem_singleton.mp hp; simpa only [he] using hlandprivate)
    hregister (by simpa only [F, WireFault.single_boxes] using hprotected) cluster hsub
    (Wire.reverse_corner_lineConvex hc ha)
    (F.lineClosed_of_anchors cluster (by simp [cluster, F, WireFault.single])
      (by intro p hp; have he := Finset.mem_singleton.mp hp; simp [he, cluster]) hanchors)
    (by simp [cluster, F, WireFault.single])
    (by intro p hp; have he := Finset.mem_singleton.mp hp; simp [he, cluster])
  exact ⟨by simpa only [F, WireFault.single_boxes] using hdead,
    by simpa only [F, WireFault.single_boxes] using WireFault.single_missing signal stop landed hstop hsignal hlandne⟩

end PushPuzzle.PushPush.Doors.Source.Stock
