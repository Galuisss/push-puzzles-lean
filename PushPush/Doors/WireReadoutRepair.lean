/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutReverse

/-! Exact fault inventory updates and closure after the sole B/C attraction. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction Adjacent)

namespace Wire

variable {w h : ℕ}

/-- Replacing one cluster box preserves all old occupied lines. Only the landing
box's new perpendicular line requires a separate clearance certificate. -/
private theorem LineClosed.replace {cluster boxes : Finset (Cell w h)}
    (hclosed : LineClosed cluster boxes) (moving landed : Cell w h)
    (hnew : ∀ (d : Direction),
      (∃ p ∈ cluster, d.lane landed = d.lane p) ∨
      ∀ q ∈ boxes, d.lane q = d.lane landed → False) :
    LineClosed (insert landed (cluster.erase moving)) (insert landed (boxes.erase moving)) := by
  intro d p hp q hq hl
  rcases Finset.mem_insert.mp hq with he | hq
  · exact Finset.mem_insert.mpr (Or.inl he)
  obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  refine ⟨hne, ?_⟩
  rcases Finset.mem_insert.mp hp with he | hp
  · subst p
    rcases hnew d with ⟨a, ha, hla⟩ | hempty
    · exact hclosed d a ha q hq (hl.trans hla)
    · exact False.elim (hempty q hq hl)
  · exact hclosed d p (Finset.mem_of_mem_erase hp) q hq hl

theorem extended_reverse_convex {forward : Direction}
    {signal previous extra stop landed : Cell w h}
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (ha : Adjacent forward signal landed) :
    LineConvex (insert landed (({signal, previous, extra, stop} : Finset (Cell w h)).erase stop)) := by
  have hs : signal ≠ stop := by intro h; have hp := hc.2.2.2; rw [h] at hp; omega
  have hp : previous ≠ stop := by intro h; exact hc.2.1 (h ▸ hc.2.2.1)
  have hl := he.lane
  simp only [opposite_lane] at hl
  have he' : extra ≠ stop := by
    intro h
    exact hc.2.1 ((hl.symm.trans (congrArg forward.lane h)).trans hc.2.2.1)
  have hc' := extended_reverse_lineConvex hc he ha
  rw [Finset.erase_insert_of_ne hs, Finset.erase_insert_of_ne hp,
    Finset.erase_insert_of_ne he', Finset.erase_singleton]
  convert hc' using 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
  tauto

theorem extended_forward_convex {forward : Direction}
    {signal previous extra stop landed : Cell w h}
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (ha : Adjacent forward landed stop) :
    LineConvex (insert landed (({signal, previous, extra, stop} : Finset (Cell w h)).erase signal)) := by
  have hs : stop ≠ signal := by intro h; have hp := hc.2.2.2; rw [h] at hp; omega
  have hp : previous ≠ signal := by intro h; exact hc.2.1 (congrArg forward.lane h)
  have hl := he.lane
  simp only [opposite_lane] at hl
  have he' : extra ≠ signal := by intro h; exact hc.2.1 (hl.symm.trans (congrArg forward.lane h))
  have hc' := extended_forward_lineConvex hc he ha
  rw [Finset.erase_insert_eq_erase, Finset.erase_insert_of_ne hp,
    Finset.erase_insert_of_ne he', Finset.erase_eq_of_notMem
      (show signal ∉ ({stop} : Finset (Cell w h)) from fun hm => hs (Finset.mem_singleton.mp hm).symm)]
  convert hc' using 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

end Wire

namespace Source.WireFault

variable {storage : Bool} {I : Instance} {S : Stock I}

/-- A current displaced pin takes its one further attraction step. -/
def moveAdded (F : WireFault storage I S)
    (moving landed : Cell (layout storage I).width (layout storage I).height) : WireFault storage I S :=
  {F with added := insert landed (F.added.erase moving)}

theorem moveAdded_boxes (F : WireFault storage I S)
    (moving landed : Cell (layout storage I).width (layout storage I).height)
    (hbase : moving ∉ (S.boxes storage) \ F.removed) :
    (F.moveAdded moving landed).boxes = insert landed (F.boxes.erase moving) := by
  change ((S.boxes storage) \ F.removed) ∪ insert landed (F.added.erase moving) =
    insert landed ((((S.boxes storage) \ F.removed) ∪ F.added).erase moving)
  rw [Finset.union_insert, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hbase]

/-- A second original pin is consumed by the single attraction step. -/
def movePin (F : WireFault storage I S)
    (moving landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (moving.1.val, moving.2.val) ∈ (layout storage I).pins) : WireFault storage I S where
  removed := insert moving F.removed
  added := insert landed (F.added.erase moving)
  signal := F.signal
  removed_pin := by
    intro p hp
    rcases Finset.mem_insert.mp hp with he | hp
    · exact he ▸ hpin
    · exact F.removed_pin p hp
  signal_raw := F.signal_raw

theorem movePin_boxes (F : WireFault storage I S)
    (moving landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (moving.1.val, moving.2.val) ∈ (layout storage I).pins) :
    (F.movePin moving landed hpin).boxes = insert landed (F.boxes.erase moving) := by
  change ((S.boxes storage) \ insert moving F.removed) ∪ insert landed (F.added.erase moving) =
    insert landed ((((S.boxes storage) \ F.removed) ∪ F.added).erase moving)
  rw [Finset.sdiff_insert, Finset.union_insert, Finset.erase_union_distrib]

/-- The concrete fault update is dead once its replacement cluster is convex and
its new perpendicular line has been checked against the old inventory. -/
theorem replacement_deadStock (F G : WireFault storage I S)
    (moving landed : Cell (layout storage I).width (layout storage I).height)
    (hboxes : G.boxes = insert landed (F.boxes.erase moving))
    (hsignal : G.signal.1.val < (layout storage I).rackX - 1)
    (hland : ∀ p ∈ G.added, p.1.val < (layout storage I).rackX - 1)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner, G.boxes⟩)
    (cluster : Finset (Cell (layout storage I).width (layout storage I).height))
    (hsub : cluster ⊆ F.boxes) (hclosed : Wire.LineClosed cluster F.boxes)
    (hconvex : Wire.LineConvex (insert landed (cluster.erase moving)))
    (hsig : G.signal ∈ insert landed (cluster.erase moving))
    (hadded : G.added ⊆ insert landed (cluster.erase moving))
    (hnew : ∀ (d : Direction),
      (∃ p ∈ cluster, d.lane landed = d.lane p) ∨
      ∀ q ∈ F.boxes, d.lane q = d.lane landed → False) :
    Wire.DeadStock G.boxes (Protected storage I) := by
  apply G.deadStock hsignal hland hregister hprotected (insert landed (cluster.erase moving))
    ?_ hconvex ?_ hsig hadded
  · intro p hp
    rw [hboxes]
    rcases Finset.mem_insert.mp hp with he | hp
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hp).1, hsub (Finset.mem_of_mem_erase hp)⟩)
  · rw [hboxes]
    exact hclosed.replace moving landed hnew

end Source.WireFault

namespace Source

/-- A fault with one possible attraction cannot finish when every such attraction
leaves a dead inventory with the consumed original pin still absent. -/
theorem reject_after_next_dead (storage : Bool) (I : Instance)
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable s final)
    (hgoal : final.boxes = (puzzle storage I).board.goals)
    (missing : Cell (layout storage I).width (layout storage I).height)
    (hpin : (missing.1.val, missing.2.val) ∈ (layout storage I).pins)
    (hmissing : missing ∉ s.boxes)
    (hnext : ∀ (d : Direction)
      (u : PushFS.State (layout storage I).width (layout storage I).height) (n k : ℕ)
      (r : Slide d u n k) (hn : 0 < n) (hk : 0 < k), u.boxes = s.boxes → u.player ∉ u.boxes →
      Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ →
      Wire.DeadStock r.boxes (Protected storage I) ∧ missing ∉ r.boxes) : False := by
  have hi : ∀ u, Reachable s u → Reachable u final → u.boxes = s.boxes := by
    intro u hu
    induction hu with
    | refl => exact fun _ => rfl
    | @tail u v hu hstep ih =>
      intro hv
      have hub := ih ((Relation.ReflTransGen.single hstep).trans hv)
      obtain ⟨d, hm⟩ := hstep
      cases hm with
      | walk _ _ _ hb => exact hb.trans hub
      | push hvalid hn hk r hplayer hboxes =>
        have hvprefix := hprefix.trans (hu.tail ⟨d, Move.push hvalid hn hk r hplayer hboxes⟩)
        have hprot := protected_prefix storage I hvprefix hv hgoal
        have hprot' : Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ :=
          hprot.of_boxes_eq hboxes.symm
        obtain ⟨hd, hm⟩ := hnext d u _ _ r hn hk hub hvalid hprot'
        exact False.elim (deadStock_reject storage I hvprefix hv hgoal
          (by rw [hboxes]; exact hd) missing hpin (by rw [hboxes]; exact hm))
  have hb := hi final hsuffix .refl
  apply hmissing
  rw [← hb, hgoal]
  apply ((layout storage I).mem_raster _ _).mpr
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hpin))

end Source
end PushPuzzle.PushPush.Doors
