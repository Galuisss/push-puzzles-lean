/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutPins
public import PushPush.Doors.PhysicalChamber

/-! A private pin fault with a closed convex active cluster is a complete dead stock. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem Protected.of_boxes_eq {storage : Bool} {I : Instance}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (hb : t.boxes = s.boxes) : Protected storage I t := by
  rcases s with ⟨player, boxes⟩
  rcases t with ⟨other, boxes'⟩
  change boxes' = boxes at hb
  subst boxes'
  exact ⟨hs.interior, hs.supported, hs.rack, hs.dividers, hs.caps⟩

/-- Original routing pins removed from their cells, with their current private landing cells. -/
structure WireFault (storage : Bool) (I : Instance) (stock : Stock I) where
  /-- Consumed original pins. -/
  removed : Finset (Cell (layout storage I).width (layout storage I).height)
  /-- Their current landing cells. -/
  added : Finset (Cell (layout storage I).width (layout storage I).height)
  /-- The original travelling signal. -/
  signal : Cell (layout storage I).width (layout storage I).height
  /-- Every removed cell belongs to the literal emitted pin set. -/
  removed_pin : ∀ p ∈ removed, (p.1.val, p.2.val) ∈ (layout storage I).pins
  /-- The signal retains its original physical identity. -/
  signal_raw : (signal.1.val, signal.2.val) = stock.signal

namespace WireFault

variable {storage : Bool} {I : Instance} {S : Stock I}

def boxes (F : WireFault storage I S) :
    Finset (Cell (layout storage I).width (layout storage I).height) :=
  ((S.boxes storage) \ F.removed) ∪ F.added

/-- A line through the active cluster is tracked by an original pin, or is empty
in the unchanged source inventory. Removed original pins remain valid line anchors. -/
def Anchored (F : WireFault storage I S)
    (cluster : Finset (Cell (layout storage I).width (layout storage I).height))
    (d : Direction) (p : Cell (layout storage I).width (layout storage I).height) : Prop :=
  (∃ pin : Cell (layout storage I).width (layout storage I).height,
    (pin.1.val, pin.2.val) ∈ (layout storage I).pins ∧
      (pin ∈ cluster ∨ pin ∈ F.removed) ∧ d.lane p = d.lane pin) ∨
    ∀ q ∈ S.boxes storage, d.lane q = d.lane p → False

theorem lineClosed_of_anchors (F : WireFault storage I S)
    (cluster : Finset (Cell (layout storage I).width (layout storage I).height))
    (hsig : F.signal ∈ cluster) (hadded : F.added ⊆ cluster)
    (hanchors : ∀ d p, p ∈ cluster → F.Anchored cluster d p) :
    Wire.LineClosed cluster F.boxes := by
  intro d p hp q hq hl
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨hbase, hnotremoved⟩ := Finset.mem_sdiff.mp hq
    rcases hanchors d p hp with ⟨pin, hpin, hm, hpl⟩ | hempty
    · let base : PushFS.State (layout storage I).width (layout storage I).height :=
        ⟨(layout storage I).corner, S.boxes storage⟩
      rcases (S.pin_line_readout storage (s := base) rfl d pin q hpin (hl.trans hpl)).mp hbase with he | he
      · subst q
        exact hm.resolve_right hnotremoved
      · have heq : q = F.signal :=
          Prod.ext (Fin.ext (congrArg Prod.fst (he.trans F.signal_raw.symm)))
            (Fin.ext (congrArg Prod.snd (he.trans F.signal_raw.symm)))
        exact heq ▸ hsig
    · exact False.elim (hempty q hbase hl)
  · exact hadded hq

theorem working_membership (F : WireFault storage I S)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1) :
    p ∈ F.boxes ↔ p ∈ S.boxes storage := by
  have hne : p ∉ F.removed := by
    intro hp
    have hw := (layout storage I).pins_west (F.removed_pin p hp)
    dsimp at hw
    omega
  have hne' : p ∉ F.added := by intro hp; have hw := hland p hp; omega
  simp only [boxes, Finset.mem_union, Finset.mem_sdiff, hne', or_false]
  exact ⟨And.left, fun hp => ⟨hp, hne⟩⟩

private theorem solo_column (F : WireFault storage I S)
    (hsignal : F.signal.1.val < (layout storage I).rackX - 1)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    {s : PushFS.State (layout storage I).width (layout storage I).height} (hs : s.boxes = F.boxes)
    (door : Fin I.doors.length) :
    Room.SoloColumn s (S.doorPoint storage door).1
      (doorBase door.val + (layout storage I).shift) (S.register door).row := by
  let base : PushFS.State (layout storage I).width (layout storage I).height := ⟨s.player, S.boxes storage⟩
  have hout : S.SignalOutsideDoor storage door := by
    intro p hx _ _ he
    have hx' := congrArg Prod.fst (he.trans F.signal_raw.symm)
    dsimp at hx'
    omega
  have hc := S.solo_column (storage := storage) door (s := base) rfl hout
  intro p hx hlo hhi
  rw [hs, F.working_membership hland p (congrArg Fin.val hx)]
  exact hc p hx hlo hhi

/-- Every successful-prefix movement of the fault inventory must begin in its active cluster. -/
theorem slide_first_in_cluster (F : WireFault storage I S)
    (hsignal : F.signal.1.val < (layout storage I).rackX - 1)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner, F.boxes⟩)
    (cluster : Finset (Cell (layout storage I).width (layout storage I).height))
    (hclosed : Wire.LineClosed cluster F.boxes)
    (hsig : F.signal ∈ cluster) (hbad : F.added ⊆ cluster)
    (d : Direction) (s : PushFS.State (layout storage I).width (layout storage I).height)
    (n k : ℕ) (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : s.boxes = F.boxes) (hv : s.player ∉ s.boxes)
    (ht : Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩) :
    r.cell ⟨1, by omega⟩ ∈ cluster := by
  by_contra hnotcluster
  let target : PushFS.State (layout storage I).width (layout storage I).height :=
    ⟨r.cell ⟨1, by omega⟩, r.boxes⟩
  have hs : Protected storage I s := hprotected.of_boxes_eq hb
  have ht' : Protected storage I target := ht
  have hinterior : ∀ p ∈ r.boxes, ¬ Boundary p := ht.interior
  have hframe := hs.slide_avoids_frame ht' r hn hk hv rfl
  have hfirstb : r.cell ⟨1, by omega⟩ ∈ r.before :=
    Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hfirst : r.cell ⟨1, by omega⟩ ∈ F.boxes := hb ▸ r.occupied ⟨0, hn⟩
  have hpinblocked : ∀ pin : Cell (layout storage I).width (layout storage I).height,
      (pin.1.val, pin.2.val) ∈ (layout storage I).pins → r.cell ⟨1, by omega⟩ = pin → False := by
    intro pin hpin hfirsteq
    obtain ⟨stop, hstop, ha⟩ := r.exists_stopper hn hinterior
    have hstopb : stop ∈ F.boxes := hb ▸ hstop
    have hstoplane : d.lane stop = d.lane pin := by
      have hf := r.lane ⟨1, by omega⟩
      rw [hfirsteq] at hf
      exact ha.lane.trans ((r.lane _).trans hf.symm)
    have hstopcluster : stop ∈ cluster := by
      rcases Finset.mem_union.mp hstopb with he | he
      · have hbase := (Finset.mem_sdiff.mp he).1
        let base : PushFS.State (layout storage I).width (layout storage I).height :=
          ⟨s.player, S.boxes storage⟩
        rcases (S.pin_line_readout storage (s := base) rfl d pin stop hpin hstoplane).mp hbase with heq | heq
        · have hp := r.position ⟨1, by omega⟩
          have hl := r.position ⟨n + k, by omega⟩
          have hq := ha.position
          rw [hfirsteq] at hp
          change d.position pin = d.position s.player + (1 : ℕ) at hp
          change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hl
          rw [heq] at hq
          omega
        · have heq' : stop = F.signal :=
            Prod.ext (Fin.ext (congrArg Prod.fst (heq.trans F.signal_raw.symm)))
              (Fin.ext (congrArg Prod.snd (heq.trans F.signal_raw.symm)))
          exact heq' ▸ hsig
      · exact hbad he
    apply hnotcluster
    apply hclosed d stop hstopcluster _ hfirst
    simpa only [hfirsteq] using hstoplane.symm
  have hrest : r.cell ⟨1, by omega⟩ ∈ S.boxes storage \ F.removed := by
    rcases Finset.mem_union.mp hfirst with hrest | hadded
    · exact hrest
    · exact False.elim (hnotcluster (hbad hadded))
  have hstock := (Finset.mem_sdiff.mp hrest).1
  have hraw := ((layout storage I).mem_raster _ _).mp hstock
  rcases Finset.mem_union.mp hraw with hraw | hraw
  · rcases Finset.mem_union.mp hraw with hraw | hraw
    · rcases Finset.mem_union.mp hraw with hraw | hraw
      · rcases Finset.mem_union.mp hraw with hpin | hrack
        · exact hpinblocked _ hpin rfl
        · apply Finset.disjoint_left.mp hframe _ hfirstb
          exact ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_left _ hrack)
      · apply Finset.disjoint_left.mp hframe _ hfirstb
        exact ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_right _ hraw)
    · obtain ⟨door, _, he⟩ := Finset.mem_image.mp hraw
      have hfirsteq : r.cell ⟨1, by omega⟩ = S.doorPoint storage door := by
        apply Prod.ext <;> apply Fin.ext
        · exact (congrArg Prod.fst he).symm
        · exact (congrArg Prod.snd he).symm
      by_cases hd : d = .east ∨ d = .west
      · exact S.register_no_horizontal door hs ht' (hregister door) r hn hk hv rfl hfirsteq hd
      · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
        have hc := F.solo_column hsignal hland hb door
        have hroom : doorBase door.val + (layout storage I).shift + 90 < (layout storage I).height := by
          have hr := (layout storage I).translated_bounds
            (dividers_fit storage I (door_south_divider_mem storage I door.isLt))
          omega
        have hrow := Register.row_bounds (S.register door)
        have hcollision := Room.solo_collision r hn hk (S.doorPoint storage door).1
          (doorBase door.val + (layout storage I).shift) (S.register door).row hroom (by omega) hc
          (by rw [hfirsteq]; exact ⟨rfl, by dsimp [Stock.doorPoint]; omega⟩) hdv
        have hlastx : (r.cell ⟨n + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
          have hf := r.lane ⟨1, by omega⟩
          have hl := r.lane ⟨n + k, by omega⟩
          rw [hfirsteq] at hf
          rcases hdv with rfl | rfl <;> simp only [Direction.lane] at hf hl <;>
            dsimp [Stock.doorPoint] at hf <;> omega
        exact ht'.door_neighbors_empty door _ hlastx hcollision.2 (r.last_mem_boxes hn)
  · have he := Finset.mem_singleton.mp hraw
    have heq : r.cell ⟨1, by omega⟩ = F.signal :=
      Prod.ext (Fin.ext (congrArg Prod.fst (he.trans F.signal_raw.symm)))
        (Fin.ext (congrArg Prod.snd (he.trans F.signal_raw.symm)))
    exact hnotcluster (heq ▸ hsig)

/-- A private fault whose active cluster is closed and convex has no positive push. -/
theorem deadStock (F : WireFault storage I S)
    (hsignal : F.signal.1.val < (layout storage I).rackX - 1)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner, F.boxes⟩)
    (cluster : Finset (Cell (layout storage I).width (layout storage I).height))
    (hsub : cluster ⊆ F.boxes) (hconvex : Wire.LineConvex cluster)
    (hclosed : Wire.LineClosed cluster F.boxes)
    (hsig : F.signal ∈ cluster) (hbad : F.added ⊆ cluster) :
    Wire.DeadStock F.boxes (Protected storage I) := by
  intro d s n k r hn hk hb hv ht
  have hfirst := F.slide_first_in_cluster hsignal hland hregister hprotected cluster hclosed
    hsig hbad d s n k r hn hk hb hv ht
  have hdis := Wire.slide_avoids_cluster r hn hk ht.interior cluster
    (by rw [hb]; exact hsub) hconvex (by rw [hb]; exact hclosed)
  apply Finset.disjoint_left.mp hdis hfirst
  exact Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩

end WireFault

/-- A certified dead stock with a missing original pin cannot finish the storage target. -/
theorem deadStock_reject (storage : Bool) (I : Instance)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable s t)
    (hgoal : t.boxes = (puzzle storage I).board.goals)
    (hd : Wire.DeadStock s.boxes (Protected storage I))
    (missing : Cell (layout storage I).width (layout storage I).height)
    (hpin : (missing.1.val, missing.2.val) ∈ (layout storage I).pins)
    (hmissing : missing ∉ s.boxes) : False := by
  have hb := hd.reachable_boxes rfl hsuffix (fun u hsu hut =>
    protected_prefix storage I (hprefix.trans hsu) hut hgoal)
  have hm : missing ∈ t.boxes := by
    rw [hgoal]
    apply ((layout storage I).mem_raster _ _).mpr
    apply Finset.mem_union_left
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hpin)
  exact hmissing (hb ▸ hm)

end PushPuzzle.PushPush.Doors.Source
