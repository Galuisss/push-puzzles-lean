/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutEndpointsRow
public import PushPush.Doors.WireReadoutFree

/-! A signal arriving beside a terminal pin on the wrong row forms a closed pair. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

private theorem goals_private_pin (storage : Bool) (I : Instance)
    {p : Cell (layout storage I).width (layout storage I).height}
    (hx : p.1.val < (layout storage I).rackX - 1)
    (hp : p ∈ (puzzle storage I).board.goals) :
    (p.1.val, p.2.val) ∈ (layout storage I).pins := by
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact hp
      · have hc := (layout storage I).rack_column hp
        omega
    · have hc := (layout storage I).blockers_column hp
      omega
  · obtain ⟨row, _, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hc := congrArg Prod.fst he
    dsimp at hc
    omega

private theorem deadStock_reject_extra (storage : Bool) (I : Instance)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable s t)
    (hgoal : t.boxes = (puzzle storage I).board.goals)
    (hd : Wire.DeadStock s.boxes (Protected storage I))
    (extra : Cell (layout storage I).width (layout storage I).height)
    (hextra : extra ∈ s.boxes) (hnot : extra ∉ (puzzle storage I).board.goals) : False := by
  have hb := hd.reachable_boxes rfl hsuffix (fun u hsu hut =>
    protected_prefix storage I (hprefix.trans hsu) hut hgoal)
  exact hnot ((hb ▸ hgoal) ▸ hextra)

namespace Stock

variable {I : Instance}

/-- A private adjacent pin-signal pair in a free neighbouring column is a complete dead stock. -/
theorem private_pair_deadStock (storage : Bool) (S : Stock I)
    (signal pin : Cell (layout storage I).width (layout storage I).height)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (ha : Adjacent .east pin signal)
    (hprivate : signal.1.val < (layout storage I).rackX - 1)
    (hfree : ∀ p ∈ (layout storage I).pins, p.1 ≠ signal.1.val)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I (S.canonical storage)) :
    Wire.DeadStock (S.boxes storage) (Protected storage I) := by
  let F : WireFault storage I S :=
    ⟨∅, ∅, signal, by simp, hsignal⟩
  let cluster : Finset (Cell (layout storage I).width (layout storage I).height) := {signal, pin}
  have hF : F.boxes = S.boxes storage := by simp [F, WireFault.boxes]
  have hsub : cluster ⊆ F.boxes := by
    intro p hp
    rw [hF]
    simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
    apply ((layout storage I).mem_raster _ _).mpr
    rcases hp with rfl | rfl
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hsignal)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hpin)))
  have hclosed : Wire.LineClosed cluster F.boxes := by
    intro d p hp q hq hl
    rw [hF] at hq
    by_cases hline : d.lane p = d.lane pin
    · let base : PushFS.State (layout storage I).width (layout storage I).height :=
        ⟨(layout storage I).corner, S.boxes storage⟩
      rcases (S.pin_line_readout storage (s := base) rfl d pin q hpin (hl.trans hline)).mp hq with hh | hh
      · simp [cluster, hh]
      · have hh : q = signal := by
          have hh := hh.trans hsignal.symm
          exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
        simp [cluster, hh]
    · have hp : p = signal := by
        simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
        exact hp.resolve_right (fun he => hline (he ▸ rfl))
      subst p
      have hv : d = .north ∨ d = .south := by
        by_contra hv
        have hh : d = .east ∨ d = .west := by cases d <;> simp_all
        apply hline
        rcases hh with rfl | rfl <;> exact congrArg Fin.val ha.2
      have hx : q.1.val = signal.1.val := by rcases hv with rfl | rfl <;> exact hl
      have hraw := ((layout storage I).mem_raster _ _).mp hq
      rcases Finset.mem_union.mp hraw with hstationary | hsig
      · exact False.elim (S.private_clear storage (by omega)
          (fun h => hfree _ h hx) hstationary)
      · have he : q = signal := by
          have he := (Finset.mem_singleton.mp hsig).trans hsignal.symm
          exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
        simp [cluster, he]
  have hd := F.deadStock hprivate (by simp [F]) hregister
    (by simpa only [hF, canonical] using hprotected) cluster hsub
    (by simpa only [cluster, Finset.pair_comm] using Wire.pair_lineConvex ha) hclosed
    (by simp [F, cluster]) (by simp [F])
  simpa only [hF] using hd

/-- Pushing a working-column signal horizontally along a terminal-pin row is fatal. -/
theorem terminal_row_signal_reject (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hrow : S.signal.2 = (wireStopRaw (layout storage I) index.val
      (layout storage I).wires[index] 5).2)
    (hworking : S.signal.1 = (layout storage I).rackX - 1)
    (hregister : ∀ door, S.register door ≠ .erase)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable t final)
    (hgoal : final.boxes = (puzzle storage I).board.goals)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hmove : Step s t) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal)
    (hd : d = .east ∨ d = .west) : False := by
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let pin := wireStop storage I index.val index.isLt e he 5
  let signal := r.cell ⟨1, by omega⟩
  have hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins := by
    apply wireStopRaw_pin_mem storage I _ 5 (by decide)
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hsigx : signal.1.val = (layout storage I).rackX - 1 :=
    (congrArg Prod.fst hfirst).trans hworking
  have hsigrow : signal.2 = pin.2 := Fin.ext ((congrArg Prod.snd hfirst).trans hrow)
  have hgap : pin.1.val + 3 ≤ signal.1.val := by
    have hi := index.isLt
    change Layout.wireC index.val + 3 ≤ _
    rw [hsigx]
    dsimp [Layout.wireC, Layout.rackX]
    omega
  obtain ⟨rfl, hdw, hstop⟩ := S.row_signal_slide storage signal pin hfirst hpin hsigrow hgap
    hstock r hn hk (by rw [← hb]; exact ht.interior) rfl hd
  let landed := r.cell ⟨1 + k, by omega⟩
  have ha : Adjacent .east pin landed := by
    have ha := hstop.reverse
    simpa only [hdw, Direction.opposite] using ha
  have hlandx : landed.1.val = Layout.wireC index.val + 1 := ha.1
  have hprivate : landed.1.val < (layout storage I).rackX - 1 := by
    have hi := index.isLt
    dsimp [Layout.wireC, Layout.rackX] at hlandx ⊢
    omega
  have hfree : ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val := by
    intro p hp
    rw [hlandx]
    exact ((layout storage I).pins_not_free_column index.val hp).2.2
  have hclear : signal ∉ S.stationary storage := by
    intro hp
    have heq := S.stationary_at_pin_row storage hpin hsigrow hp
    have hx := congrArg (fun p => p.1.val) heq
    omega
  let next : Stock I := {S with signal := (landed.1.val, landed.2.val)}
  have hboxes : t.boxes = next.boxes storage := by
    have hu := S.boxes_setSignal storage signal landed hfirst.symm hclear
    rw [hb, single_slide_boxes r, hstock]
    simpa only [next, signal, landed, Nat.add_comm] using hu.symm
  have hd := next.private_pair_deadStock storage landed pin rfl hpin ha hprivate hfree hregister
    (ht.of_boxes_eq hboxes.symm)
  apply deadStock_reject_extra storage I (hprefix.trans (.single hmove)) hsuffix hgoal
    (by rw [hboxes]; exact hd) landed
  · rw [hboxes]
    exact ((layout storage I).mem_raster _ _).mpr
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · intro hgoalbox
    exact hfree _ (goals_private_pin storage I hprivate hgoalbox) rfl

end Stock
end PushPuzzle.PushPush.Doors.Source
