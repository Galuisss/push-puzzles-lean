/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutExtended

/-! Complete successful-suffix rejection of a same-sign four-box attraction. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.ExtendedFault

open PushFS (Cell Direction Adjacent)

variable {storage : Bool} {I : Instance} {S : Stock I}

def fault (E : ExtendedFault storage I S) : WireFault storage I S :=
  WireFault.single E.signal E.removed E.near E.removed_pin E.signal_raw

def cluster (E : ExtendedFault storage I S) :
    Finset (Cell (layout storage I).width (layout storage I).height) :=
  {E.near, E.signal, E.extra, E.remote}

private theorem normal_vertical
    (E : ExtendedFault storage I S) : E.normal = .north ∨ E.normal = .south := by
  have ha := E.nearAdj
  have hp := E.extendedCorner.2.1
  cases hn : E.normal <;> rcases E.horizontal with hd | hd <;>
    simp_all [Adjacent, Direction.lane]

theorem signal_near_column (E : ExtendedFault storage I S) : E.signal.1 = E.near.1 := by
  have ha := E.nearAdj
  rcases E.normal_vertical with hd | hd <;> rw [hd] at ha <;> exact ha.1.symm

private theorem removed_near_column (E : ExtendedFault storage I S) : E.removed.1 = E.near.1 := by
  have hl := E.normalCorner.2.2.1
  have hs := E.signal_near_column
  apply Fin.ext
  rcases E.normal_vertical with hd | hd <;> rw [hd] at hl <;> exact hl.trans (congrArg Fin.val hs)

private theorem signal_ne_removed (E : ExtendedFault storage I S) : E.signal ≠ E.removed := by
  intro he
  have hp := E.normalCorner.2.2.2
  rw [he] at hp
  omega

private theorem extra_ne_removed (E : ExtendedFault storage I S) : E.extra ≠ E.removed := by
  intro he
  exact E.normalCorner.2.1 (he ▸ E.normalCorner.2.2.1)

private theorem pin_mem_boxes (p : Cell (layout storage I).width (layout storage I).height)
    (hp : (p.1.val, p.2.val) ∈ (layout storage I).pins) : p ∈ S.boxes storage :=
  ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))))

theorem subset_boxes (E : ExtendedFault storage I S) : E.cluster ⊆ E.fault.boxes := by
  have hsignal : E.signal ∈ S.boxes storage :=
    ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_right _ (Finset.mem_singleton.mpr E.signal_raw))
  intro p hp
  rw [fault, WireFault.single_boxes]
  simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with he | he | he | he
  · exact Finset.mem_insert.mpr (Or.inl he)
  · subst p
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨E.signal_ne_removed, hsignal⟩)
  · subst p
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨E.extra_ne_removed, pin_mem_boxes _ E.extra_pin⟩)
  · subst p
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨E.remote_ne_removed, pin_mem_boxes _ E.remote_pin⟩)

theorem lineClosed (E : ExtendedFault storage I S) : Wire.LineClosed E.cluster E.fault.boxes := by
  apply E.fault.lineClosed_of_anchors E.cluster (by simp [fault, WireFault.single, cluster])
    (by intro p hp; have he := Finset.mem_singleton.mp hp; simp [he, cluster])
  intro d p hp
  have hpin : ∀ pin : Cell (layout storage I).width (layout storage I).height,
      (pin.1.val, pin.2.val) ∈ (layout storage I).pins →
      (pin ∈ E.cluster ∨ pin = E.removed) → d.lane p = d.lane pin → E.fault.Anchored E.cluster d p := by
    intro pin hpin hm hl
    exact Or.inl ⟨pin, hpin, hm.imp_right (fun he => by simp [fault, WireFault.single, he]), hl⟩
  have hsignal : d.lane p = d.lane E.signal → E.fault.Anchored E.cluster d p := by
    intro hl
    rcases Wire.corner_lane_cover E.normalCorner d with he | he
    · exact hpin E.extra E.extra_pin (Or.inl (by simp [cluster])) (hl.trans he)
    · exact hpin E.removed E.removed_pin (Or.inr rfl) (hl.trans he)
  simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with he | he | he | he
  · subst p
    rcases Wire.corner_lane_cover E.extendedCorner d with he | he
    · exact hsignal he
    · exact hpin E.remote E.remote_pin (Or.inl (by simp [cluster])) he
  · subst p
    exact hsignal rfl
  · subst p
    exact hpin E.extra E.extra_pin (Or.inl (by simp [cluster])) rfl
  · subst p
    exact hpin E.remote E.remote_pin (Or.inl (by simp [cluster])) rfl

private theorem near_not_base (E : ExtendedFault storage I S) : E.near ∉ S.boxes storage := by
  let base := S.canonical storage
  have hc := S.corner_lineClosed storage (s := base) rfl E.normal E.signal E.extra E.removed
    E.signal_raw E.normalCorner E.extra_pin E.removed_pin
  intro hn
  apply Wire.corner_forward_isolated E.normalCorner E.nearAdj
  exact hc E.normal E.signal (by simp) E.near hn E.nearAdj.lane

theorem landing_info (E : ExtendedFault storage I S)
    (landed : Cell (layout storage I).width (layout storage I).height)
    (ha : Adjacent E.forward E.near landed ∨ Adjacent E.forward landed E.remote) :
    landed.1.val < (layout storage I).rackX - 1 ∧ landed.1.val ≠ E.near.1.val ∧
      ∀ (d : Direction), (∃ p ∈ E.cluster, d.lane landed = d.lane p) ∨
        ∀ q ∈ E.fault.boxes, d.lane q = d.lane landed → False := by
  have hmargin := (layout storage I).pins_west E.remote_pin
  have hg := E.extendedCorner.2.2.2
  have hl := E.extendedCorner.2.2.1
  have hy : landed.2 = E.near.2 := by
    rcases ha with ha | ha
    · rcases E.horizontal with hd | hd <;> rw [hd] at ha <;> exact ha.2
    · rcases E.horizontal with hd | hd <;> rw [hd] at ha hl <;>
        exact ha.2.symm.trans (Fin.ext hl)
  have hprivate : landed.1.val < (layout storage I).rackX - 1 := by
    have hn := E.near_margin
    rcases ha with ha | ha <;> rcases E.horizontal with hd | hd <;>
      rw [hd] at ha <;> simp only [Adjacent] at ha <;> dsimp at hmargin <;> omega
  have hne : landed.1.val ≠ E.near.1.val := by
    rcases ha with ha | ha <;> rcases E.horizontal with hd | hd <;>
      rw [hd] at ha hg <;> simp only [Adjacent, Direction.position] at ha hg <;> omega
  have hfree : ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val :=
    ha.elim (E.free_near landed) (E.free_remote landed)
  refine ⟨hprivate, hne, ?_⟩
  intro d
  cases d with
  | east => exact Or.inl ⟨E.near, by simp [cluster], congrArg Fin.val hy⟩
  | west => exact Or.inl ⟨E.near, by simp [cluster], congrArg Fin.val hy⟩
  | north | south =>
    apply Or.inr
    intro q hq hcol
    rcases Finset.mem_union.mp hq with hbase | hadded
    · have hqbase := (Finset.mem_sdiff.mp hbase).1
      have hqraw := ((layout storage I).mem_raster _ _).mp hqbase
      have hsigx : S.signal.1 ≠ landed.1.val := by
        have hx := congrArg Prod.fst E.signal_raw
        have hs := congrArg Fin.val E.signal_near_column
        dsimp at hx
        omega
      exact S.raw_column_empty storage landed.1.val hprivate hfree hsigx hcol hqraw
    · have heq : q = E.near := Finset.mem_singleton.mp hadded
      subst q
      exact hne hcol.symm

private theorem certifyReplacement (E : ExtendedFault storage I S) (G : WireFault storage I S)
    (moving landed : Cell (layout storage I).width (layout storage I).height)
    (hboxes : G.boxes = insert landed (E.fault.boxes.erase moving))
    (hsignal : G.signal = E.signal)
    (hadded : G.added = insert landed (E.fault.added.erase moving))
    (hsigne : E.signal ≠ moving)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner, G.boxes⟩)
    (hconvex : Wire.LineConvex (insert landed (E.cluster.erase moving)))
    (ha : Adjacent E.forward E.near landed ∨ Adjacent E.forward landed E.remote) :
    Wire.DeadStock G.boxes (Protected storage I) ∧ E.removed ∉ G.boxes := by
  have info := E.landing_info landed ha
  have hremoved : E.removed ∉ E.fault.boxes := by
    exact WireFault.single_missing E.signal E.removed E.near E.removed_pin E.signal_raw E.removed_ne_near
  have hne : E.removed ≠ landed := by
    intro he
    have hx := congrArg Fin.val E.removed_near_column
    rw [he] at hx
    exact info.2.1 hx
  refine ⟨?_, ?_⟩
  · apply E.fault.replacement_deadStock G moving landed hboxes
      (by rw [hsignal]; exact E.signal_private) ?_ hregister hprotected E.cluster E.subset_boxes E.lineClosed
      hconvex ?_ ?_ info.2.2
    · intro p hp
      rw [hadded] at hp
      rcases Finset.mem_insert.mp hp with he | hp
      · exact he ▸ info.1
      · have he : p = E.near := Finset.mem_singleton.mp (Finset.mem_of_mem_erase hp)
        rw [he]
        have hn := E.near_margin
        omega
    · rw [hsignal]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsigne, by simp [cluster]⟩)
    · intro p hp
      rw [hadded] at hp
      rcases Finset.mem_insert.mp hp with he | hp
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hp).1, by
            have he : p = E.near := Finset.mem_singleton.mp (Finset.mem_of_mem_erase hp)
            simp [he, cluster]⟩)
  · rw [hboxes]
    intro hp
    rcases Finset.mem_insert.mp hp with he | hp
    · exact hne he
    · exact hremoved (Finset.mem_of_mem_erase hp)

/-- Any positive protected slide of a same-sign fault is its sole attraction,
and both choices end in a completely dead stock with the first pin absent. -/
theorem after_slide_dead (E : ExtendedFault storage I S)
    (hregister : ∀ door, S.register door ≠ .erase)
    (hprotected : Protected storage I ⟨(layout storage I).corner, E.fault.boxes⟩)
    {u : PushFS.State (layout storage I).width (layout storage I).height}
    {d : Direction} {n k : ℕ} (r : Slide d u n k) (hn : 0 < n) (hk : 0 < k)
    (hb : u.boxes = E.fault.boxes) (hv : u.player ∉ u.boxes)
    (ht : Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩) :
    Wire.DeadStock r.boxes (Protected storage I) ∧ E.removed ∉ r.boxes := by
  have hfirst := E.fault.slide_first_in_cluster E.signal_private
    (by intro p hp; have he : p = E.near := Finset.mem_singleton.mp hp
        rw [he]; have hm := E.near_margin; omega)
    hregister hprotected E.cluster E.lineClosed (by simp [fault, WireFault.single, cluster])
    (by intro p hp; have he := Finset.mem_singleton.mp hp; simp [he, cluster]) d u n k r hn hk hb hv ht
  have hclosed : Wire.LineClosed E.cluster u.boxes := by rw [hb]; exact E.lineClosed
  have hread := Wire.extended_corner_slide r hn hk ht.interior E.near E.signal E.extra E.remote
    E.extendedCorner E.extraAdj hclosed hfirst
  have hn1 := hread.1
  clear hread
  subst n
  have hread := Wire.extended_corner_slide r hn hk ht.interior E.near E.signal E.extra E.remote
    E.extendedCorner E.extraAdj hclosed hfirst
  let landed := r.cell ⟨1 + k, by omega⟩
  rcases hread.2 with ⟨hd, hf, ha⟩ | ⟨hd, hf, ha⟩
  · have hal : Adjacent E.forward landed E.remote := by simpa only [hd] using ha
    let G := E.fault.moveAdded E.near landed
    have hG : G.boxes = insert landed (E.fault.boxes.erase E.near) :=
      E.fault.moveAdded_boxes E.near landed (fun hp => E.near_not_base (Finset.mem_sdiff.mp hp).1)
    have hresult : r.boxes = G.boxes := by
      rw [hG, single_slide_boxes r, hf, hb]
      simp only [landed, Nat.add_comm]
    have hprot : Protected storage I ⟨(layout storage I).corner, G.boxes⟩ :=
      ht.of_boxes_eq hresult.symm
    have hr := E.certifyReplacement G E.near landed hG rfl rfl E.nearAdj.ne hregister hprot
      (Wire.extended_forward_convex E.extendedCorner E.extraAdj hal) (Or.inr hal)
    simpa only [hresult] using hr
  · have hal : Adjacent E.forward E.near landed := by
      have h := ha.reverse
      simpa only [hd, Direction.opposite_opposite] using h
    let G := E.fault.movePin E.remote landed E.remote_pin
    have hG : G.boxes = insert landed (E.fault.boxes.erase E.remote) :=
      E.fault.movePin_boxes E.remote landed E.remote_pin
    have hresult : r.boxes = G.boxes := by
      rw [hG, single_slide_boxes r, hf, hb]
      simp only [landed, Nat.add_comm]
    have hprot : Protected storage I ⟨(layout storage I).corner, G.boxes⟩ :=
      ht.of_boxes_eq hresult.symm
    have hsigne : E.signal ≠ E.remote := by
      intro he
      exact E.extendedCorner.2.1 (he ▸ E.extendedCorner.2.2.1)
    have hr := E.certifyReplacement G E.remote landed hG rfl rfl hsigne hregister hprot
      (Wire.extended_reverse_convex E.extendedCorner E.extraAdj hal) (Or.inl hal)
    simpa only [hresult] using hr

/-- Same-sign faults cannot occur on a successful exact-storage execution. -/
theorem reject (E : ExtendedFault storage I S)
    (hregister : ∀ door, S.register door ≠ .erase)
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (hboxes : s.boxes = insert E.near ((S.boxes storage).erase E.removed))
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable s final)
    (hgoal : final.boxes = (puzzle storage I).board.goals) : False := by
  have hb : s.boxes = E.fault.boxes := by simpa only [fault, WireFault.single_boxes] using hboxes
  have hprotected : Protected storage I ⟨(layout storage I).corner, E.fault.boxes⟩ :=
    (protected_prefix storage I hprefix hsuffix hgoal).of_boxes_eq hb.symm
  apply reject_after_next_dead storage I hprefix hsuffix hgoal E.removed E.removed_pin
    (by
      rw [hb]
      exact WireFault.single_missing E.signal E.removed E.near E.removed_pin
        E.signal_raw E.removed_ne_near)
  intro d u n k r hn hk hbox hu ht
  exact E.after_slide_dead hregister hprotected r hn hk (hbox.trans hb) hu ht

end PushPuzzle.PushPush.Doors.Source.ExtendedFault
