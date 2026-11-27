/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourceForwardClear

/-! The complete seven-slide physical routing macro on the emitted source board. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

private theorem forward_wire_leg (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7)
    (hsignal : S.signal = wirePositionRaw (layout storage I) i e j.castSucc)
    (hregister : ((layout storage I).rackX - 1, e.target + (layout storage I).shift) ∉
      S.registerPoints storage) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := wirePositionRaw (layout storage I) i e j.succ} : Stock I).canonical storage) := by
  have hi := (List.mem_zipIdx' hei).1
  have he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
  let source := wirePosition storage I i hi e he j.castSucc
  let dest := wirePosition storage I i hi e he j.succ
  let stop := wireStop storage I i hi e he j
  let d := wireDirection (layout storage I) i e j
  have hsource := wirePosition_raw storage I i hi e he j.castSucc
  have hdest := wirePosition_raw storage I i hi e he j.succ
  have hstop := wireStop_raw storage I i hi e he j
  change (source.1.val, source.2.val) = wirePositionRaw (layout storage I) i e j.castSucc at hsource
  change (dest.1.val, dest.2.val) = wirePositionRaw (layout storage I) i e j.succ at hdest
  change (stop.1.val, stop.2.val) = wireStopRaw (layout storage I) i e j at hstop
  have hg := wire_leg_geometry (layout storage I) i e hi (wires_fit storage I he).1
    (wires_fit storage I he).2 j source dest stop hsource hdest hstop
  have hsb := (layout storage I).wirePath_interior hi e (wires_fit storage I he).1
    (wires_fit storage I he).2 (wirePositionRaw_mem _ i e j.castSucc)
  have hdb := (layout storage I).wirePath_interior hi e (wires_fit storage I he).1
    (wires_fit storage I he).2 (wirePositionRaw_mem _ i e j.succ)
  rw [← hsource] at hsb
  rw [← hdest] at hdb
  change 0 < source.1.val ∧ source.1.val < (layout storage I).width - 1 ∧
    0 < source.2.val ∧ source.2.val < (layout storage I).height - 1 at hsb
  change 0 < dest.1.val ∧ dest.1.val < (layout storage I).width - 1 ∧
    0 < dest.2.val ∧ dest.2.val < (layout storage I).height - 1 at hdb
  have hsint : ¬ Boundary source := by simp only [Boundary]; omega
  obtain ⟨support, hsupport⟩ := adjacent_exists_of_interior source hsint d.opposite
  have hfirst : Adjacent d support source := by
    simpa only [Direction.opposite_opposite] using hsupport.reverse
  have hsourcefree : source ∉ S.stationary storage :=
    S.wire_interval_clear storage hei j hregister source dest stop source hsource hdest hstop rfl
      le_rfl hg.2.1.le
  have hsupportfree := S.wire_support_clear storage hei j source dest stop support hsource hdest hstop hsupport
  have hstopmem : stop ∈ S.stationary storage := by
    apply ((layout storage I).mem_raster _ _).mpr
    apply Finset.mem_union_left
    rw [hstop]
    exact wireStopRaw_mem storage I hei j
  have hsourcecol : source.1.val ∈ (layout storage I).columns :=
    wirePosition_columns (layout storage I) i e hi j.castSucc
  have hdestcol : dest.1.val ∈ (layout storage I).columns :=
    wirePosition_columns (layout storage I) i e hi j.succ
  have hr := S.slide_signal storage d source dest stop support (hsignal.trans hsource.symm)
    hsourcecol hdestcol hsb.2.2.1 hdb.2.2.1 hsourcefree hsupportfree hfirst hg.1 hg.2.1
    (fun p hl hlo hhi => S.wire_interval_clear storage hei j hregister source dest stop p
      hsource hdest hstop hl hlo.le hhi) hg.2.2 hstopmem
  simpa only [hdest] using hr

/-- Traverse the complete original wire, preserving every stored door value. -/
private theorem forward_wire_indexed (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx)
    (hsignal : S.signal = ((layout storage I).rackX - 1, e.source + (layout storage I).shift))
    (hregister : ((layout storage I).rackX - 1, e.target + (layout storage I).shift) ∉
      S.registerPoints storage) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := ((layout storage I).rackX - 1,
        e.target + (layout storage I).shift)} : Stock I).canonical storage) := by
  let stockAt (j : Fin 8) : Stock I := {S with signal := wirePositionRaw (layout storage I) i e j}
  have hr : ∀ j, Finite.Reachable 1 ((stockAt 0).canonical storage) ((stockAt j).canonical storage) := by
    intro j
    induction j using Fin.induction with
    | zero => exact .refl
    | succ j ih =>
      have hstep := forward_wire_leg storage (stockAt j.castSucc) hei j rfl hregister
      exact ih.trans hstep
  have hzero : stockAt 0 = S := by
    cases S
    simp_all [stockAt, wirePositionRaw, Layout.wirePath]
  have hlast : stockAt (Fin.last 7) =
      ({S with signal := ((layout storage I).rackX - 1,
        e.target + (layout storage I).shift)} : Stock I) := rfl
  simpa only [hzero, hlast] using hr (Fin.last 7)

/-- Any listed wire is a genuine physical macro between its source and target ports. -/
theorem forward_wire (storage : Bool) (S : Stock I) (e : Wire)
    (he : e ∈ (layout storage I).wires)
    (hsignal : S.signal = ((layout storage I).rackX - 1, e.source + (layout storage I).shift))
    (hregister : ((layout storage I).rackX - 1, e.target + (layout storage I).shift) ∉
      S.registerPoints storage) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := ((layout storage I).rackX - 1,
        e.target + (layout storage I).shift)} : Stock I).canonical storage) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
  have hzip : (e, i) ∈ ((layout storage I).wires).zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simp [hi, heq]
  exact S.forward_wire_indexed storage hzip hsignal hregister

end PushPuzzle.PushPush.Doors.Source.Stock
