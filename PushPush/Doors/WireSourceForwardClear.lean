/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourceForwardGeometry

/-! Complete physical clearance for every normal wire slide. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem wire_interval_pin_clear (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7)
    (source dest stop p : Cell (layout storage I).width (layout storage I).height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw (layout storage I) i e j.castSucc)
    (hdest : (dest.1.val, dest.2.val) = wirePositionRaw (layout storage I) i e j.succ)
    (hstop : (stop.1.val, stop.2.val) = wireStopRaw (layout storage I) i e j)
    (hlane : (wireDirection (layout storage I) i e j).lane p =
      (wireDirection (layout storage I) i e j).lane source)
    (hupper : (wireDirection (layout storage I) i e j).position p ≤
      (wireDirection (layout storage I) i e j).position dest) :
    (p.1.val, p.2.val) ∉ (layout storage I).pins := by
  have hi := (List.mem_zipIdx' hei).1
  have he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
  have hg := wire_leg_geometry (layout storage I) i e hi (wires_fit storage I he).1
    (wires_fit storage I he).2 j source dest stop hsource hdest hstop
  by_cases hj : j.val < 6
  · have hspins : (stop.1.val, stop.2.val) ∈ (layout storage I).pins := by
      rw [hstop]
      exact wireStopRaw_pin_mem storage I hei j hj
    apply pin_ray_clear storage I _ p stop hspins
    · exact hlane.trans (hg.2.2.lane.trans hg.1).symm
    · have hp := hg.2.2.position
      omega
  · have hy : p.2.val = e.target + (layout storage I).shift := by
      rcases j with ⟨j, hj'⟩
      change ¬ j < 6 at hj
      have heq : j = 6 := by omega
      subst j
      simp [wireDirection, wirePositionRaw, Layout.wirePath, Direction.lane] at hlane hsource
      omega
    intro hp
    exact pins_not_target_row storage I he hp hy

private theorem wire_support_pin_clear (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7)
    (source dest stop support : Cell (layout storage I).width (layout storage I).height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw (layout storage I) i e j.castSucc)
    (hdest : (dest.1.val, dest.2.val) = wirePositionRaw (layout storage I) i e j.succ)
    (hstop : (stop.1.val, stop.2.val) = wireStopRaw (layout storage I) i e j)
    (hsupport : Adjacent (wireDirection (layout storage I) i e j).opposite source support) :
    (support.1.val, support.2.val) ∉ (layout storage I).pins := by
  have hi := (List.mem_zipIdx' hei).1
  have he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
  have hg := wire_leg_geometry (layout storage I) i e hi (wires_fit storage I he).1
    (wires_fit storage I he).2 j source dest stop hsource hdest hstop
  have hfirst : Adjacent (wireDirection (layout storage I) i e j) support source := by
    simpa only [Direction.opposite_opposite] using hsupport.reverse
  apply wire_interval_pin_clear storage I hei j source dest stop support hsource hdest hstop
  · exact hfirst.lane.symm
  · have hp := hfirst.position
    have hforward := hg.2.1
    omega

namespace Stock

variable {I : Instance}

/-- The entire closed signal interval, including both turns, misses the stationary inventory. -/
theorem wire_interval_clear (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7)
    (hregister : ((layout storage I).rackX - 1, e.target + (layout storage I).shift) ∉ S.registerPoints storage)
    (source dest stop p : Cell (layout storage I).width (layout storage I).height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw (layout storage I) i e j.castSucc)
    (hdest : (dest.1.val, dest.2.val) = wirePositionRaw (layout storage I) i e j.succ)
    (hstop : (stop.1.val, stop.2.val) = wireStopRaw (layout storage I) i e j)
    (hlane : (wireDirection (layout storage I) i e j).lane p =
      (wireDirection (layout storage I) i e j).lane source)
    (hlower : (wireDirection (layout storage I) i e j).position source ≤
      (wireDirection (layout storage I) i e j).position p)
    (hupper : (wireDirection (layout storage I) i e j).position p ≤
      (wireDirection (layout storage I) i e j).position dest) : p ∉ S.stationary storage := by
  have hi := (List.mem_zipIdx' hei).1
  have he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
  have hpins := wire_interval_pin_clear storage I hei j source dest stop p hsource hdest hstop hlane hupper
  have hloc := wire_interval_location (layout storage I) i e hi j source dest p hsource hdest hlane hlower hupper
  have hraw : (p.1.val, p.2.val) ∉ (layout storage I).fixed ∪ S.registerPoints storage := by
    rcases hloc with hx | ⟨_, hport⟩ | ⟨_, hport⟩
    · exact S.private_clear storage hx hpins
    · rw [hport]
      exact S.launch_empty storage he
    · rw [hport]
      exact S.target_empty storage he hregister
  exact fun hp => hraw (((layout storage I).mem_raster _ _).mp hp)

/-- The reverse support of each normal wire slide is an actual empty cell. -/
theorem wire_support_clear (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7)
    (source dest stop support : Cell (layout storage I).width (layout storage I).height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw (layout storage I) i e j.castSucc)
    (hdest : (dest.1.val, dest.2.val) = wirePositionRaw (layout storage I) i e j.succ)
    (hstop : (stop.1.val, stop.2.val) = wireStopRaw (layout storage I) i e j)
    (hsupport : Adjacent (wireDirection (layout storage I) i e j).opposite source support) :
    support ∉ insert source (S.stationary storage) := by
  have hi := (List.mem_zipIdx' hei).1
  have he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
  have hpins := wire_support_pin_clear storage I hei j source dest stop support hsource hdest hstop hsupport
  have hloc := wire_support_location (layout storage I) i e hi j source support hsource hsupport
  have hraw : (support.1.val, support.2.val) ∉ (layout storage I).fixed ∪ S.registerPoints storage := by
    rcases hloc with hx | ⟨_, heq⟩
    · exact S.private_clear storage hx hpins
    · rw [heq]
      exact S.launch_support_empty storage he
  simp only [Finset.mem_insert, not_or]
  exact ⟨Ne.symm hsupport.ne, fun hp => hraw (((layout storage I).mem_raster _ _).mp hp)⟩

end Stock
end PushPuzzle.PushPush.Doors.Source
