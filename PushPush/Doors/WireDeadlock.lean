/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Boundary
public import PushPush.Doors.RoomSlide

/-! Closed line-convex box clusters cannot move along an interior trajectory. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Wire

open PushFS (Cell State Direction)

variable {w h : ℕ} {s t : State w h} {d : Direction} {n k : ℕ}

/-- Each occupied row and column of the cluster is a single consecutive interval. -/
def LineConvex (cluster : Finset (Cell w h)) : Prop :=
  ∀ (d : Direction), ∀ p ∈ cluster, ∀ q ∈ cluster,
    d.lane q = d.lane p → ∀ z : Cell w h, d.lane z = d.lane p →
      d.position p ≤ d.position z → d.position z ≤ d.position q → z ∈ cluster

/-- Other inventory avoids every row and column used by the cluster. -/
def LineClosed (cluster boxes : Finset (Cell w h)) : Prop :=
  ∀ (d : Direction), ∀ p ∈ cluster, ∀ q ∈ boxes, d.lane q = d.lane p → q ∈ cluster

/-- A cluster with at most two adjacent cells in each lane is line convex. -/
theorem lineConvex_of_short_lines (cluster : Finset (Cell w h))
    (hshort : ∀ (d : Direction), ∀ p ∈ cluster, ∀ q ∈ cluster,
      d.lane q = d.lane p → d.position q ≤ d.position p + 1) : LineConvex cluster := by
  intro d p hp q hq hl z hzl hlo hhi
  have hbound := hshort d p hp q hq hl
  have hcases : d.position z = d.position p ∨ d.position z = d.position q := by omega
  rcases hcases with hz | hz
  · exact d.cell_ext hzl hz ▸ hp
  · exact d.cell_ext (hzl.trans hl.symm) hz ▸ hq

/-- Two adjacent boxes form a convex cluster in every direction. -/
theorem pair_lineConvex {a b : Cell w h} {e : Direction} (ha : PushFS.Adjacent e a b) :
    LineConvex ({a, b} : Finset (Cell w h)) := by
  apply lineConvex_of_short_lines
  intro d p hp q hq hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    cases e <;> cases d <;>
    simp_all [PushFS.Adjacent, Direction.position, Direction.lane] <;> omega

/-- A three-box right-angle cluster has no separated pair on any occupied line. -/
theorem elbow_lineConvex {a b c : Cell w h} {e f : Direction}
    (ha : PushFS.Adjacent e a b) (hb : PushFS.Adjacent f a c)
    (hperp : e.lane c ≠ e.lane a) : LineConvex ({a, b, c} : Finset (Cell w h)) := by
  apply lineConvex_of_short_lines
  intro d p hp q hq hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    cases e <;> cases f <;> cases d <;>
    simp_all [PushFS.Adjacent, Direction.position, Direction.lane] <;> omega

/-- A positive interior slide cannot take any box from a closed convex cluster. -/
theorem slide_avoids_cluster (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (cluster : Finset (Cell w h)) (hsub : cluster ⊆ s.boxes)
    (hconvex : LineConvex cluster) (hclosed : LineClosed cluster s.boxes) :
    Disjoint cluster r.before := by
  apply Finset.disjoint_left.mpr
  intro p hp hbefore
  obtain ⟨i, _, he⟩ := Finset.mem_image.mp hbefore
  subst p
  obtain ⟨stop, hstop, ha⟩ := r.exists_stopper hn hinterior
  have hstoplane : d.lane stop = d.lane s.player := ha.lane.trans (r.lane _)
  have hstopp := ha.position
  have hlastp := r.position ⟨n + k, by omega⟩
  have hip := r.position ⟨i.val + 1, by omega⟩
  have higap := r.position ⟨n + 1, by omega⟩
  have hstopmem : stop ∈ cluster :=
    hclosed d _ hp stop hstop (hstoplane.trans (r.lane _).symm)
  have hgapmem : r.cell ⟨n + 1, by omega⟩ ∈ cluster := by
    apply hconvex d _ hp stop hstopmem (hstoplane.trans (r.lane _).symm) _
      ((r.lane _).trans (r.lane _).symm)
    · change d.position (r.cell ⟨i.val + 1, by omega⟩) =
        d.position s.player + (i.val + 1 : ℕ) at hip
      change d.position (r.cell ⟨n + 1, by omega⟩) =
        d.position s.player + (n + 1 : ℕ) at higap
      have := i.isLt
      omega
    · change d.position (r.cell ⟨n + k, by omega⟩) =
        d.position s.player + (n + k : ℕ) at hlastp
      change d.position (r.cell ⟨n + 1, by omega⟩) =
        d.position s.player + (n + 1 : ℕ) at higap
      omega
  exact r.clear ⟨0, hk⟩ (hsub hgapmem)

/-- A stock has no positive slide whose destination obeys the protected-prefix predicate. -/
def DeadStock (boxes : Finset (Cell w h)) (allowed : State w h → Prop) : Prop :=
  ∀ (d : Direction) (s : State w h) (n k : ℕ) (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k),
    s.boxes = boxes → s.player ∉ s.boxes →
      allowed ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ → False

/-- After a certified dead stock, all remaining successful-prefix actions are walks. -/
theorem DeadStock.reachable_boxes {boxes : Finset (Cell w h)} {allowed : State w h → Prop}
    (hd : DeadStock boxes allowed) (hs : s.boxes = boxes) (hr : Reachable s t)
    (hp : ∀ u, Reachable s u → Reachable u t → allowed u) : t.boxes = boxes := by
  have hi : ∀ u, Reachable s u → Reachable u t → u.boxes = boxes := by
    intro u hu
    induction hu with
    | refl => exact fun _ => hs
    | @tail u v hu hstep ih =>
      intro hv
      have hu' := ih ((Relation.ReflTransGen.single hstep).trans hv)
      obtain ⟨d, hm⟩ := hstep
      cases hm with
      | walk _ _ _ hb => exact hb.trans hu'
      | push hvalid hn hk r hplayer hboxes =>
        have hstate : v = ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ := State.ext hplayer hboxes
        have hprotected := hp v (hu.tail ⟨d, Move.push hvalid hn hk r hplayer hboxes⟩) hv
        rw [hstate] at hprotected
        exact False.elim (hd d u _ _ r hn hk hu' hvalid hprotected)
  exact hi t hr .refl

end PushPuzzle.PushPush.Doors.Wire
