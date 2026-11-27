/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalFaultRegister

/-! Assemble complete dead stocks from pin, register and active-actor exclusions. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell State Direction)

namespace Wire

/-- The closed-cluster obstruction only needs closure along the current pushing direction. -/
theorem slide_avoids_closed_line {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (cluster : Finset (Cell w h)) (hsub : cluster ⊆ s.boxes)
    (hconvex : LineConvex cluster)
    (hclosed : ∀ p ∈ cluster, ∀ q ∈ s.boxes, d.lane q = d.lane p → q ∈ cluster) :
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
    hclosed _ hp stop hstop (hstoplane.trans (r.lane _).symm)
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

end Wire

namespace Source.WireFault

variable {storage : Bool} {I : Instance} {S : Stock I}

/-- No positive protected successor can start from an actor satisfying this predicate. -/
def BlocksFirst (F : WireFault storage I S)
    (actor : Cell (layout storage I).width (layout storage I).height → Prop) : Prop :=
  ∀ (d : Direction) (s : PushFS.State (layout storage I).width (layout storage I).height)
    (n k : ℕ) (r : Slide d s n k) (hn : 0 < n), 0 < k → s.boxes = F.boxes →
      s.player ∉ s.boxes →
      Protected storage I ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ →
      actor (r.cell ⟨1, by omega⟩) → False

/-- The protected frame handles all remaining inventory once the three movable actor classes are excluded. -/
theorem deadStock_of_actors (F : WireFault storage I S)
    (hprotected : Protected storage I ⟨(layout storage I).corner, F.boxes⟩)
    (hpin : F.BlocksFirst fun p => (p.1.val, p.2.val) ∈ (layout storage I).pins)
    (hregister : F.BlocksFirst fun p => ∃ door : Fin I.doors.length, p = S.doorPoint storage door)
    (hactive : F.BlocksFirst fun p => p = F.signal ∨ p ∈ F.added) :
    Wire.DeadStock F.boxes (Protected storage I) := by
  intro d s n k r hn hk hb hv ht
  have hs : Protected storage I s := hprotected.of_boxes_eq hb
  have hframe := hs.slide_avoids_frame ht r hn hk hv rfl
  have hfirstb : r.cell ⟨1, by omega⟩ ∈ r.before :=
    Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hfirst : r.cell ⟨1, by omega⟩ ∈ F.boxes := hb ▸ r.occupied ⟨0, hn⟩
  rcases Finset.mem_union.mp hfirst with hrest | hadded
  · have hstock := (Finset.mem_sdiff.mp hrest).1
    have hraw := ((layout storage I).mem_raster _ _).mp hstock
    rcases Finset.mem_union.mp hraw with hraw | hraw
    · rcases Finset.mem_union.mp hraw with hraw | hraw
      · rcases Finset.mem_union.mp hraw with hraw | hraw
        · rcases Finset.mem_union.mp hraw with hpinraw | hrack
          · exact hpin d s n k r hn hk hb hv ht hpinraw
          · apply Finset.disjoint_left.mp hframe _ hfirstb
            exact ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_left _ hrack)
        · apply Finset.disjoint_left.mp hframe _ hfirstb
          exact ((layout storage I).mem_raster _ _).mpr (Finset.mem_union_right _ hraw)
      · obtain ⟨door, _, he⟩ := Finset.mem_image.mp hraw
        apply hregister d s n k r hn hk hb hv ht
        refine ⟨door, ?_⟩
        apply Prod.ext <;> apply Fin.ext
        · exact (congrArg Prod.fst he).symm
        · exact (congrArg Prod.snd he).symm
    · have he := Finset.mem_singleton.mp hraw
      have heq : r.cell ⟨1, by omega⟩ = F.signal :=
        Prod.ext (Fin.ext (congrArg Prod.fst (he.trans F.signal_raw.symm)))
          (Fin.ext (congrArg Prod.snd (he.trans F.signal_raw.symm)))
      exact hactive d s n k r hn hk hb hv ht (Or.inl heq)
  · exact hactive d s n k r hn hk hb hv ht (Or.inr hadded)

end Source.WireFault
end PushPuzzle.PushPush.Doors
