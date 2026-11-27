/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlGoalEmpty
public import PushPush.Doors.ProtectedFrame

/-! Normalized physical shadows and classification of the first moving actor. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

namespace SignalPosition

/-- Working rows and genuine private corners; endpoint names are normalized by wire epsilon steps. -/
def Regular {storage : Bool} {I : Instance} : SignalPosition storage I → Prop
  | .working _ => True
  | .wire _ corner => 0 < corner.val ∧ corner.val < 7

end SignalPosition

namespace Control

variable {storage : Bool} {I : Instance}

/-- One or more control microsteps realize the same actual target box set. -/
def PhysicalNext (current : Control storage I)
    (target : PushFS.State (layout storage I).width (layout storage I).height) : Prop :=
  ∃ next, Control.Reachable current next ∧ next.signal.Regular ∧ next.stock.Realizes storage target

theorem PhysicalNext.refl (current : Control storage I)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hregular : current.signal.Regular) (hs : current.stock.Realizes storage s) :
    current.PhysicalNext s := ⟨current, .refl, hregular, hs⟩

theorem PhysicalNext.same_boxes {current : Control storage I}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hr : current.PhysicalNext s) (hb : t.boxes = s.boxes) : current.PhysicalNext t := by
  obtain ⟨next, hnext, hregular, hs⟩ := hr
  exact ⟨next, hnext, hregular, hb.trans hs⟩

theorem PhysicalNext.prefix {initial current : Control storage I}
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hprefix : Control.Reachable initial current) (hnext : current.PhysicalNext s) :
    initial.PhysicalNext s := by
  obtain ⟨next, hreach, hregular, hs⟩ := hnext
  exact ⟨next, hprefix.trans hreach, hregular, hs⟩

theorem initial_physical (storage : Bool) (I : Instance) :
    (Control.initial storage I).PhysicalNext (puzzle storage I).initial := by
  refine PhysicalNext.refl _ trivial ?_
  change (puzzle storage I).initial.boxes = (Stock.initial storage I).boxes storage
  exact (congrArg PushFS.State.boxes (Stock.initial_canonical storage I)).symm

end Control

/-- The first moved box is a private pin, a uniquely identified door register, or the signal. -/
theorem Stock.first_actor {storage : Bool} {I : Instance} (S : Stock I)
    {s t : PushFS.State (layout storage I).width (layout storage I).height} {d : Direction} {n k : ℕ}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : S.Realizes storage s)
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) :
    ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈ (layout storage I).pins ∨
      (∃ door : Fin I.doors.length, r.cell ⟨1, by omega⟩ = S.doorPoint storage door) ∨
      ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal := by
  have hfirst : r.cell ⟨1, by omega⟩ ∈ s.boxes := r.occupied ⟨0, hn⟩
  have hbefore : r.cell ⟨1, by omega⟩ ∈ r.before :=
    Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hraw := ((layout storage I).mem_raster _ _).mp (hstock ▸ hfirst)
  have hframe := hs.slide_avoids_frame ht r hn hk hv hb
  rcases Finset.mem_union.mp hraw with hraw | hraw
  · rcases Finset.mem_union.mp hraw with hraw | hraw
    · rcases Finset.mem_union.mp hraw with hraw | hraw
      · rcases Finset.mem_union.mp hraw with hpin | hrack
        · exact Or.inl hpin
        · apply False.elim
          apply Finset.disjoint_left.mp hframe _ hbefore
          apply ((layout storage I).mem_raster _ _).mpr
          exact Finset.mem_union_left _ hrack
      · apply False.elim
        apply Finset.disjoint_left.mp hframe _ hbefore
        apply ((layout storage I).mem_raster _ _).mpr
        exact Finset.mem_union_right _ hraw
    · obtain ⟨door, _, he⟩ := Finset.mem_image.mp hraw
      apply Or.inr
      apply Or.inl
      refine ⟨door, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact (congrArg Prod.fst he).symm
      · exact (congrArg Prod.snd he).symm
  · exact Or.inr (Or.inr (Finset.mem_singleton.mp hraw))

end PushPuzzle.PushPush.Doors.Source
