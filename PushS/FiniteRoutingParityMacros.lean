/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingParityInventory

/-! Complete parity execution on the actual buffered route inventory. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Tool.Parity

open PushFS FiniteTools


theorem floor (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (p : Cell (side w) (side w)) (hp : p ∈ parityActive w) :
    (place w before after n m above).cells p ∈ active w (before++ .line n:: .parity:: .line m::after) above := by
  exact parity_floor w hw before after n m hn hm above p hp

theorem frame (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    FiniteWireFrame.Frame (parityActive w) (place w before after n m above)
      (macroBoard w (before++ .line n:: .parity:: .line m::after) above)
      (fixed w hw before after n m (by unfold buffer at hn; omega) (by unfold buffer at hm; omega)) := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hspan := paritySpan_bounds w
  refine ⟨fun p hp => (FiniteWireFrame.floor_iff _ _ _).mpr (floor w hw before after n m hn hm above p hp), ?_, ?_⟩
  · intro p hp hmem
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hmem
    have hl' := (Finset.mem_filter.mp hl).2
    have hout : l.val < ownedCount w before+n-1 ∨ ownedCount w before+n+2 < l.val := by
      by_contra hh
      exact hl' (label_complete w before after n m hn' hm' l (by omega) (by omega))
    have hpa := (Finset.mem_filter.mp hp).2
    have hxe := congrArg (fun p : Cell (width w (before++ .line n:: .parity:: .line m::after)) (height w) => p.1.val) he
    have hlx := (cutCell_coordinates w hw (cut w before n false) _ l).1
    rcases hout with hout | hout
    · have hg := cutPosition_gap w hw (cut w before n false) _ l
        (label w before after n m hn' hm' .predecessor) (by rw [label_val]; exact hout)
      have hpx := (cutCell_coordinates w hw (cut w before n false) _
        (label w before after n m hn' hm' .predecessor)).1
      have hs := congrArg (fun p : Cell (width w (before++ .line n:: .parity:: .line m::after)) (height w) => p.1.val)
        (slot w hw before after n m hn' hm' above false .predecessor)
      dsimp [place, parityPlace, embedding, parityCell, parityPoint] at hxe hs
      unfold radius at *
      omega
    · have hg := cutPosition_gap w hw (cut w before n false) _
        (label w before after n m hn' hm' .successor) l (by rw [label_val]; dsimp [index]; omega)
      have hpx := (cutCell_coordinates w hw (cut w before n false) _
        (label w before after n m hn' hm' .successor)).1
      have hs := congrArg (fun p : Cell (width w (before++ .line n:: .parity:: .line m::after)) (height w) => p.1.val)
        (slot w hw before after n m hn' hm' above false .successor)
      dsimp [place, parityPlace, embedding, parityCell, parityPoint] at hxe hs
      unfold radius at *
      omega
  · apply Finset.disjoint_left.mpr
    intro p hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    exact (FiniteWireFrame.floor_iff _ _ _).mpr (cutCell_active w hw (cut w before n false) _ above l)

theorem low_to_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard w (before++ .line n:: .parity:: .line m::after) above) (some 1)
      ⟨(place w before after n m above).cells (parityRoute w 0),
        cutBoxes w hw (cut w before n false) (before++ .line n:: .parity:: .line m::after)⟩
      ⟨(place w before after n m above).cells (parityRoute w 5),
        cutBoxes w hw (cut w before n true) (before++ .line n:: .parity:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hh := parity_forward_active_placed w (place w before after n m above) (frame w hw before after n m hn hm above)
  change Reachable _ _ ⟨_, _⟩ ⟨_, _⟩ at hh
  rw [← inventory w hw before after n m hn' hm' above false,
    ← inventory w hw before after n m hn' hm' above true] at hh
  exact hh

theorem high_to_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard w (before++ .line n:: .parity:: .line m::after) above) (some 1)
      ⟨(place w before after n m above).cells (parityBackwardRoute w 0),
        cutBoxes w hw (cut w before n true) (before++ .line n:: .parity:: .line m::after)⟩
      ⟨(place w before after n m above).cells (parityBackwardRoute w 5),
        cutBoxes w hw (cut w before n false) (before++ .line n:: .parity:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hh := parity_backward_active_placed w (place w before after n m above) (frame w hw before after n m hn hm above)
  change Reachable _ _ ⟨_, _⟩ ⟨_, _⟩ at hh
  rw [← inventory w hw before after n m hn' hm' above true,
    ← inventory w hw before after n m hn' hm' above false] at hh
  exact hh

end PushPuzzle.PushS.FiniteRouting.Line.Tool.Parity
