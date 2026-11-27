/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Single

/-! Physical single-box identity updates and order on a straight row. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets


variable {w h : ℕ}

/-- Follow the unique pushed box, leaving every other physical box fixed. -/
def shiftBox (src dst : Cell w h) (p : Cell w h) : Cell w h :=
  if p = src then dst else p

@[simp] theorem shiftBox_source (src dst : Cell w h) : shiftBox src dst src = dst := by
  simp [shiftBox]

@[simp] theorem shiftBox_other {src dst p : Cell w h} (hp : p ≠ src) :
    shiftBox src dst p = p := by simp [shiftBox, hp]

/-- The fresh destination prevents two physical boxes from merging. -/
theorem shiftBox_injOn {boxes : Finset (Cell w h)} {src dst : Cell w h}
    (hdst : dst ∉ boxes) : Set.InjOn (shiftBox src dst) (boxes : Set (Cell w h)) := by
  intro p hp q hq heq
  by_cases hp' : p = src <;> by_cases hq' : q = src
  · exact hp'.trans hq'.symm
  · subst p
    simp only [shiftBox_source, shiftBox_other hq'] at heq
    exact False.elim (hdst (heq ▸ hq))
  · subst q
    simp only [shiftBox_other hp', shiftBox_source] at heq
    exact False.elim (hdst (heq ▸ hp))
  · simpa only [shiftBox_other hp', shiftBox_other hq'] using heq

/-- Following the actual pushed box gives exactly the new unlabelled box set. -/
theorem image_shiftBox {boxes : Finset (Cell w h)} {src dst : Cell w h}
    (hsrc : src ∈ boxes) : boxes.image (shiftBox src dst) = insert dst (boxes.erase src) := by
  ext q
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_cases he : p = src
    · exact Or.inl (by simp [shiftBox, he])
    · exact Or.inr (by simpa [shiftBox, he] using And.intro he hp)
  · rintro (rfl | ⟨hne, hmem⟩)
    · exact ⟨src, hsrc, shiftBox_source _ _⟩
    · exact ⟨q, hmem, shiftBox_other hne⟩

end PushPuzzle.PushFS.Gadgets
