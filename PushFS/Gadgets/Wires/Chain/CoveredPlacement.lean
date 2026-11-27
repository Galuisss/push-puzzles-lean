/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Placement
public import PushFS.Gadgets.Gates.Framing

/-!
# Placing macros with actual overlapping collar boxes

Every ambient box inside the represented rectangle is explicitly present in
both local endpoint states. Place only the boxes outside the rectangle, then
restore the identical endpoint unions. One physical collar box is represented
once in the final global state.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h W H : ℕ}

/-- Receiver-oriented notation for the existing exact grid-state extension. -/
abbrev State.place (s : State w h) (e : GridEmbedding w h W H) (outside : Finset (Cell W H)) :
    State W H := e.extend outside s

namespace GridEmbedding

/-- Keep precisely the ambient boxes outside the represented rectangle. -/
def outsideImage (e : GridEmbedding w h W H) (external : Finset (Cell W H)) : Finset (Cell W H) :=
  external \ Finset.univ.map e.cells

private theorem outsideImage_excludes (e : GridEmbedding w h W H) (external : Finset (Cell W H))
    (p : Cell w h) : e.cells p ∉ e.outsideImage external := by simp [outsideImage]

private theorem extend_outsideImage (e : GridEmbedding w h W H) (s : State w h)
    (external : Finset (Cell W H)) (hcovered : ∀ p, e.cells p ∈ external → p ∈ s.boxes) :
    e.extend (e.outsideImage external) s = e.extend external s := by
  refine State.ext rfl ?_
  ext q
  simp only [extend, Finset.mem_union, outsideImage, Finset.mem_sdiff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hq : q ∈ Finset.univ.map e.cells
      · obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hq
        exact Or.inl (Finset.mem_map.mpr ⟨p, hcovered p h, rfl⟩)
      · exact Or.inr ⟨h, hq⟩

/-- Exact local replay with every overlapping ambient box already represented at both endpoints. -/
theorem reachable_covered (e : GridEmbedding w h W H) {sourceBoard : Board w h} {ambient : Board W H}
    {external : Finset (Cell W H)} {s t : State w h}
    (hw : e.WallsAgree sourceBoard ambient)
    (hs : ∀ p, e.cells p ∈ external → p ∈ s.boxes)
    (ht : ∀ p, e.cells p ∈ external → p ∈ t.boxes)
    (he : Disjoint external ambient.walls) (hr : Reachable sourceBoard (some 1) s t) :
    Reachable ambient (some 1) (e.extend external s) (e.extend external t) := by
  have he' : Disjoint (e.outsideImage external) ambient.walls := he.mono_left Finset.sdiff_subset
  have hh := reachable_one hw (e.outsideImage_excludes external) he' hr
  rw [e.extend_outsideImage s external hs, e.extend_outsideImage t external ht] at hh
  exact hh

private theorem extend_withFixed (e : GridEmbedding w h W H) (s : State w h)
    (fixed : Finset (Cell w h)) (external : Finset (Cell W H))
    (hf : ∀ p ∈ fixed, e.cells p ∈ external) :
    e.extend external (Gadgets.Gates.withFixed fixed s) = e.extend external s := by
  refine State.ext rfl ?_
  change (s.boxes ∪ fixed).map e.cells ∪ external = s.boxes.map e.cells ∪ external
  rw [Finset.map_union, Finset.union_assoc]
  congr 1
  apply Finset.union_eq_right.mpr
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
  exact hf p hp

/-- Hold all overlapping collar neighbors fixed inside the local proof, preserving global ownership. -/
theorem reachable_withFixed (e : GridEmbedding w h W H)
    {sourceBoard : Board w h} {ambient : Board W H}
    {external : Finset (Cell W H)} {fixed : Finset (Cell w h)} {s t : State w h}
    (hw : e.WallsAgree sourceBoard ambient)
    (hinside : ∀ p, e.cells p ∈ external → p ∈ fixed)
    (hfixed : ∀ p ∈ fixed, e.cells p ∈ external)
    (he : Disjoint external ambient.walls)
    (hr : Reachable sourceBoard (some 1) (Gadgets.Gates.withFixed fixed s)
      (Gadgets.Gates.withFixed fixed t)) :
    Reachable ambient (some 1) (e.extend external s) (e.extend external t) := by
  have hh := e.reachable_covered hw
    (fun p hp => Finset.mem_union_right _ (hinside p hp))
    (fun p hp => Finset.mem_union_right _ (hinside p hp)) he hr
  simpa only [e.extend_withFixed _ fixed external hfixed] using hh

end GridEmbedding
end PushPuzzle.PushFS
