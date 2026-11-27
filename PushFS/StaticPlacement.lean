/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Placement
public import PushFS.DisplacementCheck

/-!
# Reflecting ambient box displacements into a translated wall stencil

A source cell with a one-cell interior collar has local preimages of every
ambient adjacent destination and support. Matching walls therefore reflects
every actual static displacement into the finite source board.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h W H : ℕ}

/-- The complete four-neighbor stencil lies inside the source rectangle. -/
def Interior (p : Cell w h) : Prop :=
  0 < p.1.val ∧ p.1.val + 1 < w ∧ 0 < p.2.val ∧ p.2.val + 1 < h

instance (p : Cell w h) : Decidable (Interior p) := by unfold Interior; infer_instance

theorem Interior.neighbor_exists {p : Cell w h} (hp : Interior p) (d : Direction) :
    ∃ q : Cell w h, Adjacent d p q := by
  rcases hp with ⟨hx₀, hx₁, hy₀, hy₁⟩
  cases d with
  | north =>
    refine ⟨(p.1, ⟨p.2.val - 1, by omega⟩), ?_⟩
    simp only [Adjacent, true_and]
    omega
  | east => exact ⟨(⟨p.1.val + 1, hx₁⟩, p.2), rfl, rfl⟩
  | south => exact ⟨(p.1, ⟨p.2.val + 1, hy₁⟩), rfl, rfl⟩
  | west =>
    refine ⟨(⟨p.1.val - 1, by omega⟩, p.2), ?_⟩
    simp only [Adjacent, and_true]
    omega

namespace GridEmbedding

/-- Every ambient neighbor of a translated interior cell has its unique local preimage. -/
private theorem translate_neighbor_preimage (dx dy : ℕ) (hx : dx + w ≤ W) (hy : dy + h ≤ H)
    {p : Cell w h} (hp : Interior p) {d : Direction} {q : Cell W H}
    (hq : Adjacent d ((translate dx dy hx hy).cells p) q) :
    ∃ p' : Cell w h, Adjacent d p p' ∧ (translate dx dy hx hy).cells p' = q := by
  obtain ⟨p', hp'⟩ := hp.neighbor_exists d
  have ha : Adjacent d ((translate dx dy hx hy).cells p) ((translate dx dy hx hy).cells p') :=
    (translate dx dy hx hy).adjacent d p p' hp'
  exact ⟨p', hp', ha.functional hq⟩

/-- Both the destination and the rear support reflect into the local wall stencil. -/
theorem displacement_preimage (dx dy : ℕ) (hx : dx + w ≤ W) (hy : dy + h ≤ H)
    {sourceBoard : Board w h} {ambient : Board W H}
    (hw : (translate dx dy hx hy).WallsAgree sourceBoard ambient)
    {p : Cell w h} (hp : Interior p) {q : Cell W H}
    (hd : Displacement ambient ((translate dx dy hx hy).cells p) q) :
    ∃ q' : Cell w h, (translate dx dy hx hy).cells q' = q ∧ Displacement sourceBoard p q' := by
  obtain ⟨hpw, d, rear, hr, hq, hrw, hqw⟩ := hd
  obtain ⟨rear', hrear, heRear⟩ := translate_neighbor_preimage dx dy hx hy hp hr.reverse
  obtain ⟨q', hq', heq⟩ := translate_neighbor_preimage dx dy hx hy hp hq
  refine ⟨q', heq, fun h => hpw ((hw p).mpr h), d, rear', ?_, hq', ?_, ?_⟩
  · simpa only [Direction.opposite_opposite] using hrear.reverse
  · intro h
    exact hrw (heRear ▸ (hw rear').mpr h)
  · intro h
    exact hqw (heq ▸ (hw q').mpr h)

end GridEmbedding
end PushPuzzle.PushFS
