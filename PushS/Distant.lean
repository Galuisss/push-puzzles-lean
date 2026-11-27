/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Boundary
public import PushS.Radius
public import PushS.Blocked

/-! Distant holes and occupied crossings on trajectories ending with an empty frame. -/

@[expose] public section
namespace PushPuzzle.PushS.Distant

open PushFS Boundary

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {s u t : State w h}

private theorem frame_holes (hs : Disjoint s.boxes frame) : frame ⊆ holes s := by
  intro p hp
  exact (mem_holes _).mpr (fun hb => Finset.disjoint_left.mp hs hb hp)

/-- An empty final frame supplies the permanent region throughout the original play. -/
private theorem frame_preserving (hr : Reachable B cap s t) (ht : Disjoint t.boxes frame) :
    Relation.ReflTransGen (Radius.PreservingStep B cap frame) s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih =>
    have hs := reachable_frame_empty (Relation.ReflTransGen.single hm) ht
    exact (ih hs).tail ⟨hm, frame_holes ht⟩

/-- Every player position is within the full interior-hole budget of the outer frame. -/
private theorem player_distance (hr : Reachable B cap s t) (hp : s.player ∈ frame)
    (ht : Disjoint t.boxes frame) :
    ∃ a ∈ frame, distance a t.player ≤ (holes s \ frame).card :=
  Radius.reachable_distance (frame_preserving hr ht)
    (frame_holes (reachable_frame_empty hr ht)) hp

/-- The distance test used for remote holes and solid internal crossings. -/
def Far (s : State w h) (g : Cell w h) : Prop :=
  ∀ a ∈ frame, (holes s \ frame).card < distance a g

/-- A cell is beyond the interior-hole budget from the whole frame exactly when its four
coordinate margins exceed that budget. -/
theorem far_iff_margins (s : State w h) (g : Cell w h) :
    Far s g ↔ (holes s \ frame).card < g.1.val ∧
      (holes s \ frame).card + g.1.val + 1 < w ∧
      (holes s \ frame).card < g.2.val ∧
      (holes s \ frame).card + g.2.val + 1 < h := by
  have hw := g.1.isLt
  have hh := g.2.isLt
  constructor
  · intro hg
    have hl := hg (⟨0, by omega⟩, g.2)
      ((mem_frame _).mpr ⟨.west, by simp [edge]⟩)
    have hr := hg (⟨w - 1, by omega⟩, g.2)
      ((mem_frame _).mpr ⟨.east, by
        simp only [edge, Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩)
    have ht := hg (g.1, ⟨0, by omega⟩)
      ((mem_frame _).mpr ⟨.north, by simp [edge]⟩)
    have hb := hg (g.1, ⟨h - 1, by omega⟩)
      ((mem_frame _).mpr ⟨.south, by
        simp only [edge, Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩)
    simp only [distance, Nat.dist] at hl hr ht hb
    omega
  · rintro ⟨hl, hr, ht, hb⟩ a ha
    obtain ⟨d, hd⟩ := (mem_frame a).mp ha
    cases d <;>
      simp only [edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;>
      simp only [distance, Nat.dist] <;> omega

theorem player_ne (hr : Reachable B cap s t) (hp : s.player ∈ frame)
    (ht : Disjoint t.boxes frame) {g : Cell w h} (hg : Far s g) : t.player ≠ g := by
  obtain ⟨a, ha, hd⟩ := player_distance hr hp ht
  intro he
  rw [he] at hd
  have := hg a ha
  omega

/-- A required distant final hole remains empty at every intermediate state. -/
private theorem hole_at (hsu : Reachable B cap s u) (hut : Reachable B cap u t)
    (hp : s.player ∈ frame) (ht : Disjoint t.boxes frame)
    {g : Cell w h} (hg : Far s g) (hgt : g ∈ holes t) : g ∈ holes u :=
  Radius.distant_hole_at (frame_preserving hsu (reachable_frame_empty hut ht))
    (frame_preserving hut ht) (frame_holes (reachable_frame_empty (hsu.trans hut) ht))
    hp hg hgt

/-- A distant initially occupied crossing stays occupied throughout the play. -/
theorem box_at (hsu : Reachable B cap s u) (hut : Reachable B cap u t)
    (hp : s.player ∈ frame) (ht : Disjoint t.boxes frame)
    {g : Cell w h} (hg : Far s g) (hgs : g ∈ s.boxes) : g ∈ u.boxes := by
  by_contra hgu
  have hs := Radius.distant_hole_source
    (frame_preserving hsu (reachable_frame_empty hut ht))
    (frame_holes (reachable_frame_empty (hsu.trans hut) ht)) hp hg ((mem_holes _).mpr hgu)
  exact (mem_holes _).mp hs hgs

/-- A set of distant final holes is excluded at every state of the successful play. -/
theorem excluded_at (hsu : Reachable B cap s u) (hut : Reachable B cap u t)
    (hp : s.player ∈ frame) (ht : Disjoint t.boxes frame)
    {G : Finset (Cell w h)} (hfar : ∀ g ∈ G, Far s g) (hend : G ⊆ holes t) :
    Blocked.Excluded G u where
  empty _ hg := hole_at hsu hut hp ht (hfar _ hg) (hend hg)
  player hg := player_ne hsu hp (reachable_frame_empty hut ht) (hfar _ hg) rfl

end PushPuzzle.PushS.Distant
