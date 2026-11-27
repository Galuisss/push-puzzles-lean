/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Placement
public import PushFS.Walking

/-! Replay tool macros using only their explicit active floor and actual stationary inventory. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteWireFrame

open PushFS

variable {w h W H : ℕ}

/-- The temporary proof board exposes precisely the macro's active cells. -/
def board (active goals : Finset (Cell w h)) : Board w h := ⟨Finset.univ \ active, goals⟩

@[simp] theorem floor_iff (active goals : Finset (Cell w h)) (p : Cell w h) :
    p ∉ (board active goals).walls ↔ p ∈ active := by simp [board]

/-- An ambient placement preserves every exposed floor cell and its fixed inventory. -/
structure Frame (active : Finset (Cell w h)) (e : GridEmbedding w h W H)
    (B : Board W H) (fixed : Finset (Cell W H)) : Prop where
  floor : ∀ p ∈ active, e.cells p ∉ B.walls
  fixed_avoids : ∀ p ∈ active, e.cells p ∉ fixed
  fixed_floor : Disjoint fixed B.walls

/-- Relocating one indexed box preserves every other actual inventory cell. -/
theorem image_relocate {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f g : α → β) (hf : Function.Injective f) (a : α)
    (hrest : ∀ i, i ≠ a → g i = f i) :
    insert (g a) ((Finset.univ.image f).erase (f a)) = Finset.univ.image g := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    · obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      have hi : i ≠ a := fun hh => hne (congrArg f hh)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hrest i hi⟩
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases hi : i = a
    · exact Finset.mem_insert.mpr (Or.inl (congrArg g hi))
    · apply Finset.mem_insert_of_mem
      rw [hrest i hi]
      exact Finset.mem_erase.mpr ⟨fun he => hi (hf he),
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- An explicitly indexed single push gives the exact updated unlabelled inventory. -/
theorem push_named {α : Type} [Fintype α] [DecidableEq α] {B : Board w h}
    (f g : α → Cell w h) (hf : Function.Injective f) (a : α)
    (hrest : ∀ i, i ≠ a → g i = f i) {support : Cell w h} {d : Direction}
    (hs : (⟨support, Finset.univ.image f⟩ : State w h).Valid B)
    (hsupport : Adjacent d support (f a)) (hstep : Adjacent d (f a) (g a))
    (hfloor : g a ∉ B.walls) (hempty : g a ∉ Finset.univ.image f) :
    Move B (some 1) d ⟨support, Finset.univ.image f⟩ ⟨f a, Finset.univ.image g⟩ := by
  have hh := SingleMoveView.push hs hsupport
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩) hstep hfloor hempty
  rw [image_relocate f g hf a hrest] at hh
  exact Move.single_iff.mpr hh

/-- Two actual straight walks connect opposite corners of an empty rectangle. -/
theorem walk_rectangle {B : Board w h} {boxes : Finset (Cell w h)}
    (hd : Disjoint boxes B.walls) (a b : Cell w h)
    (hfree : ∀ p : Cell w h,
      min a.1.val b.1.val ≤ p.1.val → p.1.val ≤ max a.1.val b.1.val →
      min a.2.val b.2.val ≤ p.2.val → p.2.val ≤ max a.2.val b.2.val → Free B boxes p) :
    Reachable B (some 1) ⟨a, boxes⟩ ⟨b, boxes⟩ := by
  have h1 : Reachable B (some 1) ⟨a, boxes⟩ ⟨(b.1, a.2), boxes⟩ := by
    apply walk_horizontal hd
    intro x hx hx'
    exact hfree (x, a.2) hx hx' (by dsimp; omega) (by dsimp; omega)
  have h2 : Reachable B (some 1) ⟨(b.1, a.2), boxes⟩ ⟨b, boxes⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    exact hfree (b.1, y) (by dsimp; omega) (by dsimp; omega) hy hy'
  exact h1.trans h2

private theorem valid_extend {e : GridEmbedding w h W H} {A : Board w h} {B : Board W H}
    {fixed : Finset (Cell W H)}
    (hfloor : ∀ p, p ∉ A.walls → e.cells p ∉ B.walls)
    (hfixed : ∀ p, p ∉ A.walls → e.cells p ∉ fixed)
    (hfw : Disjoint fixed B.walls) {s : State w h} (hs : s.Valid A) :
    (e.extend fixed s).Valid B := by
  refine ⟨hfloor _ hs.1, ?_, ?_⟩
  · apply Finset.disjoint_union_left.mpr
    refine ⟨?_, hfw⟩
    apply Finset.disjoint_left.mpr
    intro p hp hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    exact hfloor q (Finset.disjoint_left.mp hs.2.1 hq) hw
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hp
      exact hs.2.2 (e.cells.injective he ▸ hq)
    · exact hfixed _ hs.1 hp

private theorem move_extend {e : GridEmbedding w h W H} {A : Board w h} {B : Board W H}
    {fixed : Finset (Cell W H)}
    (hfloor : ∀ p, p ∉ A.walls → e.cells p ∉ B.walls)
    (hfixed : ∀ p, p ∉ A.walls → e.cells p ∉ fixed)
    (hfw : Disjoint fixed B.walls) {d : Direction} {s t : State w h}
    (hm : Move A (some 1) d s t) :
    Move B (some 1) (e.direction d) (e.extend fixed s) (e.extend fixed t) := by
  obtain ⟨hs, ha, ht, hwalk | hpush⟩ := Move.single_iff.mp hm
  all_goals apply Move.single_iff.mpr
  · obtain ⟨he, hb⟩ := hwalk
    refine ⟨valid_extend hfloor hfixed hfw hs, e.adjacent _ _ _ ha, hfloor _ ht,
      Or.inl ⟨?_, ?_⟩⟩
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨q, hq, hqe⟩ := Finset.mem_map.mp hp
        exact he (e.cells.injective hqe ▸ hq)
      · exact hfixed _ ht hp
    · simp only [GridEmbedding.extend, hb]
  · obtain ⟨hp, q, hq, hqw, hqe, hb⟩ := hpush
    refine ⟨valid_extend hfloor hfixed hfw hs, e.adjacent _ _ _ ha, hfloor _ ht,
      Or.inr ⟨Finset.mem_union_left _ (Finset.mem_map.mpr ⟨t.player, hp, rfl⟩),
        e.cells q, e.adjacent _ _ _ hq, hfloor _ hqw, ?_, ?_⟩⟩
    · intro hm
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨r, hr, hre⟩ := Finset.mem_map.mp hm
        exact hqe (e.cells.injective hre ▸ hr)
      · exact hfixed _ hqw hm
    · change t.boxes.map e.cells ∪ fixed =
        insert (e.cells q) ((s.boxes.map e.cells ∪ fixed).erase (e.cells t.player))
      rw [hb, Finset.map_insert, Finset.map_erase, Finset.erase_union_distrib,
        Finset.erase_eq_of_notMem (hfixed _ ht), Finset.insert_union]

/-- Ambient replay preserves every box, exact player position, and every intermediate step. -/
theorem Frame.replay {active goals : Finset (Cell w h)} {e : GridEmbedding w h W H}
    {B : Board W H} {fixed : Finset (Cell W H)} (frame : Frame active e B fixed)
    {s t : State w h} (hr : Reachable (board active goals) (some 1) s t) :
    Reachable B (some 1) (e.extend fixed s) (e.extend fixed t) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih =>
    exact ih.tail ⟨e.direction hm.choose,
      move_extend (fun p hp => frame.floor p ((floor_iff _ _ _).mp hp))
        (fun p hp => frame.fixed_avoids p ((floor_iff _ _ _).mp hp))
        frame.fixed_floor hm.choose_spec⟩

end PushPuzzle.PushS.FiniteWireFrame
