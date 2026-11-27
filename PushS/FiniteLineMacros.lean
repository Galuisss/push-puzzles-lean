/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Walking

/-! Arbitrary-length, bidirectional single-box sweeps on a gap-two straight track. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteLineMacros

open PushFS

/-- The working row and an adjacent exposed walking lane. -/
structure Line (W H : ℕ) where
  count : ℕ
  base : ℕ
  base_pos : 0 < base
  fits : base + 2*count + 1 < W
  row : Fin H
  lane : Fin H
  entry : Direction
  crossing : ∀ x : Fin W, Adjacent entry (x, lane) (x, row)
  hub : Fin W

variable {W H : ℕ}

namespace Line

/-- Every coordinate needed by either direction of the sweep. -/
def track (L : Line W H) (x : Fin W) : Prop :=
  L.base - 1 ≤ x.val ∧ x.val ≤ L.base + 2*L.count

/-- The complete lane segment used to reach all support cells from the hub. -/
def laneSegment (L : Line W H) (x : Fin W) : Prop :=
  min L.hub.val (L.base - 1) ≤ x.val ∧
    x.val ≤ max L.hub.val (L.base + 2*L.count)

/-- Boxes before the frontier have their low slot; the remaining boxes have their high slot. -/
def position (L : Line W H) (frontier : ℕ) (i : Fin L.count) : Cell W H :=
  (⟨L.base + 2*i.val + if i.val < frontier then 0 else 1, by
    have hi := i.isLt
    have hb := L.fits
    split <;> omega⟩, L.row)

def boxes (L : Line W H) (fixed : Finset (Cell W H)) (frontier : ℕ) : Finset (Cell W H) :=
  fixed ∪ Finset.univ.image (L.position frontier)

/-- Geometry and unchanged inventory along the track and walking lane. -/
structure Frame (L : Line W H) (B : Board W H) (fixed : Finset (Cell W H)) : Prop where
  fixed_floor : Disjoint fixed B.walls
  track_free : ∀ x, L.track x → Free B fixed (x, L.row)
  lane_free : ∀ x, L.laneSegment x → Free B fixed (x, L.lane)

private theorem position_track (L : Line W H) (frontier : ℕ) (i : Fin L.count) :
    L.track (L.position frontier i).1 := by
  have hi := i.isLt
  dsimp [track, position]
  split <;> omega

private theorem position_injective (L : Line W H) (frontier : ℕ) :
    Function.Injective (L.position frontier) := by
  intro i j he
  have hx := congrArg (fun p : Cell W H => p.1.val) he
  dsimp [position] at hx
  apply Fin.ext
  split_ifs at hx <;> omega

theorem Frame.boxes_floor {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) (frontier : ℕ) : Disjoint (L.boxes fixed frontier) B.walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.disjoint_left.mp F.fixed_floor hp hw
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (F.track_free _ (L.position_track frontier i)).1 hw

theorem Frame.lane_free_boxes {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) (frontier : ℕ) (x : Fin W) (hx : L.laneSegment x) :
    Free B (L.boxes fixed frontier) (x, L.lane) := by
  have hf := F.lane_free x hx
  refine ⟨hf.1, ?_⟩
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hf.2 hm
  · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    have hy : L.row = L.lane := congrArg Prod.snd he
    exact (L.crossing x).ne (by rw [hy])

private theorem Frame.track_free_boxes {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) (frontier : ℕ) (x : Fin W) (hx : L.track x)
    (hne : ∀ i, L.position frontier i ≠ (x, L.row)) :
    Free B (L.boxes fixed frontier) (x, L.row) := by
  have hf := F.track_free x hx
  refine ⟨hf.1, ?_⟩
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hf.2 hm
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact hne i hi

theorem image_relocate {α β : Type} [Fintype α] [DecidableEq β]
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

private theorem position_other (L : Line W H) {j : ℕ} (hj : j < L.count) (i : Fin L.count)
    (hi : i ≠ ⟨j, hj⟩) : L.position (j+1) i = L.position j i := by
  have hival : i.val ≠ j := fun he => hi (Fin.ext he)
  apply Prod.ext <;> apply Fin.ext
  · dsimp [position]
    split_ifs <;> omega
  · rfl

private theorem Frame.boxes_update {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) {j : ℕ} (hj : j < L.count) :
    insert (L.position (j+1) ⟨j, hj⟩)
      ((L.boxes fixed j).erase (L.position j ⟨j, hj⟩)) = L.boxes fixed (j+1) := by
  have hsource : L.position j ⟨j, hj⟩ ∉ fixed :=
    (F.track_free _ (L.position_track j ⟨j, hj⟩)).2
  have himage := image_relocate (L.position j) (L.position (j+1))
    (L.position_injective j) ⟨j, hj⟩ (L.position_other hj)
  dsimp [boxes]
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hsource, ← Finset.union_insert,
    himage]

private theorem Frame.boxes_update_back {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) {j : ℕ} (hj : j < L.count) :
    insert (L.position j ⟨j, hj⟩)
      ((L.boxes fixed (j+1)).erase (L.position (j+1) ⟨j, hj⟩)) = L.boxes fixed j := by
  have hsource : L.position (j+1) ⟨j, hj⟩ ∉ fixed :=
    (F.track_free _ (L.position_track (j+1) ⟨j, hj⟩)).2
  have himage := image_relocate (L.position (j+1)) (L.position j)
    (L.position_injective (j+1)) ⟨j, hj⟩ (fun i hi => (L.position_other hj i hi).symm)
  dsimp [boxes]
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hsource, ← Finset.union_insert,
    himage]

/-- Move the frontier one box leftward, with real walks to and from its support. -/
private theorem Frame.forward_step {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) {j : ℕ} (hj : j < L.count) :
    Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed j⟩
      ⟨(L.hub, L.lane), L.boxes fixed (j+1)⟩ := by
  let src := L.position j ⟨j, hj⟩
  let dst := L.position (j+1) ⟨j, hj⟩
  let support : Fin W := ⟨L.base + 2*j + 2, by have hb := L.fits; omega⟩
  have hsrc : src ∈ L.boxes fixed j :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩)
  have hfreeS : Free B (L.boxes fixed j) (support, L.row) := by
    apply F.track_free_boxes j support
    · dsimp [track, support]; omega
    · intro i he
      have hx := congrArg (fun p : Cell W H => p.1.val) he
      dsimp [position, support] at hx
      split_ifs at hx <;> omega
  have hfreeD : Free B (L.boxes fixed j) dst := by
    apply F.track_free_boxes j dst.1
    · exact L.position_track (j+1) _
    · intro i he
      have hx := congrArg (fun p : Cell W H => p.1.val) he
      dsimp [dst, position] at hx
      split_ifs at hx <;> omega
  have hlane : ∀ x : Fin W, min L.hub.val support.val ≤ x.val →
      x.val ≤ max L.hub.val support.val → Free B (L.boxes fixed j) (x, L.lane) := by
    intro x hx hx'
    apply F.lane_free_boxes j x
    have hb := L.base_pos
    dsimp [laneSegment, support] at *
    omega
  have hreturn : ∀ x : Fin W, min src.1.val L.hub.val ≤ x.val →
      x.val ≤ max src.1.val L.hub.val → Free B (L.boxes fixed j) (x, L.lane) := by
    intro x hx hx'
    apply F.lane_free_boxes j x
    have hb := L.base_pos
    dsimp [laneSegment, src, position] at *
    split_ifs at * <;> omega
  have hr := push_via_parallel_row (F.boxes_floor j) L.hub support src.1 dst.1 L.lane L.row
    L.entry .west (L.crossing support) (L.crossing src.1).reverse
    (by
      constructor
      · simp only [src, position, support, Fin.val_mk, lt_self_iff_false, ite_false]
      · rfl)
    (by
      constructor
      · simp only [src, dst, position, Fin.val_mk, lt_self_iff_false, Nat.lt_succ_self,
          ite_false, ite_true]
      · rfl) hfreeS hsrc hfreeD hlane hreturn
  change Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed j⟩
    ⟨(L.hub, L.lane), insert (L.position (j+1) ⟨j, hj⟩)
      ((L.boxes fixed j).erase (L.position j ⟨j, hj⟩))⟩ at hr
  rw [F.boxes_update hj] at hr
  exact hr

/-- Move the frontier one box rightward, with the same exact walking hub. -/
private theorem Frame.backward_step {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) {j : ℕ} (hj : j < L.count) :
    Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed (j+1)⟩
      ⟨(L.hub, L.lane), L.boxes fixed j⟩ := by
  let src := L.position (j+1) ⟨j, hj⟩
  let dst := L.position j ⟨j, hj⟩
  let support : Fin W := ⟨L.base + 2*j - 1, by have hb := L.fits; omega⟩
  have hsrc : src ∈ L.boxes fixed (j+1) :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩)
  have hfreeS : Free B (L.boxes fixed (j+1)) (support, L.row) := by
    apply F.track_free_boxes (j+1) support
    · have hb := L.base_pos; dsimp [track, support]; omega
    · intro i he
      have hx := congrArg (fun p : Cell W H => p.1.val) he
      have hb := L.base_pos
      dsimp [position, support] at hx
      split_ifs at hx <;> omega
  have hfreeD : Free B (L.boxes fixed (j+1)) dst := by
    apply F.track_free_boxes (j+1) dst.1
    · exact L.position_track j _
    · intro i he
      have hx := congrArg (fun p : Cell W H => p.1.val) he
      dsimp [dst, position] at hx
      split_ifs at hx <;> omega
  have hlane : ∀ x : Fin W, min L.hub.val support.val ≤ x.val →
      x.val ≤ max L.hub.val support.val → Free B (L.boxes fixed (j+1)) (x, L.lane) := by
    intro x hx hx'
    apply F.lane_free_boxes (j+1) x
    have hb := L.base_pos
    dsimp [laneSegment, support] at *
    omega
  have hreturn : ∀ x : Fin W, min src.1.val L.hub.val ≤ x.val →
      x.val ≤ max src.1.val L.hub.val → Free B (L.boxes fixed (j+1)) (x, L.lane) := by
    intro x hx hx'
    apply F.lane_free_boxes (j+1) x
    have hb := L.base_pos
    dsimp [laneSegment, src, position] at *
    split_ifs at * <;> omega
  have hr := push_via_parallel_row (F.boxes_floor (j+1)) L.hub support src.1 dst.1 L.lane L.row
    L.entry .east (L.crossing support) (L.crossing src.1).reverse
    (by
      constructor
      · have hb := L.base_pos
        simp only [src, position, support, Fin.val_mk, Nat.lt_succ_self, ite_true]
        omega
      · rfl)
    (by
      constructor
      · simp only [src, dst, position, Fin.val_mk, lt_self_iff_false, Nat.lt_succ_self,
          ite_false, ite_true]
      · rfl) hfreeS hsrc hfreeD hlane hreturn
  change Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed (j+1)⟩
    ⟨(L.hub, L.lane), insert (L.position j ⟨j, hj⟩)
      ((L.boxes fixed (j+1)).erase (L.position (j+1) ⟨j, hj⟩))⟩ at hr
  rw [F.boxes_update_back hj] at hr
  exact hr

/-- Update the complete line from high slots to low slots. -/
theorem Frame.forward {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) :
    Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed 0⟩
      ⟨(L.hub, L.lane), L.boxes fixed L.count⟩ := by
  have he : ∀ j, j ≤ L.count → Reachable B (some 1)
      ⟨(L.hub, L.lane), L.boxes fixed 0⟩ ⟨(L.hub, L.lane), L.boxes fixed j⟩ := by
    intro j hj
    induction j with
    | zero => exact .refl
    | succ j ih => exact (ih (by omega)).trans (F.forward_step (by omega))
  exact he L.count (by rfl)

/-- Update the complete line from low slots to high slots. -/
theorem Frame.backward {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) :
    Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed L.count⟩
      ⟨(L.hub, L.lane), L.boxes fixed 0⟩ := by
  have he : ∀ j, j ≤ L.count → Reachable B (some 1)
      ⟨(L.hub, L.lane), L.boxes fixed j⟩ ⟨(L.hub, L.lane), L.boxes fixed 0⟩ := by
    intro j hj
    induction j with
    | zero => exact .refl
    | succ j ih => exact (F.backward_step (by omega)).trans (ih (by omega))
  exact he L.count (by rfl)

end Line
end PushPuzzle.PushS.FiniteLineMacros
