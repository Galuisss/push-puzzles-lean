/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Distant
public import PushS.Support
import all PushS.Support
import all PushS.Distant

/-!
# Actual departures from the frame into sparse streets

Adjacent supported player positions select a complete street. A departure from the empty frame
therefore starts at a selected column on the top or bottom edge, or a selected row on a side.
The excursion budget retains this actual departure point through repeated returns to the frame.
-/

public section

namespace PushPuzzle.PushS.Support


open PushFS Boundary

variable {w h : ℕ}

/-- The boundary ports of the selected complete streets. -/
@[expose] def frameExits (X : Set (Fin w)) (Y : Set (Fin h)) : Set (Cell w h) :=
  {p | ((p ∈ edge .north ∨ p ∈ edge .south) ∧ p.1 ∈ X) ∨
    ((p ∈ edge .west ∨ p ∈ edge .east) ∧ p.2 ∈ Y)}

private theorem vertical_frame_side {p q : Cell w h} (hp : p ∈ frame) (hq : q ∉ frame)
    (hx : q.1 = p.1) : p ∈ edge .north ∨ p ∈ edge .south := by
  obtain ⟨e, he⟩ := (mem_frame p).mp hp
  cases e with
  | north => exact Or.inl he
  | south => exact Or.inr he
  | east =>
    apply False.elim
    apply hq
    refine (mem_frame q).mpr ⟨.east, ?_⟩
    simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and, hx] using he
  | west =>
    apply False.elim
    apply hq
    refine (mem_frame q).mpr ⟨.west, ?_⟩
    simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and, hx] using he

private theorem horizontal_frame_side {p q : Cell w h} (hp : p ∈ frame) (hq : q ∉ frame)
    (hy : q.2 = p.2) : p ∈ edge .west ∨ p ∈ edge .east := by
  obtain ⟨e, he⟩ := (mem_frame p).mp hp
  cases e with
  | west => exact Or.inl he
  | east => exact Or.inr he
  | north =>
    apply False.elim
    apply hq
    refine (mem_frame q).mpr ⟨.north, ?_⟩
    simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and, hy] using he
  | south =>
    apply False.elim
    apply hq
    refine (mem_frame q).mpr ⟨.south, ?_⟩
    simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and, hy] using he

variable {B : Board w h} {cap : Option ℕ} {X : Set (Fin w)} {Y : Set (Fin h)}
  {s t : State w h}

/-- Every actual supported step leaving the frame uses one of its street ports. -/
theorem step_frame_exit (hX : Separated X) (hY : Separated Y) (hm : Step B cap s t)
    (hs : Supported (streets X Y) s) (ht : Supported (streets X Y) t)
    (hp : s.player ∈ frame) (hq : t.player ∉ frame) : s.player ∈ frameExits X Y := by
  obtain ⟨d, hm⟩ := hm
  have hs' := hs _ hm.valid_source.2.2
  have ht' := ht _ hm.valid_target.2.2
  have ha := players_adjacent hm
  cases d with
  | north =>
    have hc := vertical_column hY ht' hs' ha.1.symm ha.2
    exact Or.inl ⟨vertical_frame_side hp hq ha.1, ha.1 ▸ hc⟩
  | south =>
    exact Or.inl ⟨vertical_frame_side hp hq ha.1,
      vertical_column hY hs' ht' ha.1 ha.2.symm⟩
  | east =>
    exact Or.inr ⟨horizontal_frame_side hp hq ha.2,
      horizontal_row hX hs' ht' ha.2 ha.1.symm⟩
  | west =>
    have hc := horizontal_row hX ht' hs' ha.2.symm ha.1
    exact Or.inr ⟨horizontal_frame_side hp hq ha.2, ha.2 ▸ hc⟩

private theorem supported_frame_path (hX : Separated X) (hY : Separated Y)
    (hr : Reachable B cap s t) (hf : Disjoint t.boxes frame)
    (ht : Supported (streets X Y) t) :
    Relation.ReflTransGen (fun u v => Radius.PreservingStep B cap frame u v ∧
      Supported (streets X Y) u ∧ Supported (streets X Y) v) s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih =>
    have hu := (streets_axisClosed hX hY).step_source hm ht
    have huf := reachable_frame_empty (Relation.ReflTransGen.single hm) hf
    exact (ih huf hu).tail ⟨⟨hm, Distant.frame_holes hf⟩, hu, ht⟩

/-- Every off-frame player position is within the interior-hole budget of an actual frame port. -/
theorem reachable_frame_distance (hX : Separated X) (hY : Separated Y)
    (hr : Reachable B cap s t) (hp : s.player ∈ frame) (hf : Disjoint t.boxes frame)
    (ht : Supported (streets X Y) t) :
    t.player ∈ frame ∨ ∃ a ∈ frameExits X Y, distance a t.player ≤ (holes s \ frame).card := by
  apply Radius.reachable_distance_from_exits
    (R := fun u v => Radius.PreservingStep B cap frame u v ∧
      Supported (streets X Y) u ∧ Supported (streets X Y) v)
    (fun ⦃_ _⦄ h => h.1)
    (fun ⦃_ _⦄ h hi ho => step_frame_exit hX hY h.1.1 h.2.1 h.2.2 hi ho)
    (supported_frame_path hX hY hr hf ht)
  · exact Distant.frame_holes (reachable_frame_empty hr hf)
  · exact hp

private theorem border_distance {n x y b : ℕ} (hl : b < x) (hr : b + x + 1 < n)
    (hy : y = 0 ∨ y + 1 = n) : b < Nat.dist y x := by
  rcases hy with hy | hy <;> simp only [Nat.dist] <;> omega

/-- A horizontal gap in the selected columns separates a cell from every possible frame exit. -/
theorem frameExits_far_of_column_gap {b : ℕ} {q : Cell w h}
    (hl : b < q.1.val) (hr : b + q.1.val + 1 < w)
    (hx : ∀ x ∈ X, b < Nat.dist x.val q.1.val) :
    ∀ a ∈ frameExits X Y, b < distance a q := by
  intro a ha
  have hd : b < Nat.dist a.1.val q.1.val := by
    rcases ha with ⟨_, hax⟩ | ⟨ha, _⟩
    · exact hx a.1 hax
    · apply border_distance hl hr
      simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  simp only [distance]
  omega

/-- A vertical gap in the selected rows separates a cell from every possible frame exit. -/
theorem frameExits_far_of_row_gap {b : ℕ} {q : Cell w h}
    (ht : b < q.2.val) (hb : b + q.2.val + 1 < h)
    (hy : ∀ y ∈ Y, b < Nat.dist y.val q.2.val) :
    ∀ a ∈ frameExits X Y, b < distance a q := by
  intro a ha
  have hd : b < Nat.dist a.2.val q.2.val := by
    rcases ha with ⟨ha, _⟩ | ⟨_, hay⟩
    · apply border_distance ht hb
      simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and, or_comm] using ha
    · exact hy a.2 hay
  simp only [distance]
  omega

/-- Distance from the actual frame ports excludes an off-frame cell from a successful play. -/
theorem player_ne_of_frame_exits (hX : Separated X) (hY : Separated Y)
    (hr : Reachable B cap s t) (hp : s.player ∈ frame) (hf : Disjoint t.boxes frame)
    (ht : Supported (streets X Y) t) {g : Cell w h} (hg : g ∉ frame)
    (hfar : ∀ a ∈ frameExits X Y, (holes s \ frame).card < distance a g) : t.player ≠ g := by
  rcases reachable_frame_distance hX hY hr hp hf ht with hframe | ⟨a, ha, hd⟩
  · exact fun he => hg (he ▸ hframe)
  · intro he
    rw [he] at hd
    have := hfar a ha
    omega

/-- A required distant endpoint hole persists at every prefix of the supported play. -/
theorem hole_at_of_frame_exits {u : State w h} (hX : Separated X) (hY : Separated Y)
    (hsu : Reachable B cap s u) (hut : Reachable B cap u t) (hp : s.player ∈ frame)
    (hf : Disjoint t.boxes frame) (ht : Supported (streets X Y) t)
    {g : Cell w h} (hg : g ∉ frame)
    (hfar : ∀ a ∈ frameExits X Y, (holes s \ frame).card < distance a g)
    (hgt : g ∈ holes t) : g ∈ holes u := by
  induction hut with
  | refl => exact hgt
  | tail huv hm ih =>
    have hne := player_ne_of_frame_exits hX hY (hsu.trans (huv.tail hm)) hp hf ht hg hfar
    exact ih (reachable_frame_empty (Relation.ReflTransGen.single hm) hf)
      ((streets_axisClosed hX hY).step_source hm ht)
      (hole_source_of_ne_player hm.choose_spec (Ne.symm hne) hgt)

/-- An initially occupied distant crossing remains occupied along the supported play. -/
theorem box_at_of_frame_exits {u : State w h} (hX : Separated X) (hY : Separated Y)
    (hsu : Reachable B cap s u) (hut : Reachable B cap u t) (hp : s.player ∈ frame)
    (hf : Disjoint t.boxes frame) (ht : Supported (streets X Y) t)
    {g : Cell w h}
    (hfar : ∀ a ∈ frameExits X Y, (holes s \ frame).card < distance a g)
    (hgs : g ∈ s.boxes) : g ∈ u.boxes := by
  by_contra hgu
  have hframe := reachable_frame_empty (hsu.trans hut) hf
  have hg : g ∉ frame := fun h => Finset.disjoint_left.mp hframe hgs h
  have hh := hole_at_of_frame_exits hX hY .refl hsu hp (reachable_frame_empty hut hf)
    ((streets_axisClosed hX hY).reachable_source hut ht) hg hfar ((mem_holes _).mpr hgu)
  exact (mem_holes _).mp hh hgs

end PushPuzzle.PushS.Support
