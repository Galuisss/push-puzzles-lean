/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Basic

/-! Preserve actual fixed neighbor boxes outside a checked macro's coordinate footprint. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


variable {w h : ℕ}

/-- Add the actual stationary neighboring boxes to a represented local state. -/
def withFixed (fixed : Finset (Cell w h)) (s : State w h) : State w h :=
  ⟨s.player, s.boxes ∪ fixed⟩

/-- A coordinate-only checker covering the player, adjacent cell and possible pushed destination. -/
def clearFootprint (blocked : Cell w h → Bool) (p : Cell w h) : List Direction → Bool
  | [] => !blocked p
  | d :: ds => match neighbor d p with
    | none => false
    | some q => !blocked p && !blocked q &&
        (neighbor d q).elim true (fun r => !blocked r) && clearFootprint blocked q ds

private theorem add_walls {B : Board w h} {extra : Finset (Cell w h)}
    {d : Direction} {s t : State w h} (hm : Move B (some 1) d s t)
    (hs : s.Valid ⟨B.walls ∪ extra, B.goals⟩) (ht : t.player ∉ extra)
    (hq : ∀ q, Adjacent d t.player q → q ∉ extra) :
    Move ⟨B.walls ∪ extra, B.goals⟩ (some 1) d s t := by
  obtain ⟨_, ha, hf, hwalk | hpush⟩ := Move.single_iff.mp hm
  all_goals apply Move.single_iff.mpr
  · exact ⟨hs, ha, fun h => (Finset.mem_union.mp h).elim hf ht, Or.inl hwalk⟩
  · obtain ⟨hb, q, hadj, hw, he, hboxes⟩ := hpush
    exact ⟨hs, ha, fun h => (Finset.mem_union.mp h).elim hf ht,
      Or.inr ⟨hb, q, hadj, fun h => (Finset.mem_union.mp h).elim hw (hq q hadj), he, hboxes⟩⟩

private theorem move_withFixed {B : Board w h} {extra fixed : Finset (Cell w h)}
    (hf : fixed ⊆ extra) (hw : Disjoint fixed B.walls)
    {d : Direction} {s t : State w h}
    (hm : Move (⟨B.walls ∪ extra, B.goals⟩ : Board w h) (some 1) d s t) :
    Move B (some 1) d (withFixed fixed s) (withFixed fixed t) := by
  obtain ⟨hs, ha, ht, hwalk | hpush⟩ := Move.single_iff.mp hm
  all_goals
    have hvalid : (withFixed fixed s).Valid B := by
      refine ⟨fun h => hs.1 (Finset.mem_union_left _ h), ?_, ?_⟩
      · exact Finset.disjoint_union_left.mpr
          ⟨hs.2.1.mono_right Finset.subset_union_left, hw⟩
      · intro h
        exact (Finset.mem_union.mp h).elim hs.2.2
          (fun h => hs.1 (Finset.mem_union_right _ (hf h)))
    apply Move.single_iff.mpr
  · obtain ⟨he, hb⟩ := hwalk
    refine ⟨hvalid, ha, fun h => ht (Finset.mem_union_left _ h), Or.inl ⟨?_, ?_⟩⟩
    · intro h
      exact (Finset.mem_union.mp h).elim he
        (fun h => ht (Finset.mem_union_right _ (hf h)))
    · simp only [withFixed, hb]
  · obtain ⟨hp, q, hq, hqw, hqe, hb⟩ := hpush
    have htf : t.player ∉ fixed := fun h => ht (Finset.mem_union_right _ (hf h))
    refine ⟨hvalid, ha, fun h => ht (Finset.mem_union_left _ h), Or.inr ⟨?_, q, hq,
      fun h => hqw (Finset.mem_union_left _ h), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ hp
    · intro h
      exact (Finset.mem_union.mp h).elim hqe
        (fun h => hqw (Finset.mem_union_right _ (hf h)))
    · change t.boxes ∪ fixed = insert q ((s.boxes ∪ fixed).erase t.player)
      rw [hb, Finset.erase_union_distrib, Finset.erase_eq_of_notMem htf, Finset.insert_union]

/-- Replace any subset of reserved walls by actual stationary boxes. -/
theorem reachable_withFixed {B : Board w h} {extra fixed : Finset (Cell w h)}
    (hf : fixed ⊆ extra) (hw : Disjoint fixed B.walls) {s t : State w h}
    (hr : Reachable (⟨B.walls ∪ extra, B.goals⟩ : Board w h) (some 1) s t) :
    Reachable B (some 1) (withFixed fixed s) (withFixed fixed t) :=
  hr.lift (withFixed fixed) (fun _ _ h => ⟨h.choose, move_withFixed hf hw h.choose_spec⟩)

private theorem execute_avoiding {wall blocked : Cell w h → Bool} {B : Board w h}
    {extra : Finset (Cell w h)}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (hb : ∀ p, blocked p = true ↔ p ∈ extra)
    {s t : State w h} {ds : List Direction}
    (hs : s.Valid ⟨B.walls ∪ extra, B.goals⟩)
    (he : Execution.execute wall s ds = some t)
    (hc : clearFootprint blocked s.player ds = true) :
    Reachable ⟨B.walls ∪ extra, B.goals⟩ (some 1) s t := by
  induction ds generalizing s with
  | nil =>
    simp only [Execution.execute, Option.some.injEq] at he
    exact he ▸ .refl
  | cons d ds ih =>
    cases hn : neighbor d s.player with
    | none => simp [clearFootprint, hn] at hc
    | some q =>
      simp only [clearFootprint, hn, Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨_, hq⟩, hr⟩, htail⟩ := hc
      cases hm : Execution.perform wall d s with
      | none => simp [Execution.execute, hm] at he
      | some u =>
        have hs0 : s.Valid B := ⟨fun h => hs.1 (Finset.mem_union_left _ h),
          hs.2.1.mono_right Finset.subset_union_left, hs.2.2⟩
        have hmove := Execution.perform_sound hw hs0 hm
        have hmview := Move.single_iff.mp hmove
        have hu : u.player = q := hmview.2.1.functional (neighbor_sound hn)
        have hqu : u.player ∉ extra := by
          rw [hu, ← hb q, hq]
          decide
        have hnext : ∀ r, Adjacent d u.player r → r ∉ extra := by
          intro r ha hm
          have hn' : neighbor d q = some r := neighbor_complete (hu ▸ ha)
          rw [hn'] at hr
          have hf : blocked r = false := by simpa using hr
          rw [(hb r).mpr hm] at hf
          contradiction
        have hm' := add_walls hmove hs hqu hnext
        exact (Relation.ReflTransGen.single ⟨d, hm'⟩).trans
          (ih hm'.valid_target (by simpa [Execution.execute, hm] using he)
            (by simpa [hu] using htail))

/-- Every represented neighboring box in the checked reserved cells stays fixed. -/
theorem frame_checked {wall blocked : Cell w h → Bool} {B : Board w h}
    {extra fixed : Finset (Cell w h)}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (hb : ∀ p, blocked p = true ↔ p ∈ extra)
    {s t : State w h} {ds : List Direction}
    (hs : s.Valid ⟨B.walls ∪ extra, B.goals⟩)
    (he : Execution.execute wall s ds = some t)
    (hc : clearFootprint blocked s.player ds = true)
    (hf : fixed ⊆ extra) (hfw : Disjoint fixed B.walls) :
    Reachable B (some 1) (withFixed fixed s) (withFixed fixed t) :=
  reachable_withFixed hf hfw (execute_avoiding hw hb hs he hc)

end PushPuzzle.PushFS.Gadgets.Gates
