/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Single
public import PushFS.Components

/-!
# Placing local macros in an ambient board

An adjacency-preserving placement transports actual player steps, complete box
sets and static slot paths. External boxes stay outside the represented local
rectangle and remain fixed throughout a transported macro.
-/

@[expose] public section

namespace PushPuzzle.PushFS


/-- A placement of one rectangle, possibly changing its four directions. -/
structure GridEmbedding (w h W H : ℕ) where
  /-- Distinct local cells have distinct ambient cells. -/
  cells : Cell w h ↪ Cell W H
  /-- Direction transformation of the placement. -/
  direction : Direction → Direction
  /-- Unit movement remains unit movement in the transformed direction. -/
  adjacent : ∀ d p q, Adjacent d p q → Adjacent (direction d) (cells p) (cells q)

namespace GridEmbedding

variable {w h W H : ℕ}

/-- Translate a local rectangle by unary horizontal and vertical offsets. -/
def translate (dx dy : ℕ) (hx : dx + w ≤ W) (hy : dy + h ≤ H) : GridEmbedding w h W H where
  cells := {
    toFun p := (⟨dx + p.1.val, by omega⟩, ⟨dy + p.2.val, by omega⟩)
    inj' := by
      intro p q he
      have heX := congrArg (fun r : Cell W H => r.1.val) he
      have heY := congrArg (fun r : Cell W H => r.2.val) he
      change dx + p.1.val = dx + q.1.val at heX
      change dy + p.2.val = dy + q.2.val at heY
      apply Prod.ext <;> apply Fin.ext <;> omega }
  direction := id
  adjacent := by
    intro d p q ha
    change Adjacent d (⟨dx + p.1.val, by omega⟩, ⟨dy + p.2.val, by omega⟩)
      (⟨dx + q.1.val, by omega⟩, ⟨dy + q.2.val, by omega⟩)
    cases d <;> simp only [Adjacent, Fin.mk.injEq] at ha ⊢ <;> constructor <;> omega

/-- Retain all local boxes and add a fixed set of ambient boxes. -/
def extend (e : GridEmbedding w h W H) (outside : Finset (Cell W H)) (s : State w h) : State W H :=
  ⟨e.cells s.player, s.boxes.map e.cells ∪ outside⟩

/-- Exact agreement on every represented wall cell. -/
def WallsAgree (e : GridEmbedding w h W H) (sourceBoard : Board w h) (ambient : Board W H) : Prop :=
  ∀ p, e.cells p ∈ ambient.walls ↔ p ∈ sourceBoard.walls

theorem extend_valid {e : GridEmbedding w h W H} {sourceBoard : Board w h} {ambient : Board W H}
    (hw : e.WallsAgree sourceBoard ambient) {outside : Finset (Cell W H)}
    (hout : ∀ p, e.cells p ∉ outside) (houtw : Disjoint outside ambient.walls)
    {s : State w h} (hs : s.Valid sourceBoard) : (e.extend outside s).Valid ambient := by
  refine ⟨fun h => hs.1 ((hw s.player).mp h), ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro p hp hpw
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
      exact Finset.disjoint_left.mp hs.2.1 hq ((hw q).mp hpw)
    · exact Finset.disjoint_left.mp houtw hp hpw
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hp
      exact hs.2.2 (e.cells.injective he ▸ hq)
    · exact hout _ hp

/-- A local single-box step is the same real step with every ambient box fixed. -/
private theorem move_one {e : GridEmbedding w h W H} {sourceBoard : Board w h} {ambient : Board W H}
    (hw : e.WallsAgree sourceBoard ambient) {outside : Finset (Cell W H)}
    (hout : ∀ p, e.cells p ∉ outside) (houtw : Disjoint outside ambient.walls)
    {d : Direction} {s t : State w h} (hm : Move sourceBoard (some 1) d s t) :
    Move ambient (some 1) (e.direction d) (e.extend outside s) (e.extend outside t) := by
  obtain ⟨hv, ha, hf, hwalk | hpush⟩ := Move.single_iff.mp hm
  all_goals apply Move.single_iff.mpr
  · obtain ⟨he, hb⟩ := hwalk
    refine ⟨extend_valid hw hout houtw hv, e.adjacent _ _ _ ha,
      fun h => hf ((hw _).mp h), Or.inl ⟨?_, ?_⟩⟩
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨p, hp, hpe⟩ := Finset.mem_map.mp hp
        exact he (e.cells.injective hpe ▸ hp)
      · exact hout _ hp
    · simp only [extend, hb]
  · obtain ⟨hp, q, hq, hqw, hqe, hb⟩ := hpush
    refine ⟨extend_valid hw hout houtw hv, e.adjacent _ _ _ ha,
      fun h => hf ((hw _).mp h), Or.inr ⟨?_, e.cells q, e.adjacent _ _ _ hq,
        fun h => hqw ((hw _).mp h), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨t.player, hp, rfl⟩)
    · intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · obtain ⟨p, hp, hpe⟩ := Finset.mem_map.mp hmem
        exact hqe (e.cells.injective hpe ▸ hp)
      · exact hout _ hmem
    · change (t.boxes.map e.cells ∪ outside) =
        insert (e.cells q) ((s.boxes.map e.cells ∪ outside).erase (e.cells t.player))
      rw [hb, Finset.map_insert, Finset.map_erase, Finset.erase_union_distrib,
        Finset.erase_eq_of_notMem (hout _), Finset.insert_union]

/-- Transport every exact player state of a finite local macro. -/
theorem reachable_one {e : GridEmbedding w h W H} {sourceBoard : Board w h} {ambient : Board W H}
    (hw : e.WallsAgree sourceBoard ambient) {outside : Finset (Cell W H)}
    (hout : ∀ p, e.cells p ∉ outside) (houtw : Disjoint outside ambient.walls)
    {s t : State w h} (hr : Reachable sourceBoard (some 1) s t) :
    Reachable ambient (some 1) (e.extend outside s) (e.extend outside t) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail ⟨e.direction hm.choose, move_one hw hout houtw hm.choose_spec⟩

/-- Static box displacements survive placement in the same wall geometry. -/
theorem displacement {e : GridEmbedding w h W H} {sourceBoard : Board w h} {ambient : Board W H}
    (hw : e.WallsAgree sourceBoard ambient) {p q : Cell w h} (hd : Displacement sourceBoard p q) :
    Displacement ambient (e.cells p) (e.cells q) := by
  obtain ⟨hp, d, rear, hr, hq, hrw, hqw⟩ := hd
  exact ⟨fun h => hp ((hw _).mp h), e.direction d, e.cells rear,
    e.adjacent _ _ _ hr, e.adjacent _ _ _ hq,
    fun h => hrw ((hw _).mp h), fun h => hqw ((hw _).mp h)⟩

/-- Local static paths, including those matching canonical source and goal slots, survive placement. -/
theorem staticReach {e : GridEmbedding w h W H} {sourceBoard : Board w h} {ambient : Board W H}
    (hw : e.WallsAgree sourceBoard ambient) {p q : Cell w h} (hr : StaticReach sourceBoard p q) :
    StaticReach ambient (e.cells p) (e.cells q) :=
  hr.lift e.cells (fun _ _ hd => displacement hw hd)

end GridEmbedding
end PushPuzzle.PushFS
