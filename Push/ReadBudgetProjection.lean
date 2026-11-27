/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnReadBudget
public import Push.SealProjection
import all Push.SealProjection

/-! Actual source-avoiding board trajectories obey the one-column reader budget. -/

@[expose] public section
namespace PushPuzzle.Push.ReadBudgetProjection

open PushFS PushS SealProjection

variable {w h : ℕ}

/-- At the selected column, the actual player stays outside the source coordinates. -/
def Outside (x : ℕ) (Z row : ℤ) (s : PushFS.State w h) : Prop :=
  s.player.1.val = x → coordinate Z s.player < row

private theorem vertical_geometry {B : Board w h} {d : Direction} {s : PushFS.State w h}
    {n : ℕ} (run : Run B d s n) (hn : 0 < n) (hd : d = .north ∨ d = .south) (Z : ℤ) :
    (coordinate Z (run.cell 1) = coordinate Z s.player + 1 ∨
      coordinate Z (run.cell 1) = coordinate Z s.player - 1) ∧
    Seal.Between (coordinate Z s.player) (coordinate Z (run.cell ⟨n + 1, by omega⟩))
      (coordinate Z (run.cell 1)) := by
  have hfirst := run.position 1
  have hend := run.position ⟨n + 1, by omega⟩
  rcases hd with rfl | rfl
  · simp only [coordinate, Direction.position, Fin.val_one, Seal.Between] at hfirst hend ⊢
    exact ⟨Or.inl (by omega), Or.inl ⟨by omega, by omega⟩⟩
  · simp only [coordinate, Direction.position, Fin.val_one, Seal.Between] at hfirst hend ⊢
    exact ⟨Or.inr (by omega), Or.inr ⟨by omega, by omega⟩⟩

private theorem vertical_ray {B : Board w h} {d : Direction} {s : PushFS.State w h}
    {n x : ℕ} (run : Run B d s n) (hv : s.Valid B) (hn : 0 < n)
    (hd : d = .north ∨ d = .south) (Z : ℤ) (hsx : s.player.1.val = x) :
    Seal.Ray ⟨columnHoles x Z s, ∅, 0, 0⟩ (coordinate Z s.player)
      (coordinate Z (run.cell 1)) (coordinate Z (run.cell ⟨n + 1, by omega⟩)) := by
  have hx (i : Fin (n + 2)) : (run.cell i).1.val = s.player.1.val := by
    have := run.lane i
    rcases hd with rfl | rfl <;> exact this
  obtain ⟨hadj, hbetween⟩ := vertical_geometry run hn hd Z
  refine ⟨?_, ?_, hadj, hbetween, ?_⟩
  · simpa only [Seal.State.holes, Finset.union_empty, columnHoles] using
      mem_project (player_mem_holes hv) hsx
  · simpa only [Seal.State.holes, Finset.union_empty, columnHoles] using
      mem_project ((mem_holes _).mpr run.empty) ((hx _).trans hsx)
  · intro z hz hbetween
    simp only [Seal.State.holes, Finset.union_empty] at hz
    obtain ⟨p, hp, hpx, hcoord⟩ := mem_columnHoles.mp hz
    have hpx' : p.1 = s.player.1 := Fin.ext (hpx.trans hsx.symm)
    have hpbox := run_interior_occupied run hd (Z := Z) hpx'
      (by simpa only [hcoord] using hbetween)
    exact (mem_holes _).mp hp hpbox

private theorem vertical_push_projection {B : Board w h} {d : Direction}
    {s t : PushFS.State w h} {n : ℕ} {x : ℕ} {Z row : ℤ}
    (hv : s.Valid B) (hn : 0 < n) (run : Run B d s n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south) (hsout : Outside x Z row s) (htout : Outside x Z row t) :
    columnHoles x Z t = columnHoles x Z s ∨
      ColumnReadBudget.Step row (columnHoles x Z s) (columnHoles x Z t) := by
  let q := run.cell ⟨n + 1, by omega⟩
  have hx (i : Fin (n + 2)) : (run.cell i).1.val = s.player.1.val := by
    have := run.lane i
    rcases hd with rfl | rfl <;> exact this
  have he : holes t = insert (run.cell 1) ((holes s).erase q) := holes_push run hn hb
  by_cases hsx : s.player.1.val = x
  · right
    have hbX : (run.cell 1).1.val = x := (hx 1).trans hsx
    have hqX : q.1.val = x := (hx _).trans hsx
    have ht : columnHoles x Z t =
        insert (coordinate Z (run.cell 1)) ((columnHoles x Z s).erase (coordinate Z q)) := by
      unfold columnHoles
      rw [he, project_insert_on _ _ _ _ hbX, project_erase_on _ _ _ _ hqX]
    rw [ht]
    have ray := vertical_ray run hv hn hd Z hsx
    apply ColumnReadBudget.Step.transport (columnHoles x Z s) (coordinate Z s.player)
      (coordinate Z (run.cell 1)) (coordinate Z q)
    · simpa only [Seal.State.holes, Finset.union_empty] using ray.support
    · simpa only [Seal.State.holes, Finset.union_empty] using ray.destination
    · exact ray.adjacent
    · exact ray.intermediate
    · simpa only [Seal.State.holes, Finset.union_empty] using ray.occupied
    · exact hsout hsx
    · rw [← hp]
      exact htout (by rwa [hp])
  · left
    have hbX : (run.cell 1).1.val ≠ x := fun hh => hsx ((hx 1).symm.trans hh)
    have hqX : q.1.val ≠ x := fun hh => hsx ((hx _).symm.trans hh)
    unfold columnHoles
    rw [he, project_insert_off _ _ _ _ hbX, project_erase_off _ _ _ _ hqX]

/-- A real step projects to a permitted one-dimensional deletion or source-avoiding transport. -/
private theorem move_projection {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : PushFS.State w h} (x : ℕ) (Z row : ℤ) (hm : Move B cap d s t)
    (hguard : d = .east ∨ d = .west → s.boxes ≠ t.boxes → t.player.1.val ≠ x)
    (hsout : Outside x Z row s) (htout : Outside x Z row t) :
    columnHoles x Z t = columnHoles x Z s ∨
      ColumnReadBudget.Step row (columnHoles x Z s) (columnHoles x Z t) := by
  cases hm with
  | walk _ _ _ _ hb =>
    left
    simp only [columnHoles, holes, hb]
  | @push n hv hn hc run hp hb =>
    by_cases hd : d = .north ∨ d = .south
    · exact vertical_push_projection hv hn run hp hb hd hsout htout
    · have dh : d = .east ∨ d = .west := by cases d <;> simp_all
      have hchanged : s.boxes ≠ t.boxes := by
        intro heq
        have hv' := (Move.push hv hn hc run hp hb).valid_target
        have hplayer : t.player ∈ s.boxes := hp.symm ▸ run.first_occupied hn
        exact hv'.2.2 (heq ▸ hplayer)
      have hpx : (run.cell 1).1.val ≠ x := by simpa only [hp] using hguard dh hchanged
      let q := run.cell ⟨n + 1, by omega⟩
      have he : holes t = insert (run.cell 1) ((holes s).erase q) := holes_push run hn hb
      have ht : columnHoles x Z t = project x Z ((holes s).erase q) := by
        unfold columnHoles
        rw [he, project_insert_off _ _ _ _ hpx]
      by_cases hqx : q.1.val = x
      · right
        rw [ht, project_erase_on _ _ _ _ hqx]
        exact ColumnReadBudget.Step.erase _ _ (mem_project ((mem_holes _).mpr run.empty) hqx)
      · left
        rw [ht, project_erase_off _ _ _ _ hqx]
        rfl

/-- The physical guard and source avoidance needed during one column read. -/
def GuardedStep (B : Board w h) (cap : Option ℕ) (x : ℕ) (Z row : ℤ)
    (s t : PushFS.State w h) : Prop :=
  SealProjection.GuardedStep B cap x s t ∧ Outside x Z row s ∧ Outside x Z row t

private theorem guarded_reachable {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x : ℕ} {Z row : ℤ} (hr : Relation.ReflTransGen (GuardedStep B cap x Z row) s t) :
    Reachable B cap s t :=
  SealProjection.guarded_reachable (Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hr)

/-- Every intermediate real step lifts to the restricted column dynamics. -/
private theorem reachable_projection {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x : ℕ} {Z row : ℤ} (hr : Relation.ReflTransGen (GuardedStep B cap x Z row) s t) :
    Relation.ReflTransGen (ColumnReadBudget.Step row) (columnHoles x Z s) (columnHoles x Z t) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih =>
    obtain ⟨⟨d, hm, hguard⟩, hsout, htout⟩ := hm
    rcases move_projection x Z row hm hguard hsout htout with he | hh
    · simpa only [he] using ih
    · exact ih.tail hh

/-- In physical y-coordinates, source avoidance means the player remains below the source. -/
theorem outside_iff {x cutoff : ℕ} {Z : ℤ} {s : PushFS.State w h} :
    Outside x Z (Z - cutoff + 1) s ↔ (s.player.1.val = x → cutoff ≤ s.player.2.val) := by
  unfold Outside coordinate
  constructor <;> intro hs hx <;> have := hs hx <;> omega

/-- Source holes in an actual column and above the original source bottom. -/
def sourceCells (x cutoff : ℕ) (s : PushFS.State w h) : Finset (Cell w h) :=
  (holes s).filter fun p => p.1.val = x ∧ p.2.val < cutoff

private theorem sources_eq (x cutoff : ℕ) (Z : ℤ) (s : PushFS.State w h) :
    ColumnReadBudget.sources (Z - cutoff + 1) (columnHoles x Z s) =
      (sourceCells x cutoff s).image (coordinate Z) := by
  ext z
  simp only [ColumnReadBudget.sources, Finset.mem_filter, mem_columnHoles,
    sourceCells, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨p, hp, hx, hz⟩, hsource⟩
    refine ⟨p, ⟨hp, hx, ?_⟩, hz⟩
    dsimp [coordinate] at hz
    omega
  · rintro ⟨p, ⟨hp, hx, hy⟩, hz⟩
    refine ⟨⟨p, hp, hx, hz⟩, ?_⟩
    dsimp [coordinate] at hz
    omega

/-- Projection retains the exact number of source holes in the selected column. -/
private theorem sources_card (x cutoff : ℕ) (Z : ℤ) (s : PushFS.State w h) :
    (ColumnReadBudget.sources (Z - cutoff + 1) (columnHoles x Z s)).card =
      (sourceCells x cutoff s).card := by
  rw [sources_eq]
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  exact coordinate_injective (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hq).2.1 he

/-- Frontier advancement plus remaining source inventory fits the original source inventory. -/
theorem player_advance_budget {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x cutoff : ℕ} {Z f : ℤ}
    (hr : Relation.ReflTransGen (GuardedStep B cap x Z (Z - cutoff + 1)) s t)
    (hv : s.Valid B) (hs : ColumnReadBudget.Split (Z - cutoff + 1) f (columnHoles x Z s))
    (htx : t.player.1.val = x) (hty : cutoff ≤ t.player.2.val) :
    coordinate Z t.player - f + ((sourceCells x cutoff t).card : ℤ) ≤
      ((sourceCells x cutoff s).card : ℤ) := by
  have ht := player_mem_holes ((guarded_reachable hr).valid hv)
  have hmem : coordinate Z t.player ∈ columnHoles x Z t :=
    (coordinate_mem_columnHoles htx).mpr ht
  have hout : coordinate Z t.player < Z - cutoff + 1 := by dsimp [coordinate]; omega
  have hb := ColumnReadBudget.advance_paid_by_distinct_sources (reachable_projection hr) hs hmem hout
  have hc := Finset.card_sdiff_add_card_eq_card
    (ColumnReadBudget.sources_subset (reachable_projection hr))
  rw [sources_card x cutoff Z s, sources_card x cutoff Z t] at hc
  omega

end PushPuzzle.Push.ReadBudgetProjection
