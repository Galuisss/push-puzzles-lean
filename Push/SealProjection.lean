/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Seal
public import PushS.Holes

/-! Projection of real board moves onto the committed reader's three-hole column seal. -/

@[expose] public section
namespace PushPuzzle.Push.SealProjection

open PushFS PushS

variable {w h : ℕ}

/-- The seal coordinate increases upwards from the chosen bottom level. -/
def coordinate (Z : ℤ) (p : Cell w h) : ℤ := Z - p.2.val

def project (x : ℕ) (Z : ℤ) (E : Finset (Cell w h)) : Finset ℤ :=
  (E.filter fun p => p.1.val = x).image (coordinate Z)

/-- The actual unlabelled holes in the selected column. -/
def columnHoles (x : ℕ) (Z : ℤ) (s : PushFS.State w h) : Finset ℤ := project x Z (holes s)

@[simp] theorem mem_columnHoles {x : ℕ} {Z z : ℤ} {s : PushFS.State w h} :
    z ∈ columnHoles x Z s ↔ ∃ p ∈ holes s, p.1.val = x ∧ coordinate Z p = z := by
  simp only [columnHoles, project, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hx⟩, hz⟩
    exact ⟨p, hp, hx, hz⟩
  · rintro ⟨p, hp, hx, hz⟩
    exact ⟨p, ⟨hp, hx⟩, hz⟩

private theorem coordinate_injective {x : ℕ} {Z : ℤ} {p q : Cell w h}
    (hp : p.1.val = x) (hq : q.1.val = x) (hz : coordinate Z p = coordinate Z q) : p = q := by
  apply Prod.ext <;> apply Fin.ext
  · omega
  · simp only [coordinate] at hz
    omega

private theorem project_erase_on (x : ℕ) (Z : ℤ) (E : Finset (Cell w h))
    (q : Cell w h) (hq : q.1.val = x) :
    project x Z (E.erase q) = (project x Z E).erase (coordinate Z q) := by
  ext z
  simp only [project, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨p, ⟨⟨hpq, hp⟩, hx⟩, hz⟩
    refine ⟨?_, p, ⟨hp, hx⟩, hz⟩
    intro he
    exact hpq (coordinate_injective hx hq (hz.trans he))
  · rintro ⟨hzq, p, ⟨hp, hx⟩, hz⟩
    refine ⟨p, ⟨⟨?_, hp⟩, hx⟩, hz⟩
    intro he
    exact hzq (hz.symm.trans (congrArg (coordinate Z) he))

private theorem project_erase_off (x : ℕ) (Z : ℤ) (E : Finset (Cell w h))
    (q : Cell w h) (hq : q.1.val ≠ x) : project x Z (E.erase q) = project x Z E := by
  unfold project
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  exact fun hm => hq (Finset.mem_filter.mp hm).2

private theorem project_insert_on (x : ℕ) (Z : ℤ) (E : Finset (Cell w h))
    (q : Cell w h) (hq : q.1.val = x) :
    project x Z (insert q E) = insert (coordinate Z q) (project x Z E) := by
  simp only [project, Finset.filter_insert, ite_eq_left hq, Finset.image_insert]

private theorem project_insert_off (x : ℕ) (Z : ℤ) (E : Finset (Cell w h))
    (q : Cell w h) (hq : q.1.val ≠ x) : project x Z (insert q E) = project x Z E := by
  simp only [project, Finset.filter_insert, ite_eq_right hq]

private theorem mem_project {x : ℕ} {Z : ℤ} {E : Finset (Cell w h)} {p : Cell w h}
    (hp : p ∈ E) (hx : p.1.val = x) : coordinate Z p ∈ project x Z E :=
  Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩

private theorem run_interior_occupied {B : Board w h} {d : Direction}
    {s : PushFS.State w h} {n : ℕ} (run : Run B d s n)
    (hd : d = .north ∨ d = .south) {Z : ℤ} {p : Cell w h}
    (hx : p.1 = s.player.1)
    (hp : Seal.Between (coordinate Z s.player)
      (coordinate Z (run.cell ⟨n + 1, by omega⟩)) (coordinate Z p)) : p ∈ s.boxes := by
  have hend := run.position ⟨n + 1, by omega⟩
  have hpos : 0 < d.position p - d.position s.player ∧
      d.position p - d.position s.player ≤ n := by
    rcases hd with rfl | rfl <;>
      simp only [Direction.position, coordinate, Seal.Between] at hp hend ⊢ <;> omega
  let k := (d.position p - d.position s.player).toNat
  have hk : (k : ℤ) = d.position p - d.position s.player := Int.toNat_of_nonneg (by omega)
  let i : Fin (n + 2) := ⟨k, by omega⟩
  have hi := run.position i
  have hil := run.lane i
  have he : run.cell i = p := by
    apply Direction.cell_ext d
    · rcases hd with rfl | rfl <;> simp only [Direction.lane] at hil ⊢ <;>
        exact hil.trans (congrArg Fin.val hx).symm
    · change d.position (run.cell i) = d.position s.player + (k : ℤ) at hi
      omega
  rw [← he]
  exact run.occupied_at i (by change 0 < k; omega) (by change k ≤ n; omega)

private theorem vertical_push_projection {B : Board w h} {d : Direction}
    {s t : PushFS.State w h} {n : ℕ} {x : ℕ} {Z : ℤ}
    (hv : s.Valid B) (hn : 0 < n) (run : Run B d s n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south) :
    columnHoles x Z t = columnHoles x Z s ∨
      Seal.HoleStep (columnHoles x Z s) (columnHoles x Z t) := by
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
    apply Seal.HoleStep.transport (columnHoles x Z s) (coordinate Z s.player)
      (coordinate Z (run.cell 1)) (coordinate Z q)
    · exact mem_project (player_mem_holes hv) hsx
    · exact mem_project ((mem_holes _).mpr run.empty) hqX
    · have h := run.position 1
      rcases hd with rfl | rfl
      · left
        simp only [coordinate, Direction.position, Fin.val_one] at h ⊢
        omega
      · right
        simp only [coordinate, Direction.position, Fin.val_one] at h ⊢
        omega
    · have hfirst := run.position 1
      have hend := run.position ⟨n + 1, by omega⟩
      rcases hd with rfl | rfl
      · left
        simp only [coordinate, Direction.position, Fin.val_one] at hfirst hend ⊢
        dsimp [q]
        omega
      · right
        simp only [coordinate, Direction.position, Fin.val_one] at hfirst hend ⊢
        dsimp [q]
        omega
    · intro z hz hbetween
      obtain ⟨p, hp, hpx, hcoord⟩ := mem_columnHoles.mp hz
      have hpx' : p.1 = s.player.1 := Fin.ext (hpx.trans hsx.symm)
      have hpbox := run_interior_occupied run hd (Z := Z) hpx' (by simpa only [hcoord] using hbetween)
      exact (mem_holes _).mp hp hpbox
  · left
    have hbX : (run.cell 1).1.val ≠ x := fun hh => hsx ((hx 1).symm.trans hh)
    have hqX : q.1.val ≠ x := fun hh => hsx ((hx _).symm.trans hh)
    unfold columnHoles
    rw [he, project_insert_off _ _ _ _ hbX, project_erase_off _ _ _ _ hqX]

/-- Horizontal moves may consume a seal hole, while vertical moves perform its exact transport. -/
private theorem move_projection {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : PushFS.State w h} (x : ℕ) (Z : ℤ) (hm : Move B cap d s t)
    (hguard : d = .east ∨ d = .west → s.boxes ≠ t.boxes → t.player.1.val ≠ x) :
    columnHoles x Z t = columnHoles x Z s ∨
      Seal.HoleStep (columnHoles x Z s) (columnHoles x Z t) := by
  cases hm with
  | walk _ _ _ _ hb =>
    left
    simp only [columnHoles, holes, hb]
  | @push n hv hn hc run hp hb =>
    by_cases hd : d = .north ∨ d = .south
    · exact vertical_push_projection hv hn run hp hb hd
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
        exact Seal.HoleStep.erase _ _ (mem_project ((mem_holes _).mpr run.empty) hqx)
      · left
        rw [ht, project_erase_off _ _ _ _ hqx]
        rfl

/-- A true board step with no transverse creation of a hole in the selected seal column. -/
def GuardedStep (B : Board w h) (cap : Option ℕ) (x : ℕ)
    (s t : PushFS.State w h) : Prop :=
  ∃ d, Move B cap d s t ∧ (d = .east ∨ d = .west → s.boxes ≠ t.boxes → t.player.1.val ≠ x)

/-- Forgetting the geometric guard retains the exact real board trajectory. -/
theorem guarded_reachable {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x : ℕ} (hr : Relation.ReflTransGen (GuardedStep B cap x) s t) : Reachable B cap s t :=
  Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm.choose, hm.choose_spec.1⟩) _ _ hr

/-- A guarded board trajectory projects to ordinary one-dimensional transport/delete dynamics. -/
private theorem reachable_projection {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x : ℕ} (Z : ℤ) (hr : Relation.ReflTransGen (GuardedStep B cap x) s t) :
    Relation.ReflTransGen Seal.HoleStep (columnHoles x Z s) (columnHoles x Z t) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih =>
    obtain ⟨d, hm, hguard⟩ := hm
    rcases move_projection x Z hm hguard with he | hh
    · simpa only [he] using ih
    · exact ih.tail hh

/-- Reaching the landing hole closes the original upper door along every guarded trajectory. -/
private theorem reachable_seals {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x : ℕ} {Z L : ℤ} (hL : 7 ≤ L)
    (hr : Relation.ReflTransGen (GuardedStep B cap x) s t)
    (hs : columnHoles x Z s = ({0, L - 1, L} : Finset ℤ))
    (ht : 2 ∈ columnHoles x Z t) : L ∉ columnHoles x Z t := by
  exact Seal.uncoloured_landing_seals hL (hs ▸ reachable_projection Z hr) ht

/-- At a known column cell, projected membership is exactly actual emptiness. -/
theorem coordinate_mem_columnHoles {x : ℕ} {Z : ℤ} {s : PushFS.State w h} {p : Cell w h}
    (hx : p.1.val = x) : coordinate Z p ∈ columnHoles x Z s ↔ p ∈ holes s := by
  constructor
  · intro hp
    obtain ⟨q, hq, hqx, hcoord⟩ := mem_columnHoles.mp hp
    have he := coordinate_injective hqx hx hcoord
    exact he ▸ hq
  · intro hp
    exact mem_project hp hx

/-- A real player landing at coordinate two closes the seal's original upper hole. -/
theorem player_landing_seals {B : Board w h} {cap : Option ℕ} {s t : PushFS.State w h}
    {x : ℕ} {Z L : ℤ} (hL : 7 ≤ L)
    (hr : Relation.ReflTransGen (GuardedStep B cap x) s t) (hv : s.Valid B)
    (hs : columnHoles x Z s = ({0, L - 1, L} : Finset ℤ))
    (htx : t.player.1.val = x) (htz : coordinate Z t.player = 2) :
    L ∉ columnHoles x Z t := by
  apply reachable_seals hL hr hs
  rw [← htz, coordinate_mem_columnHoles htx]
  exact player_mem_holes ((guarded_reachable hr).valid hv)

end PushPuzzle.Push.SealProjection
