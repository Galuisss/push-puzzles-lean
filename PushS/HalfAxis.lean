/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Boundary
public import PushS.Holes

/-!
# Half-axis occupancy before rail inventories are balanced

A fixed-length outer train, a possibly empty gap, and a solid suffix reaching the middle cut
retain their shape under real full-run pushes. The middle cut remains occupied and may be
crossed by pushes. Transverse pushes preserve occupancy on the half-axis.

The local argument is the upper-half-axis invariant in the joint proof, Section 5.1.
-/

public section
namespace PushPuzzle.PushS.HalfAxis

open PushFS Boundary

private structure Pattern (L M : ℕ) (f : ℕ → Prop) where
  front : ℕ
  gap : ℕ
  fits : front + L + gap < M
  occupied : ∀ y, 1 ≤ y → y ≤ M →
    (f y ↔ (front < y ∧ y ≤ front + L) ∨ front + L + gap < y)

variable {L M b : ℕ} {f g : ℕ → Prop}

private theorem Pattern.front_empty (P : Pattern L M f) {y : ℕ} (hy : 1 ≤ y)
    (ha : y ≤ P.front) : ¬f y := by
  rw [P.occupied y hy (by have := P.fits; omega)]
  omega

private theorem Pattern.gap_empty (P : Pattern L M f) {y : ℕ}
    (hl : P.front + L < y) (hr : y ≤ P.front + L + P.gap) : ¬f y := by
  rw [P.occupied y (by omega) (by have := P.fits; omega)]
  omega

private theorem Pattern.change (P : Pattern L M f) {a gap q z : ℕ}
    (hfit : a + L + gap < M)
    (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q))
    (harith : ∀ y, 1 ≤ y → y ≤ M →
      ((y = z ∨ (((P.front < y ∧ y ≤ P.front + L) ∨
        P.front + L + P.gap < y) ∧ y ≠ q)) ↔
          (a < y ∧ y ≤ a + L) ∨ a + L + gap < y)) : Nonempty (Pattern L M g) := by
  refine ⟨⟨a, gap, hfit, ?_⟩⟩
  intro y hy hm
  rw [hupdate, P.occupied y hy hm]
  exact harith y hy hm

private theorem Pattern.south_start (P : Pattern L M f) (hL : 1 ≤ L)
    {p q : ℕ} (hpq : q = p + 1) (hq : q ≤ M) (hbox : f q) (hp : ¬f p) :
    q = P.front + 1 ∨ (q = P.front + L + P.gap + 1 ∧ 0 < P.gap) := by
  have hq' := (P.occupied q (by omega) hq).mp hbox
  by_cases hp0 : p = 0
  · subst p
    have := P.fits
    omega
  · have hp' : ¬((P.front < p ∧ p ≤ P.front + L) ∨ P.front + L + P.gap < p) :=
      fun h => hp ((P.occupied p (by omega) (by omega)).mpr h)
    omega

private theorem Pattern.destination_south (P : Pattern L M f)
    {q z : ℕ} (hz : ¬f z) (hqz : q < z)
    (hfull : ∀ y, q ≤ y → y < z → f y)
    (hq : q = P.front + 1) (hg : 0 < P.gap) : z = P.front + L + 1 := by
  have hf : ¬f (P.front + L + 1) := P.gap_empty (by omega) (by omega)
  have hupper : z ≤ P.front + L + 1 := by
    by_contra h
    exact hf (hfull _ (by omega) (by omega))
  have hz0 : 1 ≤ z := by omega
  have hzm : z ≤ M := by have := P.fits; omega
  have hpat := (P.occupied z hz0 hzm).not.mp hz
  omega

private theorem Pattern.south_merged (P : Pattern L M f)
    (hbudget : ∀ a, a ≤ M → (∀ y, 1 ≤ y → y ≤ a → ¬g y) → a ≤ b)
    (hmargin : L + b < M) {q z : ℕ} (hq : q = P.front + 1) (hqz : q < z)
    (hg : P.gap = 0) (hz : ¬f z)
    (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q)) : Nonempty (Pattern L M g) := by
  have hfit := P.fits
  have hzM : M < z := by
    by_contra h
    have h := (P.occupied z (by omega) (by omega)).not.mp hz
    omega
  have hfront : P.front + 1 ≤ b := by
    apply hbudget _ (by have := P.fits; omega)
    intro y hy ha
    rw [hupdate, P.occupied y hy (by omega)]
    omega
  refine P.change (a := P.front + 1) (gap := 0) (q := q) (z := z) (by omega) hupdate ?_
  intro y hy hm
  omega

private theorem Pattern.south (P : Pattern L M f) (hL : 1 ≤ L)
    (hbudget : ∀ a, a ≤ M → (∀ y, 1 ≤ y → y ≤ a → ¬g y) → a ≤ b)
    (hmargin : L + b < M) {p q z : ℕ} (hpq : q = p + 1) (hqz : q < z)
    (hp : ¬f p) (hz : ¬f z) (hfull : ∀ y, q ≤ y → y < z → f y)
    (hmid : g M) (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q)) :
    Nonempty (Pattern L M g) := by
  by_cases hq : q ≤ M
  · rcases P.south_start hL hpq hq (hfull q le_rfl hqz) hp with hq | ⟨hq, hg⟩
    · by_cases hg : 0 < P.gap
      · have hz' := P.destination_south hz hqz hfull hq hg
        refine P.change (a := P.front + 1) (gap := P.gap - 1) (q := q) (z := z)
          (by have := P.fits; omega) hupdate ?_
        intro y hy hm
        omega
      · exact P.south_merged hbudget hmargin hq hqz (by omega) hz hupdate
    · have hzM : M < z := by
        by_contra h
        have h := (P.occupied z (by omega) (by omega)).not.mp hz
        omega
      have hqM : q < M := by
        have h := (hupdate M).mp hmid
        omega
      refine P.change (a := P.front) (gap := P.gap + 1) (q := q) (z := z)
        (by omega) hupdate ?_
      intro y hy hm
      omega
  · refine P.change (a := P.front) (gap := P.gap) (q := q) (z := z) P.fits hupdate ?_
    intro y hy hm
    omega

private theorem Pattern.north_start (P : Pattern L M f) (hL : 1 ≤ L)
    {p q : ℕ} (hpq : p = q + 1) (hq : q < M) (hbox : f q) (hp : ¬f p)
    (hzero : ¬f 0) : q = P.front + L ∧ 0 < P.gap := by
  have hq0 : 1 ≤ q := by
    by_contra h
    have : q = 0 := by omega
    exact hzero (this ▸ hbox)
  have hq' := (P.occupied q hq0 (by omega)).mp hbox
  have hp' : ¬((P.front < p ∧ p ≤ P.front + L) ∨ P.front + L + P.gap < p) :=
    fun h => hp ((P.occupied p (by omega) (by omega)).mpr h)
  omega

private theorem Pattern.destination_north (P : Pattern L M f)
    {q z : ℕ} (hz : ¬f z) (hzq : z < q)
    (hfull : ∀ y, z < y → y ≤ q → f y) (hq : q = P.front + L) : z = P.front := by
  have hza : z ≤ P.front := by
    by_contra h
    have h := (P.occupied z (by omega) (by have := P.fits; omega)).not.mp hz
    omega
  by_contra h
  have ha0 : 1 ≤ P.front := by omega
  exact P.front_empty ha0 le_rfl (hfull _ (by omega) (by omega))

private theorem Pattern.north_cross (P : Pattern L M f) (hL : 1 ≤ L)
    {q z : ℕ} (hq : M < q) (hz0 : 1 ≤ z) (hzM : z ≤ M) (hz : ¬f z)
    (hfull : ∀ y, z < y → y ≤ q → f y)
    (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q)) : Nonempty (Pattern L M g) := by
  have hz' := (P.occupied z hz0 hzM).not.mp hz
  by_cases hg : 0 < P.gap
  · have hdest : z = P.front + L + P.gap := by
      have hupper : z ≤ P.front + L + P.gap := by omega
      by_contra h
      exact P.gap_empty (by omega) le_rfl
        (hfull _ (by omega) (by have := P.fits; omega))
    refine P.change (a := P.front) (gap := P.gap - 1) (q := q) (z := z)
      (by have := P.fits; omega) hupdate ?_
    intro y hy hm
    omega
  · have hg0 : P.gap = 0 := by omega
    have hdest : z = P.front := by
      have hupper : z ≤ P.front := by omega
      by_contra h
      exact P.front_empty (by omega) le_rfl
        (hfull _ (by omega) (by have := P.fits; omega))
    refine P.change (a := P.front - 1) (gap := 0) (q := q) (z := z)
      (by have := P.fits; omega) hupdate ?_
    intro y hy hm
    omega

private theorem Pattern.north (P : Pattern L M f) (hL : 1 ≤ L)
    {p q z : ℕ} (hpq : p = q + 1) (hzq : z < q) (hp : ¬f p) (hz : ¬f z)
    (hfull : ∀ y, z < y → y ≤ q → f y) (hzero : ¬f 0) (hzero' : ¬g 0)
    (hmid : g M) (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q)) :
    Nonempty (Pattern L M g) := by
  have hz0 : 1 ≤ z := by
    by_contra h
    have : z = 0 := by omega
    exact hzero' ((hupdate 0).mpr (Or.inl this.symm))
  by_cases hq : q ≤ M
  · have hqM : q < M := by have h := (hupdate M).mp hmid; omega
    obtain ⟨hq', hg⟩ := P.north_start hL hpq hqM (hfull q hzq le_rfl) hp hzero
    have hz' := P.destination_north hz hzq hfull hq'
    refine P.change (a := P.front - 1) (gap := P.gap + 1) (q := q) (z := z)
      (by have := P.fits; omega) hupdate ?_
    intro y hy hm
    omega
  · by_cases hzM : z ≤ M
    · exact P.north_cross hL (by omega) hz0 hzM hz hfull hupdate
    · refine P.change (a := P.front) (gap := P.gap) (q := q) (z := z) P.fits hupdate ?_
      intro y hy hm
      omega

variable {w h : ℕ}

/-- An interior column, read from the top frame to an interior middle cut. -/
structure Rail (w h : ℕ) where
  /-- Column carrying the signal train. -/
  column : Fin w
  /-- Last cell of the upper half-axis. -/
  cut : Fin h
  /-- The column avoids the left frame. -/
  left : 0 < column.val
  /-- The column avoids the right frame. -/
  right : column.val + 1 < w
  /-- The cut avoids the bottom frame. -/
  bottom : cut.val + 1 < h

/-- Occupancy at one depth on the specified column; depths outside the rectangle are empty. -/
@[expose] def Rail.Occupied (A : Rail w h) (s : State w h) (y : ℕ) : Prop :=
  ∃ p ∈ s.boxes, p.1 = A.column ∧ p.2.val = y

/-- The half-axis is `0^front 1^L 0^gap 1^tail`, with a nonempty final solid suffix. -/
@[expose] def Shape (A : Rail w h) (L : ℕ) (s : State w h) : Prop :=
  ∃ front gap, front + L + gap < A.cut.val ∧ ∀ y, 1 ≤ y → y ≤ A.cut.val →
    (A.Occupied s y ↔ (front < y ∧ y ≤ front + L) ∨ front + L + gap < y)

private theorem shape_pattern (A : Rail w h) (s : State w h) :
    Shape A L s ↔ Nonempty (Pattern L A.cut.val (A.Occupied s)) := by
  constructor
  · rintro ⟨a, gap, hfit, hocc⟩
    exact ⟨⟨a, gap, hfit, hocc⟩⟩
  · rintro ⟨P⟩
    exact ⟨P.front, P.gap, P.fits, P.occupied⟩

private theorem occupied_cell (A : Rail w h) (s : State w h) (p : Cell w h)
    (hx : p.1 = A.column) : A.Occupied s p.2.val ↔ p ∈ s.boxes := by
  constructor
  · rintro ⟨q, hq, hqx, hqy⟩
    have he : q = p := Prod.ext (hqx.trans hx.symm) (Fin.ext hqy)
    exact he ▸ hq
  · exact fun hp => ⟨p, hp, hx, rfl⟩

private theorem frame_zero (A : Rail w h) {s : State w h}
    (hf : Disjoint s.boxes frame) : ¬A.Occupied s 0 := by
  rintro ⟨p, hp, _hx, hy⟩
  apply Finset.disjoint_left.mp hf hp
  exact mem_frame p |>.mpr ⟨.north, by simp [edge, hy]⟩

/-- An empty prefix of this interior column is paid for by the full interior-hole inventory. -/
private theorem Rail.empty_prefix_le (A : Rail w h) (s : State w h) (a : ℕ) (ha : a ≤ A.cut.val)
    (hempty : ∀ y, 1 ≤ y → y ≤ a → ¬A.Occupied s y) : a ≤ (holes s \ frame).card := by
  let point : Fin a → Cell w h := fun i =>
    (A.column, ⟨i.val + 1, by have := A.cut.isLt; omega⟩)
  have hinj : Function.Injective point := by
    intro i j he
    have hv := congrArg (fun p : Cell w h => p.2.val) he
    exact Fin.ext (by dsimp only [point] at hv; omega)
  have hsub : Finset.univ.image point ⊆ holes s \ frame := by
    intro p hp
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · apply (mem_holes _).mpr
      intro hb
      exact hempty (i.val + 1) (by omega) (by omega) ⟨point i, hb, rfl, rfl⟩
    · have hl := A.left
      have hr := A.right
      have ht := A.bottom
      simp [point, frame, edge]
      omega
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

private theorem occupied_update (A : Rail w h) {s t : State w h} {q z : Cell w h}
    (hb : t.boxes = insert z (s.boxes.erase q)) (y : ℕ) :
    A.Occupied t y ↔ (z.1 = A.column ∧ z.2.val = y) ∨
      (A.Occupied s y ∧ ¬(q.1 = A.column ∧ q.2.val = y)) := by
  constructor
  · rintro ⟨p, hp, hx, hy⟩
    rw [hb, Finset.mem_insert, Finset.mem_erase] at hp
    rcases hp with rfl | ⟨hne, hp⟩
    · exact Or.inl ⟨hx, hy⟩
    · refine Or.inr ⟨⟨p, hp, hx, hy⟩, ?_⟩
      rintro ⟨hqx, hqy⟩
      exact hne (Prod.ext (hx.trans hqx.symm) (Fin.ext (hy.trans hqy.symm)))
  · rintro (⟨hx, hy⟩ | ⟨⟨p, hp, hx, hy⟩, hne⟩)
    · exact ⟨z, hb ▸ Finset.mem_insert_self _ _, hx, hy⟩
    · refine ⟨p, ?_, hx, hy⟩
      rw [hb]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨fun he => hne (he ▸ ⟨hx, hy⟩), hp⟩)

private theorem shape_congr (A : Rail w h) {s t : State w h} (hs : Shape A L s)
    (he : ∀ y, 1 ≤ y → y ≤ A.cut.val → (A.Occupied t y ↔ A.Occupied s y)) :
    Shape A L t := by
  obtain ⟨a, gap, hfit, hocc⟩ := hs
  exact ⟨a, gap, hfit, fun y hy hm => (he y hy hm).trans (hocc y hy hm)⟩

variable {B : Board w h} {cap : Option ℕ} {s t : State w h} {n : ℕ}

private theorem run_column (A : Rail w h) {d : Direction} (r : Run B d s n)
    (hd : d = .north ∨ d = .south) (hx : s.player.1 = A.column) (i : Fin (n + 2)) :
    (r.cell i).1 = A.column := by
  have hl := r.lane i
  apply Fin.ext
  rcases hd with rfl | rfl <;> simpa only [Direction.lane, hx] using hl

private theorem run_full_south (A : Rail w h) (r : Run B .south s n)
    (hx : s.player.1 = A.column) (y : ℕ)
    (hq : (r.cell 1).2.val ≤ y) (hz : y < (r.cell ⟨n + 1, by omega⟩).2.val) :
    A.Occupied s y := by
  have hfirst := r.position 1
  have hlast := r.position ⟨n + 1, by omega⟩
  simp only [Direction.position, Fin.val_one] at hfirst hlast
  let i : Fin (n + 2) := ⟨y - s.player.2.val, by omega⟩
  have hi := r.position i
  simp only [Direction.position] at hi
  refine ⟨r.cell i, r.occupied_at i (by dsimp only [i]; omega)
    (by dsimp only [i]; omega), run_column A r (Or.inr rfl) hx i, ?_⟩
  have hiv : i.val = y - s.player.2.val := rfl
  omega

/-- Every depth between a north push's first hole and first box has an actual occupied run index. -/
theorem north_index (r : Run B .north s n) (y : ℕ)
    (hz : (r.cell ⟨n + 1, by omega⟩).2.val < y) (hq : y ≤ (r.cell 1).2.val) :
    ∃ i : Fin n, (r.cell ⟨i.val + 1, by omega⟩).2.val = y := by
  have hfirst := r.position 1
  have hlast := r.position ⟨n + 1, by omega⟩
  simp only [Direction.position, Fin.val_one] at hfirst hlast
  let i : Fin n := ⟨s.player.2.val - y - 1, by omega⟩
  have hi := r.position ⟨i.val + 1, by omega⟩
  simp only [Direction.position] at hi
  exact ⟨i, by have hiv : i.val = s.player.2.val - y - 1 := rfl; omega⟩

private theorem run_full_north (A : Rail w h) (r : Run B .north s n)
    (hx : s.player.1 = A.column) (y : ℕ)
    (hz : (r.cell ⟨n + 1, by omega⟩).2.val < y) (hq : y ≤ (r.cell 1).2.val) :
    A.Occupied s y := by
  obtain ⟨i, hi⟩ := north_index r y hz hq
  exact ⟨_, r.occupied i, run_column A r (Or.inl rfl) hx _, hi⟩

private theorem occupied_push_off (A : Rail w h)
    {d : Direction} (r : Run B d s n) (hd : d = .north ∨ d = .south)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (hx : s.player.1 ≠ A.column) (y : ℕ) : A.Occupied t y ↔ A.Occupied s y := by
  have hoff (i : Fin (n + 2)) : (r.cell i).1 ≠ A.column := by
    have hl := r.lane i
    intro he
    apply hx
    apply Fin.ext
    rcases hd with rfl | rfl <;> simpa only [Direction.lane, he] using hl.symm
  simpa only [hoff, false_and, false_or, not_false_eq_true, and_true] using
    occupied_update A hb y

private theorem push_shape (A : Rail w h) (hs : Shape A L s) (hL : 1 ≤ L)
    (hmargin : L + b < A.cut.val) {d : Direction} (r : Run B d s n) (hn : 0 < n)
    (hv : s.Valid B) (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩)
      (s.boxes.erase (r.cell 1))) (hd : d = .north ∨ d = .south)
    (hsframe : Disjoint s.boxes frame) (htframe : Disjoint t.boxes frame)
    (hmid : A.Occupied t A.cut.val) (hbudget : (holes t \ frame).card ≤ b) : Shape A L t := by
  by_cases hx : s.player.1 = A.column
  · obtain ⟨P⟩ := (shape_pattern A s).mp hs
    have hqx := run_column A r hd hx 1
    have hzx := run_column A r hd hx ⟨n + 1, by omega⟩
    have hupdate (y : ℕ) : A.Occupied t y ↔ y = (r.cell ⟨n + 1, by omega⟩).2.val ∨
        (A.Occupied s y ∧ y ≠ (r.cell 1).2.val) := by
      simpa only [hqx, hzx, true_and, eq_comm] using occupied_update A hb y
    have hp : ¬A.Occupied s s.player.2.val :=
      fun h => hv.2.2 ((occupied_cell A s s.player hx).mp h)
    have hz : ¬A.Occupied s (r.cell ⟨n + 1, by omega⟩).2.val :=
      fun h => r.empty ((occupied_cell A s _ hzx).mp h)
    have hfirst := r.position 1
    have hlast := r.position ⟨n + 1, by omega⟩
    apply (shape_pattern A t).mpr
    rcases hd with rfl | rfl
    · simp only [Direction.position, Fin.val_one] at hfirst hlast
      exact P.north hL (by omega) (by omega) hp hz (run_full_north A r hx)
        (frame_zero A hsframe) (frame_zero A htframe) hmid hupdate
    · simp only [Direction.position, Fin.val_one] at hfirst hlast
      exact P.south hL (fun a ha he => (A.empty_prefix_le t a ha he).trans hbudget)
        hmargin (by omega) (by omega) hp hz (run_full_south A r hx) hmid hupdate
  · exact shape_congr A hs (fun y _ _ => occupied_push_off A r hd hb hx y)

/-- A real move retains the half-axis shape, including long pushes through its occupied cut.
The empty frame, occupied cut, and global hole budget control longitudinal pushes;
transverse moves preserve occupancy. The rail inventory may change. -/
theorem move_shape (A : Rail w h) (hs : Shape A L s) (hL : 1 ≤ L)
    (hmargin : L + b < A.cut.val) {d : Direction} (hm : Move B cap d s t)
    (hsframe : Disjoint s.boxes frame) (htframe : Disjoint t.boxes frame)
    (hmid : (A.column, A.cut) ∈ t.boxes) (hbudget : (holes t \ frame).card ≤ b)
    (htransverse : d = .east ∨ d = .west → ∀ y, 1 ≤ y → y ≤ A.cut.val →
      (A.Occupied t y ↔ A.Occupied s y)) : Shape A L t := by
  by_cases hd : d = .north ∨ d = .south
  · cases hm with
    | walk _ _ _ _ hb => simpa only [Shape, Rail.Occupied, hb] using hs
    | push hv hn _ r _ hb =>
      exact push_shape A hs hL hmargin r hn hv hb hd hsframe htframe
        ⟨(A.column, A.cut), hmid, rfl, rfl⟩ hbudget
  · exact shape_congr A hs (htransverse (by cases d <;> simp_all))

/-- Established geometric facts carried by one genuine step before inventory cancellation. -/
structure GuardedStep (B : Board w h) (cap : Option ℕ) (A : Rail w h) (b : ℕ)
    (s t : State w h) : Prop where
  /-- The original puzzle step. -/
  step : Step B cap s t
  /-- The old frame is empty. -/
  source_frame : Disjoint s.boxes frame
  /-- The new frame is empty. -/
  target_frame : Disjoint t.boxes frame
  /-- The middle cell stays occupied, including during pushes crossing it. -/
  middle : (A.column, A.cut) ∈ t.boxes
  /-- Full interior-hole budget at the new state. -/
  budget : (holes t \ frame).card ≤ b
  /-- Transverse moves preserve half-axis occupancy, allowing exchanges of physical identities. -/
  transverse : ∀ d, Move B cap d s t → d = .east ∨ d = .west →
    ∀ y, 1 ≤ y → y ≤ A.cut.val → (A.Occupied t y ↔ A.Occupied s y)

/-- The full real trajectory preserves the half-axis shape without fixing its box inventory. -/
theorem reachable_shape (A : Rail w h) (hL : 1 ≤ L) (hmargin : L + b < A.cut.val)
    (hr : Relation.ReflTransGen (GuardedStep B cap A b) s t) (hs : Shape A L s) :
    Shape A L t := by
  induction hr with
  | refl => exact hs
  | tail _ hm ih =>
    obtain ⟨d, hd⟩ := hm.step
    exact move_shape A ih hL hmargin hd hm.source_frame hm.target_frame hm.middle hm.budget
      (hm.transverse d hd)

/-- Occupancy of the first interior cell removes the entire leading hole prefix. -/
theorem Shape.anchored (A : Rail w h) (hs : Shape A L s) (hfirst : A.Occupied s 1) :
    ∃ gap, L + gap < A.cut.val ∧ ∀ y, 1 ≤ y → y ≤ A.cut.val →
      (A.Occupied s y ↔ y ≤ L ∨ L + gap < y) := by
  obtain ⟨a, gap, hfit, hocc⟩ := hs
  have h1 := (hocc 1 le_rfl (by omega)).mp hfirst
  have ha : a = 0 := by omega
  subst a
  refine ⟨gap, by omega, ?_⟩
  intro y hy hm
  rw [hocc y hy hm]
  omega

/-- The first row-clear constraints confine all remaining half-axis holes to its three work slots.
For an outer train of length `u-1`, the occupied test cell is depth `u+3`. -/
theorem Shape.work_slots (A : Rail w h) (hs : Shape A L s)
    (hfirst : A.Occupied s 1) (hafter : A.Occupied s (L + 4)) :
    ∃ gap, gap ≤ 3 ∧ L + gap < A.cut.val ∧ ∀ y, 1 ≤ y → y ≤ A.cut.val →
      (¬A.Occupied s y ↔ L < y ∧ y ≤ L + gap) := by
  obtain ⟨gap, hfit, hocc⟩ := hs.anchored A hfirst
  have hg : gap ≤ 3 := by
    by_contra h
    have htest := (hocc (L + 4) (by omega) (by omega)).mp hafter
    omega
  refine ⟨gap, hg, hfit, ?_⟩
  intro y hy hm
  rw [hocc y hy hm]
  omega

/-- For the ordinary three-hole pocket at depth `u`, row clearing anchors its remaining gap
at depth `u` and confines it to the three cells ending at `u+2`. -/
theorem Shape.pocket_work_slots (A : Rail w h) (u : ℕ) (hu : 1 ≤ u)
    (hs : Shape A (u - 1) s) (hfirst : A.Occupied s 1) (hafter : A.Occupied s (u + 3)) :
    ∃ gap, gap ≤ 3 ∧ u - 1 + gap < A.cut.val ∧ ∀ y, 1 ≤ y → y ≤ A.cut.val →
      (¬A.Occupied s y ↔ u ≤ y ∧ y < u + gap) := by
  have ht : A.Occupied s (u - 1 + 4) := by simpa only [show u - 1 + 4 = u + 3 by omega] using hafter
  obtain ⟨gap, hg, hfit, hocc⟩ := Shape.work_slots A hs hfirst ht
  refine ⟨gap, hg, hfit, ?_⟩
  intro y hy hm
  rw [hocc y hy hm]
  omega

private structure TailPattern (M V : ℕ) (f : ℕ → Prop) where
  stop : ℕ
  lower : M < stop
  upper : stop ≤ V
  occupied : ∀ y, M ≤ y → y < V → (f y ↔ y < stop)

variable {V : ℕ}

private theorem TailPattern.change (P : TailPattern M V f) {stop q z : ℕ}
    (hl : M < stop) (hu : stop ≤ V) (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q))
    (harith : ∀ y, M ≤ y → y < V →
      ((y = z ∨ (y < P.stop ∧ y ≠ q)) ↔ y < stop)) : Nonempty (TailPattern M V g) := by
  refine ⟨⟨stop, hl, hu, ?_⟩⟩
  intro y hy hv
  rw [hupdate, P.occupied y hy hv]
  exact harith y hy hv

private theorem TailPattern.south (P : TailPattern M V f) {p q z : ℕ}
    (hpq : q = p + 1) (hqz : q < z) (hp : ¬f p) (hz : ¬f z)
    (hfull : ∀ y, q ≤ y → y < z → f y) (hmid : g M)
    (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q)) : Nonempty (TailPattern M V g) := by
  have hqoff : q < M ∨ V ≤ q := by
    by_contra h
    have hq' := (P.occupied q (by omega) (by omega)).mp (hfull q le_rfl hqz)
    have hMq : M < q := by have hh := (hupdate M).mp hmid; omega
    have hp' := (P.occupied p (by omega) (by omega)).not.mp hp
    omega
  by_cases hzIn : M ≤ z ∧ z < V
  · have hz' := (P.occupied z hzIn.1 hzIn.2).not.mp hz
    have hdest : z = P.stop := by
      by_contra h
      have hlo := P.lower
      have he := (P.occupied P.stop (by have := P.lower; omega) (by omega)).mp
        (hfull P.stop (by omega) (by omega))
      omega
    refine P.change (stop := P.stop + 1) (q := q) (z := z)
      (by have := P.lower; omega) (by omega) hupdate ?_
    intro y hy hv
    omega
  · refine P.change (stop := P.stop) (q := q) (z := z) P.lower P.upper hupdate ?_
    intro y hy hv
    omega

private theorem TailPattern.north (P : TailPattern M V f) {p q z : ℕ}
    (hpq : p = q + 1) (hzq : z < q) (hp : ¬f p) (hz : ¬f z)
    (hfull : ∀ y, z < y → y ≤ q → f y) (hmid : g M)
    (hentry : V ≤ q → V ≤ z)
    (hupdate : ∀ y, g y ↔ y = z ∨ (f y ∧ y ≠ q)) : Nonempty (TailPattern M V g) := by
  by_cases hqIn : M ≤ q ∧ q < V
  · have hq' := (P.occupied q hqIn.1 hqIn.2).mp (hfull q hzq le_rfl)
    have hMq : M < q := by have hh := (hupdate M).mp hmid; omega
    have hstop : P.stop = q + 1 := by
      by_cases hpV : p < V
      · have hp' := (P.occupied p (by omega) hpV).not.mp hp
        omega
      · have := P.upper
        omega
    have hzM : z < M := by
      by_contra h
      have hz' := (P.occupied z (by omega) (by omega)).not.mp hz
      omega
    refine P.change (stop := q) (q := q) (z := z) hMq (by omega) hupdate ?_
    intro y hy hv
    omega
  · have hqoff : q < M ∨ V ≤ q := by omega
    have hzoff : z < M ∨ V ≤ z := by rcases hqoff with h | h; omega; exact Or.inr (hentry h)
    refine P.change (stop := P.stop) (q := q) (z := z) P.lower P.upper hupdate ?_
    intro y hy hv
    omega

/-- A north push on this column cannot import a box through the working row from below. -/
@[expose] def NoNorthInput (B : Board w h) (A : Rail w h) (work : Fin h)
    (s t : State w h) : Prop :=
  ∀ n (r : Run B .north s n), 0 < n → t.player = r.cell 1 →
    t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)) →
    s.player.1 = A.column → work.val ≤ (r.cell 1).2.val →
      work.val ≤ (r.cell ⟨n + 1, by omega⟩).2.val

/-- The lower half-axis has a nonempty solid prefix and a hole suffix ending before the work row. -/
@[expose] def LowerShape (A : Rail w h) (work : Fin h) (s : State w h) : Prop :=
  ∃ stop, A.cut.val < stop ∧ stop ≤ work.val ∧ ∀ y, A.cut.val ≤ y → y < work.val →
    (A.Occupied s y ↔ y < stop)

private theorem lower_pattern (A : Rail w h) (work : Fin h) (s : State w h) :
    LowerShape A work s ↔ Nonempty (TailPattern A.cut.val work.val (A.Occupied s)) := by
  constructor
  · rintro ⟨stop, hl, hu, hocc⟩
    exact ⟨⟨stop, hl, hu, hocc⟩⟩
  · rintro ⟨P⟩
    exact ⟨P.stop, P.lower, P.upper, P.occupied⟩

private theorem lower_congr (A : Rail w h) (work : Fin h) (hs : LowerShape A work s)
    (he : ∀ y, A.cut.val ≤ y → y < work.val → (A.Occupied t y ↔ A.Occupied s y)) :
    LowerShape A work t := by
  obtain ⟨stop, hl, hu, hocc⟩ := hs
  exact ⟨stop, hl, hu, fun y hy hv => (he y hy hv).trans (hocc y hy hv)⟩

private theorem push_lower_shape (A : Rail w h) (work : Fin h) (hs : LowerShape A work s)
    {d : Direction} (r : Run B d s n) (hn : 0 < n) (hv : s.Valid B)
    (hp : t.player = r.cell 1)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (hd : d = .north ∨ d = .south) (hmid : A.Occupied t A.cut.val)
    (hentry : NoNorthInput B A work s t) : LowerShape A work t := by
  by_cases hx : s.player.1 = A.column
  · obtain ⟨P⟩ := (lower_pattern A work s).mp hs
    have hqx := run_column A r hd hx 1
    have hzx := run_column A r hd hx ⟨n + 1, by omega⟩
    have hupdate (y : ℕ) : A.Occupied t y ↔ y = (r.cell ⟨n + 1, by omega⟩).2.val ∨
        (A.Occupied s y ∧ y ≠ (r.cell 1).2.val) := by
      simpa only [hqx, hzx, true_and, eq_comm] using occupied_update A hb y
    have hplayer : ¬A.Occupied s s.player.2.val :=
      fun h => hv.2.2 ((occupied_cell A s s.player hx).mp h)
    have hz : ¬A.Occupied s (r.cell ⟨n + 1, by omega⟩).2.val :=
      fun h => r.empty ((occupied_cell A s _ hzx).mp h)
    have hfirst := r.position 1
    have hlast := r.position ⟨n + 1, by omega⟩
    apply (lower_pattern A work t).mpr
    rcases hd with rfl | rfl
    · simp only [Direction.position, Fin.val_one] at hfirst hlast
      exact P.north (by omega) (by omega) hplayer hz (run_full_north A r hx) hmid
        (hentry n r hn hp hb hx) hupdate
    · simp only [Direction.position, Fin.val_one] at hfirst hlast
      exact P.south (by omega) (by omega) hplayer hz (run_full_south A r hx) hmid hupdate
  · exact lower_congr A work hs (fun y _ _ => occupied_push_off A r hd hb hx y)

/-- The lower half-axis retains a single terminal hole suffix under real full-run moves.
The work row may exchange boxes outward, and northward import is explicitly excluded. -/
theorem lower_move_shape (A : Rail w h) (work : Fin h) (hs : LowerShape A work s)
    {d : Direction} (hm : Move B cap d s t) (hmid : (A.column, A.cut) ∈ t.boxes)
    (hentry : NoNorthInput B A work s t)
    (htransverse : d = .east ∨ d = .west → ∀ y, A.cut.val ≤ y → y < work.val →
      (A.Occupied t y ↔ A.Occupied s y)) : LowerShape A work t := by
  by_cases hd : d = .north ∨ d = .south
  · cases hm with
    | walk _ _ _ _ hb => simpa only [LowerShape, Rail.Occupied, hb] using hs
    | push hv hn _ r hp hb =>
      exact push_lower_shape A work hs r hn hv hp hb hd
        ⟨(A.column, A.cut), hmid, rfl, rfl⟩ hentry
  · exact lower_congr A work hs (htransverse (by cases d <;> simp_all))

/-- Real lower-half steps with the fixed-back-neighbour endpoint condition. -/
structure LowerGuardedStep (B : Board w h) (cap : Option ℕ) (A : Rail w h) (work : Fin h)
    (s t : State w h) : Prop where
  /-- The original puzzle step. -/
  step : Step B cap s t
  /-- The middle cut remains occupied. -/
  middle : (A.column, A.cut) ∈ t.boxes
  /-- North pushes cannot import a box from the work row. -/
  north_input : NoNorthInput B A work s t
  /-- Transverse moves preserve lower-half occupancy. -/
  transverse : ∀ d, Move B cap d s t → d = .east ∨ d = .west →
    ∀ y, A.cut.val ≤ y → y < work.val → (A.Occupied t y ↔ A.Occupied s y)

/-- The lower shape persists along the same genuine board trajectory. -/
theorem lower_reachable_shape (A : Rail w h) (work : Fin h)
    (hr : Relation.ReflTransGen (LowerGuardedStep B cap A work) s t)
    (hs : LowerShape A work s) : LowerShape A work t := by
  induction hr with
  | refl => exact hs
  | tail _ hm ih =>
    obtain ⟨d, hd⟩ := hm.step
    exact lower_move_shape A work ih hd hm.middle hm.north_input (hm.transverse d hd)

/-- Occupancy three cells before the work row confines the lower hole suffix to its final two slots. -/
theorem LowerShape.work_slots (A : Rail w h) (work : Fin h) (hs : LowerShape A work s)
    (hbefore : A.Occupied s (work.val - 3)) :
    ∃ count, count ≤ 2 ∧ count < work.val - A.cut.val ∧
      ∀ y, A.cut.val ≤ y → y < work.val →
        (¬A.Occupied s y ↔ work.val - count ≤ y) := by
  obtain ⟨stop, hl, hu, hocc⟩ := hs
  have hc : work.val - stop ≤ 2 := by
    by_contra h
    have htest := (hocc (work.val - 3) (by omega) (by omega)).mp hbefore
    omega
  refine ⟨work.val - stop, hc, by omega, ?_⟩
  intro y hy hv
  rw [hocc y hy hv]
  omega

end PushPuzzle.PushS.HalfAxis
