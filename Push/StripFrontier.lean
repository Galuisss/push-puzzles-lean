/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Holes

/-! Before the first southern visit to a western strip, advancing north holes consumes a southern hole. -/

@[expose] public section
namespace PushPuzzle.Push.StripFrontier

open PushFS PushS

variable {w h : ℕ}

/-- Original southern holes in the selected western strip. -/
def south (cut row : ℕ) (s : State w h) : Finset (Cell w h) :=
  (holes s).filter fun q => q.1.val < cut ∧ row ≤ q.2.val

/-- The strip has a northern hole frontier and a separate southern hole region. -/
def Split (cut row frontier : ℕ) (s : State w h) : Prop :=
  ∀ q ∈ holes s, q.1.val < cut → q.2.val ≤ frontier ∨ row ≤ q.2.val

/-- The player has not visited the southern part of the strip. -/
def North (cut row : ℕ) (s : State w h) : Prop :=
  s.player.1.val < cut → s.player.2.val < row

/-- A first visit across a gap wider than one cell must enter through the eastern boundary. -/
theorem enter_west {B : Board w h} {cap : Option ℕ} {d : Direction} {s t : State w h}
    {cut row f : ℕ} (hm : Move B cap d s t) (hs : Split cut row f s)
    (hN : North cut row s) (hgap : f + 1 < row)
    (hx : t.player.1.val < cut) (hy : row ≤ t.player.2.val) :
    d = .west ∧ s.player.1.val = cut ∧ t.player.1.val + 1 = cut := by
  have hv : s.Valid B := by cases hm <;> assumption
  have hsource := hs s.player ((mem_holes _).mpr hv.2.2)
  have ha := players_adjacent hm
  cases d with
  | north =>
    obtain ⟨hax, hay⟩ := ha
    have hsx : s.player.1.val < cut := by rw [← hax]; exact hx
    have := hN hsx
    omega
  | east =>
    obtain ⟨hax, hay⟩ := ha
    have hsx : s.player.1.val < cut := by omega
    have hNy := hN hsx
    have := congrArg Fin.val hay
    omega
  | south =>
    obtain ⟨hax, hay⟩ := ha
    have hsx : s.player.1.val < cut := by rw [← hax]; exact hx
    have hNy := hN hsx
    have hs' := hsource hsx
    omega
  | west =>
    obtain ⟨hax, hay⟩ := ha
    have hy' := congrArg Fin.val hay
    have hsx : cut ≤ s.player.1.val := by
      by_contra h
      have hNy := hN (by omega)
      omega
    exact ⟨rfl, by omega, by omega⟩

private theorem advance_geometry {B : Board w h} {d : Direction} {s t : State w h}
    {n cut row f : ℕ} (r : Run B d s n) (hv : s.Valid B)
    (hp : t.player = r.cell 1) (hs : Split cut row f s) (hN : North cut row s)
    (htN : North cut row t) (htx : t.player.1.val < cut) (hty : f < t.player.2.val) :
    t.player.2.val = f + 1 ∧ r.cell ⟨n + 1, by omega⟩ ∈ south cut row s := by
  have ha : Adjacent d s.player t.player := by
    simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, r.start, ← hp] using r.adjacent 0
  have htx' := htN htx
  have hstart := hs s.player ((mem_holes _).mpr hv.2.2)
  have he := hs (r.cell ⟨n + 1, by omega⟩) ((mem_holes _).mpr r.empty)
  have hl := r.lane ⟨n + 1, by omega⟩
  have hp1 := r.position 1
  have hpN := r.position ⟨n + 1, by omega⟩
  rw [← hp] at hp1
  simp only [Fin.val_one] at hp1 hpN
  have hz := (mem_holes _).mpr r.empty
  cases d with
  | north =>
    simp only [Adjacent] at ha
    have hsx : s.player.1.val < cut := by rw [← ha.1]; exact htx
    have hsy := hstart hsx
    have hsN := hN hsx
    omega
  | east =>
    simp only [Adjacent] at ha
    have hsx : s.player.1.val < cut := by omega
    have hsy := hstart hsx
    have hsN := hN hsx
    have hy := congrArg Fin.val ha.2
    omega
  | west =>
    simp only [Adjacent, Direction.lane, Direction.position] at ha hl hp1 hpN
    have hex : (r.cell ⟨n + 1, by omega⟩).1.val < cut := by omega
    have hey := he hex
    have hy := congrArg Fin.val ha.2
    omega
  | south =>
    simp only [Adjacent, Direction.lane, Direction.position] at ha hl hp1 hpN
    have hsx : s.player.1.val < cut := by rw [← ha.1]; exact htx
    have hsy := hstart hsx
    have hsN := hN hsx
    have hex : (r.cell ⟨n + 1, by omega⟩).1.val < cut := by omega
    have hey := he hex
    refine ⟨by omega, Finset.mem_filter.mpr ⟨hz, hex, ?_⟩⟩
    omega

/-- The frontier can grow only by spending a distinct southern hole. -/
private theorem move_budget {B : Board w h} {cap : Option ℕ} {d : Direction} {s t : State w h}
    {cut row f : ℕ} (hm : Move B cap d s t) (hs : Split cut row f s)
    (hN : North cut row s) (htN : North cut row t) :
    ∃ f', Split cut row f' t ∧ f ≤ f' ∧
      f' + (south cut row t).card ≤ f + (south cut row s).card := by
  cases hm with
  | walk _ _ _ _ hb =>
    exact ⟨f, by simpa only [Split, holes, hb] using hs, le_rfl,
      by simp only [south, holes, hb]; omega⟩
  | @push n hv hn _ r hp hb =>
    have hholes := holes_push r hn hb
    have hsubset : south cut row t ⊆ south cut row s := by
      intro q hq
      obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
      rw [hholes, Finset.mem_insert] at hq
      rcases hq with he | hq
      · have : q = t.player := he.trans hp.symm
        rw [this] at hx hy
        have := htN hx
        omega
      · exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hq, hx, hy⟩
    by_cases hstay : t.player.1.val < cut ∧ f < t.player.2.val
    · obtain ⟨hy, hz⟩ := advance_geometry r hv hp hs hN htN hstay.1 hstay.2
      refine ⟨f + 1, ?_, by omega, ?_⟩
      · intro q hq hx
        rw [hholes, Finset.mem_insert] at hq
        rcases hq with he | hq
        · left
          have he' : q = t.player := he.trans hp.symm
          rw [he', hy]
        · exact (hs q (Finset.mem_of_mem_erase hq) hx).imp (by omega) id
      · have hdest : r.cell ⟨n + 1, by omega⟩ ∉ south cut row t := by
          intro hq
          have hh := (Finset.mem_filter.mp hq).1
          exact (mem_holes _).mp hh (by rw [hb]; exact Finset.mem_insert_self _ _)
        have hsub : south cut row t ⊆ (south cut row s).erase (r.cell ⟨n + 1, by omega⟩) := by
          intro q hq
          exact Finset.mem_erase.mpr ⟨fun he => hdest (he ▸ hq), hsubset hq⟩
        have hc := Finset.card_le_card hsub
        have hd := Finset.card_erase_add_one hz
        omega
    · refine ⟨f, ?_, le_rfl, Nat.add_le_add_left (Finset.card_le_card hsubset) f⟩
      intro q hq hx
      rw [hholes, Finset.mem_insert] at hq
      rcases hq with he | hq
      · left
        have he' : q = t.player := he.trans hp.symm
        rw [he'] at hx ⊢
        omega
      · exact hs q (Finset.mem_of_mem_erase hq) hx

/-- An arbitrary real step before the first southern visit. -/
def NorthStep (B : Board w h) (cap : Option ℕ) (cut row : ℕ)
    (s t : State w h) : Prop := Step B cap s t ∧ North cut row t

theorem reachable_north {B : Board w h} {cap : Option ℕ} {s t : State w h} {cut row : ℕ}
    (hr : Relation.ReflTransGen (NorthStep B cap cut row) s t) (hs : North cut row s) :
    North cut row t := by
  cases hr with
  | refl => exact hs
  | tail _ hm => exact hm.2

/-- Southern holes cannot be created before a southern visit. -/
theorem south_subset {B : Board w h} {cap : Option ℕ} {s t : State w h} {cut row : ℕ}
    (hr : Relation.ReflTransGen (NorthStep B cap cut row) s t) :
    south cut row t ⊆ south cut row s := by
  induction hr with
  | refl => exact Finset.Subset.refl _
  | @tail u v _ hm ih =>
    intro q hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    have hne : q ≠ v.player := by
      intro he
      rw [he] at hx hy
      have := hm.2 hx
      omega
    exact ih (Finset.mem_filter.mpr
      ⟨hole_source_of_ne_player hm.1.choose_spec hne hq, hx, hy⟩)

/-- Every northern advance is bounded by the initial number of southern holes in this strip. -/
theorem reachable_budget {B : Board w h} {cap : Option ℕ} {s t : State w h} {cut row f : ℕ}
    (hr : Relation.ReflTransGen (NorthStep B cap cut row) s t)
    (hs : Split cut row f s) (hN : North cut row s) :
    ∃ f', Split cut row f' t ∧ North cut row t ∧ f ≤ f' ∧
      f' + (south cut row t).card ≤ f + (south cut row s).card := by
  induction hr with
  | refl => exact ⟨f, hs, hN, le_rfl, le_rfl⟩
  | tail _ hm ih =>
    obtain ⟨g, hg, hNg, hfg, hc⟩ := ih
    obtain ⟨g', hg', hgg', hc'⟩ := move_budget hm.1.choose_spec hg hNg hm.2
    exact ⟨g', hg', hm.2, hfg.trans hgg', hc'.trans hc⟩

end PushPuzzle.Push.StripFrontier
