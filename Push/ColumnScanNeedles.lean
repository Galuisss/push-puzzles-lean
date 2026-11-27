/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanEntry
public import Push.FirstExit

/-! The original needles survive until first visited: a successful leftward traversal cannot borrow a western needle. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

private theorem narrow_north {w h a b row : ℕ} (hab : a ≤ b) {s : State w h}
    (hs : North b row s) : North a row s := fun hx => hs (hx.trans_le hab)

private theorem narrow_prefix {w h a b row : ℕ} {B : Board w h} {cap : Option ℕ}
    {s t : State w h} (hab : a ≤ b)
    (hr : Relation.ReflTransGen (NorthStep B cap b row) s t) :
    Relation.ReflTransGen (NorthStep B cap a row) s t :=
  Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm.1, narrow_north hab hm.2⟩) _ _ hr

/-- Every first southern strip entrance on a successful traversal walks into that strip's own needle. -/
theorem first_south_walk {cut : ℕ} (hcut : cut ≤ r.width)
    {s t finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none cut r.targetLevel)
      r.initialState.toState s) (hm : Step r.compile.board none s t)
    (hx : t.player.1.val < cut) (hy : r.targetLevel ≤ t.player.2.val)
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    ∃ i : Fin r.width, i.val + 1 = cut ∧ r.needle i = t.player ∧ t.boxes = s.boxes := by
  induction cut using Nat.strong_induction_on generalizing s t with
  | ind cut ih =>
    rcases r.first_south_needle hcut hr hm hx hy with hwalk | ⟨i, hi, hbefore, hafter⟩
    · exact hwalk
    · have hmcut : i.val + 1 ≤ r.width := by omega
      have hmNorth : North (i.val + 1) r.targetLevel t := by
        obtain ⟨_, _, htx⟩ := r.first_south_direction hcut hr hm.choose_spec hx hy
        intro htx'
        omega
      have hfSouth : ¬North (i.val + 1) r.targetLevel finish := by
        intro h
        have := h (by omega)
        omega
      obtain ⟨u, v, htu, hu, huv, hv, hvf⟩ := Path.first_exit
        (α := State r.outputWidth r.outputHeight) htf hmNorth hfSouth
      have hsmall : Relation.ReflTransGen
          (NorthStep r.compile.board none (i.val + 1) r.targetLevel) r.initialState.toState u :=
        ((narrow_prefix (by omega) hr).tail ⟨hm, hmNorth⟩).trans htu
      have hvSouth : v.player.1.val < i.val + 1 ∧ r.targetLevel ≤ v.player.2.val := by
        by_contra h
        apply hv
        intro hvx
        omega
      obtain ⟨j, hj, hp, hb⟩ := ih (i.val + 1) hi hmcut hsmall huv hvSouth.1 hvSouth.2 hvf
      have hij : i = j := Fin.ext (by omega)
      have hpin : r.needle i ∈ holes u := by
        rw [hij, hp, mem_holes, ← hb]
        exact huv.valid_target.2.2
      have hpinSouth : r.needle i ∈ south (i.val + 1) r.targetLevel u :=
        Finset.mem_filter.mpr ⟨hpin, by change i.val < i.val + 1; omega,
          r.targetLevel_le_needleLevel i⟩
      exact False.elim (hafter ((Finset.mem_filter.mp (south_subset htu hpinSouth)).1))

/-- Each needle is retained until the first southern visit to its own western strip. -/
private theorem before_south_needle (i : Fin r.width)
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none (i.val + 1) r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    r.needle i ∈ holes s := by
  have hsN := reachable_north hr (r.initial_north (i.val + 1))
  have hfSouth : ¬North (i.val + 1) r.targetLevel finish := by
    intro h
    have := h (by omega)
    omega
  obtain ⟨u, v, hsu, hu, huv, hv, hvf⟩ := Path.first_exit
    (α := State r.outputWidth r.outputHeight) hsf hsN hfSouth
  have hvSouth : v.player.1.val < i.val + 1 ∧ r.targetLevel ≤ v.player.2.val := by
    by_contra h
    apply hv
    intro hvx
    omega
  obtain ⟨j, hj, hp, hb⟩ := r.first_south_walk (by have := i.isLt; omega)
    (hr.trans hsu) huv hvSouth.1 hvSouth.2 hvf hfx hfy
  have hij : i = j := Fin.ext (by omega)
  have hpin : r.needle i ∈ holes u := by
    rw [hij, hp, mem_holes, ← hb]
    exact huv.valid_target.2.2
  have hpinSouth : r.needle i ∈ south (i.val + 1) r.targetLevel u :=
    Finset.mem_filter.mpr ⟨hpin, by change i.val < i.val + 1; omega,
      r.targetLevel_le_needleLevel i⟩
  exact (Finset.mem_filter.mp (south_subset hsu hpinSouth)).1

/-- Before any southern source visit, every original needle is still a hole. -/
theorem before_south_all_needles
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    ∀ i : Fin r.width, r.needle i ∈ holes s := by
  intro i
  exact r.before_south_needle i (narrow_prefix (by have := i.isLt; omega) hr) hsf hfx hfy

/-- Southern hole inventory is unchanged before the first southern source visit. -/
private theorem before_south_cut_inventory {cut : ℕ} (hcut : cut ≤ r.width)
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none cut r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    south cut r.targetLevel s = south cut r.targetLevel r.initialState.toState := by
  apply Finset.Subset.antisymm (south_subset hr)
  intro q hq
  obtain ⟨i, hi, rfl⟩ := (r.mem_south_initial hcut q).mp hq
  have hpin := r.before_south_needle i (narrow_prefix (by omega) hr) hsf hfx hfy
  exact Finset.mem_filter.mpr ⟨hpin, hi, r.targetLevel_le_needleLevel i⟩

/-- Before the first southern visit, the buffer beneath the source contains only its original needles. -/
theorem before_south_cut_exact {cut : ℕ} (hcut : cut ≤ r.width)
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none cut r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    {q : Cell r.outputWidth r.outputHeight} (hx : q.1.val < cut)
    (hy : r.height ≤ q.2.val) : q ∈ holes s ↔ ∃ i : Fin r.width, r.needle i = q := by
  constructor
  · intro hq
    obtain ⟨f, hs, _, _, hb⟩ := reachable_budget (w := r.outputWidth) (h := r.outputHeight)
      hr (r.initial_split hcut) (r.initial_north cut)
    rw [r.before_south_cut_inventory hcut hr hsf hfx hfy, r.south_initial_card hcut] at hb
    have hySouth : r.targetLevel ≤ q.2.val := by
      have hs' := hs q hq hx
      have := r.height_pos
      omega
    have hqInit := south_subset hr (Finset.mem_filter.mpr ⟨hq, hx, hySouth⟩)
    obtain ⟨i, _, hi⟩ := (r.mem_south_initial hcut q).mp hqInit
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact r.before_south_needle i (narrow_prefix (by exact hx) hr) hsf hfx hfy

theorem before_south_exact
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    {q : Cell r.outputWidth r.outputHeight} (hx : q.1.val < r.width)
    (hy : r.height ≤ q.2.val) : q ∈ holes s ↔ ∃ i : Fin r.width, r.needle i = q :=
  r.before_south_cut_exact le_rfl hr hsf hfx hfy hx hy

/-- The first westward needle entrance is made from the real committed seal landing. -/
theorem first_south_landing {s t finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hm : Step r.compile.board none s t)
    (htSouth : t.player.1.val < r.width ∧ r.targetLevel ≤ t.player.2.val)
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    s.player = r.landing := by
  obtain ⟨i, hi, hp, hb⟩ := r.first_south_walk le_rfl hpre hm htSouth.1 htSouth.2 htf hfx hfy
  obtain ⟨hd, hsx, _⟩ := r.first_south_direction le_rfl hpre hm.choose_spec htSouth.1 htSouth.2
  have ha := players_adjacent hm.choose_spec
  rw [hd] at ha
  have hilast : i = ⟨r.width - 1, by have := r.width_pos; omega⟩ := by
    apply Fin.ext
    change i.val = r.width - 1
    omega
  have hty : t.player.2.val = r.firstLevel := by
    rw [← hp]
    change r.needleLevel i = r.firstLevel
    rw [hilast, r.needleLevel_rightmost]
  apply Prod.ext <;> apply Fin.ext
  · exact hsx
  · have hay := congrArg Fin.val ha.2
    change s.player.2.val = r.firstLevel
    omega

/-- Every successful traversal reaches the seal landing before visiting any southern source column. -/
theorem exists_landing_prefix {finish : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.board none r.initialState.toState finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    ∃ s : State r.outputWidth r.outputHeight,
      Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
        r.initialState.toState s ∧ s.player = r.landing ∧
      Reachable r.compile.board none s finish := by
  have hfSouth : ¬North r.width r.targetLevel finish := by
    intro h
    have := h (by have := r.width_pos; omega)
    omega
  obtain ⟨s, t, hpre, hs, hm, ht, htf⟩ := Path.first_exit
    (α := State r.outputWidth r.outputHeight) hr (r.initial_north r.width) hfSouth
  have htSouth : t.player.1.val < r.width ∧ r.targetLevel ≤ t.player.2.val := by
    by_contra h
    apply ht
    intro htx
    omega
  exact ⟨s, hpre, r.first_south_landing hpre hm htSouth htf hfx hfy,
    (Relation.ReflTransGen.single hm).trans htf⟩

end PushPuzzle.Push.ColumnScan.Input
