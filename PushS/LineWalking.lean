/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.FrameWalking
import all PushS.LinePush

/-! A complete line of holes supports player walks in both directions with fixed boxes. -/

public section
namespace PushPuzzle.PushS.HoleState


open PushFS

/-- Traverse a finite straight line of holes in both directions, preserving every box. -/
theorem walk_line {w h : ℕ} (s : HoleState w h) (q : Cell w h) (hq : q ∈ s.empty)
    (d : Direction) (n : ℕ) (hl : d.lane q = d.lane s.player)
    (hg : d.position q = d.position s.player + n)
    (he : ∀ r : Cell w h, d.lane r = d.lane s.player →
      d.position s.player ≤ d.position r → d.position r ≤ d.position q → r ∈ s.empty)
    (B : Board w h) (hB : B.walls = ∅) (cap : Option ℕ) :
    Reachable B cap s.toState (s.walk q hq).toState ∧
      Reachable B cap (s.walk q hq).toState s.toState := by
  cases n with
  | zero =>
    have hq' : q = s.player := d.cell_ext hl (by simpa only [Int.natCast_zero, Int.add_zero] using hg)
    subst q
    exact ⟨.refl, .refl⟩
  | succ n =>
    have hg' : d.position q = d.position s.player + n + 1 := by omega
    let cell := ray d s.player q n hl hg'
    have hc (i : Fin (n + 2)) :
        d.lane (cell i) = d.lane s.player ∧ d.position (cell i) = d.position s.player + i.val :=
      ray_coordinates d s.player q n hl hg' i
    have hstart : cell 0 = s.player := d.cell_ext (hc 0).1 (by simpa using (hc 0).2)
    have hend : cell (Fin.last (n + 1)) = q :=
      d.cell_ext ((hc _).1.trans hl.symm) (by rw [(hc _).2, hg]; rfl)
    have ha (i : Fin (n + 1)) : Adjacent d (cell i.castSucc) (cell i.succ) := by
      apply (adjacent_iff_coordinates d _ _).mpr
      exact ⟨(hc _).1.trans (hc _).1.symm, by rw [(hc _).2, (hc _).2]; simp; omega⟩
    have hh (i : Fin (n + 2)) : cell i ∈ s.empty :=
      he _ (hc i).1 (by rw [(hc i).2]; omega) (by rw [(hc i).2, hg]; have := i.isLt; omega)
    constructor
    · simpa only [walk, toState, hend] using s.walk_along B hB cap d (n + 1) cell hstart ha hh
    · have hr (i : Fin (n + 1)) :
          Adjacent d.opposite (cell i.castSucc.rev) (cell i.succ.rev) := by
        simpa only [Fin.rev_castSucc, Fin.rev_succ] using (ha i.rev).reverse
      have hb := (s.walk q hq).walk_along B hB cap d.opposite (n + 1) (fun i => cell i.rev)
        (by simpa only [Fin.rev_zero, walk] using hend) hr (fun i => hh i.rev)
      simpa only [walk, toState, Fin.rev_last, hstart] using hb

/-- A horizontal closed interval of holes supports both fixed-box player routes. -/
theorem walk_horizontal {w h : ℕ} (s : HoleState w h) (q : Cell w h) (hq : q ∈ s.empty)
    (hy : q.2 = s.player.2)
    (he : ∀ r : Cell w h, r.2 = s.player.2 →
      min s.player.1.val q.1.val ≤ r.1.val → r.1.val ≤ max s.player.1.val q.1.val → r ∈ s.empty)
    (B : Board w h) (hB : B.walls = ∅) (cap : Option ℕ) :
    Reachable B cap s.toState (s.walk q hq).toState ∧
      Reachable B cap (s.walk q hq).toState s.toState := by
  by_cases hle : s.player.1.val ≤ q.1.val
  · apply s.walk_line q hq .east (q.1.val - s.player.1.val) (congrArg Fin.val hy) (by
      change (q.1.val : ℤ) = (s.player.1.val : ℤ) + (q.1.val - s.player.1.val : ℕ)
      omega) ?_ B hB cap
    intro r hl hlo hhi
    change (s.player.1.val : ℤ) ≤ (r.1.val : ℤ) at hlo
    change (r.1.val : ℤ) ≤ (q.1.val : ℤ) at hhi
    exact he r (Fin.ext hl) (by omega) (by omega)
  · apply s.walk_line q hq .west (s.player.1.val - q.1.val) (congrArg Fin.val hy) (by
      change -(q.1.val : ℤ) = -(s.player.1.val : ℤ) + (s.player.1.val - q.1.val : ℕ)
      omega) ?_ B hB cap
    intro r hl hlo hhi
    change -(s.player.1.val : ℤ) ≤ -(r.1.val : ℤ) at hlo
    change -(r.1.val : ℤ) ≤ -(q.1.val : ℤ) at hhi
    exact he r (Fin.ext hl) (by omega) (by omega)

/-- A vertical closed interval of holes supports both fixed-box player routes. -/
theorem walk_vertical {w h : ℕ} (s : HoleState w h) (q : Cell w h) (hq : q ∈ s.empty)
    (hx : q.1 = s.player.1)
    (he : ∀ r : Cell w h, r.1 = s.player.1 →
      min s.player.2.val q.2.val ≤ r.2.val → r.2.val ≤ max s.player.2.val q.2.val → r ∈ s.empty)
    (B : Board w h) (hB : B.walls = ∅) (cap : Option ℕ) :
    Reachable B cap s.toState (s.walk q hq).toState ∧
      Reachable B cap (s.walk q hq).toState s.toState := by
  by_cases hle : s.player.2.val ≤ q.2.val
  · apply s.walk_line q hq .south (q.2.val - s.player.2.val) (congrArg Fin.val hx) (by
      change (q.2.val : ℤ) = (s.player.2.val : ℤ) + (q.2.val - s.player.2.val : ℕ)
      omega) ?_ B hB cap
    intro r hl hlo hhi
    change (s.player.2.val : ℤ) ≤ (r.2.val : ℤ) at hlo
    change (r.2.val : ℤ) ≤ (q.2.val : ℤ) at hhi
    exact he r (Fin.ext hl) (by omega) (by omega)
  · apply s.walk_line q hq .north (s.player.2.val - q.2.val) (congrArg Fin.val hx) (by
      change -(q.2.val : ℤ) = -(s.player.2.val : ℤ) + (s.player.2.val - q.2.val : ℕ)
      omega) ?_ B hB cap
    intro r hl hlo hhi
    change -(s.player.2.val : ℤ) ≤ -(r.2.val : ℤ) at hlo
    change -(r.2.val : ℤ) ≤ -(q.2.val : ℤ) at hhi
    exact he r (Fin.ext hl) (by omega) (by omega)

end PushPuzzle.PushS.HoleState
