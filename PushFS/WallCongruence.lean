/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Components

/-! Changing storage targets preserves every actual walk and push on the fixed wall board. -/

@[expose] public section
namespace PushPuzzle.PushFS


variable {w h : ℕ} {B B' : Board w h}

private theorem Displacement.reboard {p q : Cell w h} (hd : Displacement B p q)
    (hw : B.walls=B'.walls) :
    Displacement B' p q := by simpa only [Displacement,hw] using hd

private theorem StaticReach.reboard {p q : Cell w h} (hr : StaticReach B p q)
    (hw : B.walls=B'.walls) :
    StaticReach B' p q := by
  induction hr with
  | refl=>exact .refl
  | tail _ hs ih=>exact ih.tail (hs.reboard hw)

theorem SameComponent.reboard {p q : Cell w h} (hc : SameComponent B p q) (hw : B.walls=B'.walls) :
    SameComponent B' p q := ⟨hc.1.reboard hw,hc.2.reboard hw⟩

private theorem State.valid_walls_congr (hw : B.walls=B'.walls) (s : State w h) :
    s.Valid B ↔s.Valid B' := by
  simp only [State.Valid,hw]

private def Run.reboard {d : Direction} {s : State w h} {n : ℕ}
    (r : Run B d s n) (hw : B.walls=B'.walls) : Run B' d s n where
  cell:=r.cell
  start:=r.start
  adjacent:=r.adjacent
  occupied:=r.occupied
  empty:=r.empty
  floor i:=hw ▸r.floor i

private theorem Move.reboard {cap : Option ℕ} {d : Direction} {s t : State w h}
    (hm : Move B cap d s t) (hw : B.walls=B'.walls) : Move B' cap d s t := by
  cases hm with
  | walk hv ha hf he hb =>
    exact .walk ((s.valid_walls_congr hw).mp hv) ha (hw ▸hf) he hb
  | push hv hn hc run hp hb =>
    exact .push ((s.valid_walls_congr hw).mp hv) hn hc (run.reboard hw) hp hb

theorem Reachable.reboard {cap : Option ℕ} {s t : State w h}
    (hr : Reachable B cap s t) (hw : B.walls=B'.walls) : Reachable B' cap s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨hs.choose,hs.choose_spec.reboard hw⟩

end PushPuzzle.PushFS
