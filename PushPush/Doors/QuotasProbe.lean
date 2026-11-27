/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasWhole
public import PushPush.Doors.CompilerBounds

/-! A four- or five-hole whole-run probe forces its stopping box. -/

public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction Adjacent)
open Push.AcceptanceProgram

variable {w h quota lane cutoff : ℕ} {E F : Finset (Cell w h)}

/-- With the outer frame removed, a positive east probe cannot stop inside a longer hole run. -/
private theorem east_probe_blocked (hw : w = cutoff + quota + 2) (hq : 0 < quota)
    (hr : (Push.Scan.Instruction.read .east lane quota).eval E = some F)
    (hwhole : ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent .west p q)
    (hborder : ∀ p : Cell w h, p.2.val = lane → p.1.val + 1 = w → p ∉ E)
    (houter : ∀ p : Cell w h, p.2.val = lane → cutoff < p.1.val → p.1.val + 1 < w → p ∈ E)
    (p : Cell w h) (hlane : p.2.val = lane) (hx : p.1.val = cutoff) : p ∉ E := by
  intro hp
  let cells : Fin (quota + 1) → Cell w h := fun i =>
    (⟨w - 2 - i.val, by have hi := i.isLt; omega⟩, p.2)
  have hempty : ∀ i, cells i ∈ E := by
    intro i
    have hi := i.isLt
    by_cases he : i.val = quota
    · have hp' : cells i = p := by
        apply Prod.ext <;> apply Fin.ext
        · dsimp [cells]
          omega
        · rfl
      exact hp' ▸ hp
    · apply houter (cells i) hlane
      · dsimp [cells]
        omega
      · dsimp [cells]
        omega
  have hadj : ∀ i : Fin quota, Adjacent .west (cells i.castSucc) (cells i.succ) := by
    intro i
    have hi := i.isLt
    constructor
    · dsimp [cells]
      omega
    · rfl
  have hfirst : ∀ q ∈ E, Direction.east.lane q = lane →
      prefixRank .east (cells 0) ≤ prefixRank .east q := by
    intro q hq' hl
    have hqb : q.1.val + 1 ≠ w := fun hb => hborder q hl hb hq'
    have hqbound := q.1.isLt
    dsimp [cells]
    simp only [prefixRank]
    omega
  have he := whole_read_chain hr hq hwhole cells hempty (fun _ => hlane) hadj hfirst
  omega

namespace Source

/-- The rack probe pays four original holes and therefore forces the rack cell to be occupied. -/
theorem rack_probe_blocked (I : Instance) {lane : ℕ}
    {E F : Finset (Cell (layout false I).width (layout false I).height)}
    (hr : (Push.Scan.Instruction.read .east lane 4).eval E = some F)
    (hwhole : ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent .west p q)
    (hborder : ∀ p : Cell (layout false I).width (layout false I).height,
      p.2.val = lane → p.1.val + 1 = (layout false I).width → p ∉ E)
    (houter : ∀ p : Cell (layout false I).width (layout false I).height,
      p.2.val = lane → (layout false I).rackX < p.1.val →
      p.1.val + 1 < (layout false I).width → p ∈ E)
    (p : Cell (layout false I).width (layout false I).height)
    (hl : p.2.val = lane) (hx : p.1.val = (layout false I).rackX) : p ∉ E :=
  east_probe_blocked rfl (by omega) hr hwhole hborder houter p hl hx

/-- The five-hole divider/cap/parking probe forces its working-column stopping box. -/
theorem marker_probe_blocked (I : Instance) {lane : ℕ}
    {E F : Finset (Cell (layout false I).width (layout false I).height)}
    (hr : (Push.Scan.Instruction.read .east lane 5).eval E = some F)
    (hwhole : ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent .west p q)
    (hborder : ∀ p : Cell (layout false I).width (layout false I).height,
      p.2.val = lane → p.1.val + 1 = (layout false I).width → p ∉ E)
    (houter : ∀ p : Cell (layout false I).width (layout false I).height,
      p.2.val = lane → (layout false I).rackX - 1 < p.1.val →
      p.1.val + 1 < (layout false I).width → p ∈ E)
    (p : Cell (layout false I).width (layout false I).height)
    (hl : p.2.val = lane) (hx : p.1.val = (layout false I).rackX - 1) : p ∉ E := by
  apply east_probe_blocked (quota := 5) (cutoff := (layout false I).rackX - 1) ?_
    (by omega) hr hwhole hborder houter p hl hx
  unfold Layout.width Layout.rackX
  omega

end Source
end PushPuzzle.PushPush.Doors
