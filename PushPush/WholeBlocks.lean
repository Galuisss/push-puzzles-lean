/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeNormalize
public import Push.AcceptanceProgramRounds
public import Push.ScanLaneProjection
public import PushPush.ReadScan
import all PushPush.ReadScan
import all Push.Scan
import all Push.ScanNormalize

/-! A complete parallel whole-run round, with its exact retained bitmap. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell Direction Adjacent)
open Push.AcceptanceProgram

variable {w h : ℕ}

/-- A round groups all sparse same-direction requests into one lower bound per lane. -/
abbrev Block (side : Direction) (requests : List (ℕ × ℕ))
    (E F : Finset (Cell w h)) : Prop :=
  WholeScan.LooseExec
    (Push.Scan.lines side (Push.Scan.ofQuotas (Push.Scan.denseQuotas side w h requests))) E F

/-- Physical parallel rounds; all extra consumption stays inside the round's whole-run cuts. -/
inductive Exec : List Round → Finset (Cell w h) → Finset (Cell w h) → Prop
  | nil (E) : Exec [] E E
  | cons {side requests rounds E F G} (head : Block side requests E F)
      (tail : Exec rounds F G) : Exec (.read side requests :: rounds) E G

/-- The simultaneous source inventory conditions of a complete parallel round. -/
structure Block.Characterization (side : Direction) (requests : List (ℕ × ℕ))
    (E F : Finset (Cell w h)) : Prop where
  subset : F ⊆ E
  front : ∀ p ∈ E \ F, ∀ q ∈ F, side.lane q = side.lane p → side.position q < side.position p
  no_split : WholeScan.NoSplit side E F
  paid : ∀ lane < Push.Scan.laneCount side w h, Push.Scan.quotaAt requests lane ≤
    ((E.filter fun p => side.lane p = lane) \ (F.filter fun p => side.lane p = lane)).card

end PushPuzzle.PushPush.WholeBlocks
