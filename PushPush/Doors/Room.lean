/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide

/-! The six-slot room implements one directed symmetric self-closing door. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Room

/-- The six horizontal input slots, in vertical order. -/
inductive Slot
  | low | a | checkA | checkB | b | high
  deriving DecidableEq

/-- Local row measured from the room's northern divider. -/
def Slot.row : Slot → ℕ
  | .low => 10
  | .a => 30
  | .checkA => 40
  | .checkB => 50
  | .b => 60
  | .high => 80

/-- The stored location for a stable door value. -/
def stable (bit : Bool) : Slot := if bit then .b else .a

/-- The incoming slot for a requested directed traversal. -/
def check (bit : Bool) : Slot := if bit then .checkB else .checkA

/-- A signal entering a slot, or leaving the room through a completed channel. -/
inductive Node
  | call (stored incoming : Slot)
  | exit (channel : Bool) (stored : Slot)
  deriving DecidableEq

/-- Slide one of two separated boxes towards the other; its landing row is adjacent
to the stationary box, on the side from which it approached. -/
def landing (moving stationary : Slot) : ℕ :=
  if moving.row < stationary.row then stationary.row - 1 else stationary.row + 1

/-- Wiring at each permitted output row. Every other row is a dead output. -/
def route (stored : Slot) (row : ℕ) : Option Node :=
  if row = 11 then some (.call stored .a)
  else if row = 29 then some (.exit true stored)
  else if row = 39 then some (.call stored .high)
  else if row = 51 then some (.call stored .low)
  else if row = 61 then some (.exit false stored)
  else if row = 79 then some (.call stored .b)
  else none

/-- Choose which of the two boxes remains at its input slot. -/
def advance (stored incoming : Slot) (keepIncoming : Bool) : Option Node :=
  if keepIncoming then route incoming (landing stored incoming)
  else route stored (landing incoming stored)

/-- A room interaction followed by its output wire. -/
def Step : Node → Node → Prop
  | .call stored incoming, next =>
      stored ≠ incoming ∧ ∃ keepIncoming : Bool, advance stored incoming keepIncoming = some next
  | .exit _ _, _ => False

instance (s t : Node) : Decidable (Step s t) := by
  cases s <;> unfold Step <;> infer_instance

/-- Internal interactions and permitted output wires, including final-step retries. -/
abbrev Reachable := Relation.ReflTransGen Step

private def allowed (old channel : Bool) (node : Node) : Prop :=
  node = .call (stable old) (check channel) ∨ old = channel ∧
    if channel then
      node = .call .checkB .low ∨ node = .call .low .a ∨ node = .exit true .a
    else
      node = .call .checkA .high ∨ node = .call .high .b ∨ node = .exit false .b

private instance (old channel : Bool) (node : Node) : Decidable (allowed old channel node) := by
  unfold allowed
  infer_instance

private theorem allowed_step :
    ∀ old channel s t, allowed old channel s → Step s t → allowed old channel t := by
  intro old channel s t ha hs
  cases old <;> cases channel
  · simp [allowed, stable, check] at ha
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp_all [allowed, stable, check, Step, advance, route, landing, Slot.row,
        Bool.exists_bool]
    rcases hs with rfl | rfl <;> simp
  · simp [allowed, stable, check] at ha
    subst s
    simp [Step, advance, route, landing, Slot.row] at hs
  · simp [allowed, stable, check] at ha
    subst s
    simp [Step, advance, route, landing, Slot.row] at hs
  · simp [allowed, stable, check] at ha
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp_all [allowed, stable, check, Step, advance, route, landing, Slot.row,
        Bool.exists_bool]
    rcases hs with rfl | rfl <;> simp

private theorem reachable_allowed (old channel : Bool) {node : Node}
    (hr : Reachable (.call (stable old) (check channel)) node) : allowed old channel node := by
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ hs ih => exact allowed_step old channel _ _ ih hs

private theorem forward_zero : Reachable (.call .a .checkA) (.exit false .b) := by
  have first : Step (.call .a .checkA) (.call .checkA .high) := by decide
  have second : Step (.call .checkA .high) (.call .high .b) := by decide
  have third : Step (.call .high .b) (.exit false .b) := by decide
  exact ((Relation.ReflTransGen.single first).tail second).tail third

private theorem forward_one : Reachable (.call .b .checkB) (.exit true .a) := by
  have first : Step (.call .b .checkB) (.call .checkB .low) := by decide
  have second : Step (.call .checkB .low) (.call .low .a) := by decide
  have third : Step (.call .low .a) (.exit true .a) := by decide
  exact ((Relation.ReflTransGen.single first).tail second).tail third

/-- A completed interaction uses exactly the enabled directed channel and flips the value. -/
theorem reachable_exit_iff (old channel out : Bool) (stored : Slot) :
    Reachable (.call (stable old) (check channel)) (.exit out stored) ↔
      old = channel ∧ out = channel ∧ stored = stable (!channel) := by
  constructor
  · intro hr
    have ha := reachable_allowed old channel hr
    cases old <;> cases channel <;> cases out <;> cases stored <;>
      simp_all [allowed, stable, check]
  · rintro ⟨rfl, rfl, rfl⟩
    cases out
    · exact forward_zero
    · exact forward_one

/-- Every permitted entry and retry keeps the two boxes in distinct slots. -/
theorem reachable_call_distinct (old channel : Bool) (stored incoming : Slot)
    (hr : Reachable (.call (stable old) (check channel)) (.call stored incoming)) :
    stored ≠ incoming := by
  have ha := reachable_allowed old channel hr
  cases old <;> cases channel <;> cases stored <;> cases incoming <;>
    simp_all [allowed, stable, check]

theorem reachable_call_checkA_channel (old channel : Bool) (stored incoming : Slot)
    (hr : Reachable (.call (stable old) (check channel)) (.call stored incoming))
    (hcheck : stored = .checkA ∨ incoming = .checkA) : channel = false := by
  have ha := reachable_allowed old channel hr
  cases old <;> cases channel <;> cases stored <;> cases incoming <;>
    simp_all [allowed, stable, check]

theorem reachable_call_checkB_channel (old channel : Bool) (stored incoming : Slot)
    (hr : Reachable (.call (stable old) (check channel)) (.call stored incoming))
    (hcheck : stored = .checkB ∨ incoming = .checkB) : channel = true := by
  have ha := reachable_allowed old channel hr
  cases old <;> cases channel <;> cases stored <;> cases incoming <;>
    simp_all [allowed, stable, check]

/-- Slot coordinates are separated by at least ten rows. -/
theorem slot_separation (s t : Slot) (hne : s ≠ t) :
    s.row + 10 ≤ t.row ∨ t.row + 10 ≤ s.row := by
  cases s <;> cases t <;> simp_all [Slot.row]

theorem slot_row_bounds (s : Slot) : 10 ≤ s.row ∧ s.row ≤ 80 := by
  cases s <;> decide

/-- A room interaction preserves one slot and leaves the departing box beside it. -/
theorem landing_adjacent (s t : Slot) :
    landing s t + 1 = t.row ∨ landing s t = t.row + 1 := by
  cases s <;> cases t <;> simp [landing, Slot.row]

end PushPuzzle.PushPush.Doors.Room
