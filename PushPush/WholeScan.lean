/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Scan
import all Push.Scan

/-! Whole-component destructive scans and exact full-budget payment. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction Adjacent)

variable {w h : ℕ}

/-- One exact read whose final cut does not divide a consecutive hole run. -/
structure Read (side : Direction) (lane quota : ℕ) (E F : Finset (Cell w h)) : Prop where
  eval : (Push.Scan.Instruction.read side lane quota).eval E = some F
  no_split : ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent side.opposite p q

theorem Read.card {side : Direction} {lane quota : ℕ} {E F : Finset (Cell w h)}
    (H : Read side lane quota E F) : F.card + quota = E.card :=
  Push.Scan.consume_card H.eval

theorem Read.subset {side : Direction} {lane quota : ℕ} {E F : Finset (Cell w h)}
    (H : Read side lane quota E F) : F ⊆ E := Push.Scan.consume_subset H.eval

/-- A static program executed with complete hole components at every cut. -/
inductive Exec : List (Push.Scan.Instruction w h) → Finset (Cell w h) → Finset (Cell w h) → Prop
  | nil (E) : Exec [] E E
  | cons {side lane quota program E F G} (head : Read side lane quota E F)
      (tail : Exec program F G) : Exec (.read side lane quota :: program) E G

theorem Exec.eval {program : List (Push.Scan.Instruction w h)} {E F : Finset (Cell w h)}
    (H : Exec program E F) : Push.Scan.eval program E = some F := by
  induction H with
  | nil => rfl
  | cons head _ ih => simp only [Push.Scan.eval, head.eval, Option.bind_some, ih]

theorem Exec.append {first second : List (Push.Scan.Instruction w h)} {E F G : Finset (Cell w h)}
    (hEF : Exec first E F) (hFG : Exec second F G) : Exec (first ++ second) E G := by
  induction hEF with
  | nil => exact hFG
  | cons h _ ih => exact .cons h (ih hFG)

theorem Exec.append_iff (first second : List (Push.Scan.Instruction w h)) (E G : Finset (Cell w h)) :
    Exec (first ++ second) E G ↔ ∃ F, Exec first E F ∧ Exec second F G := by
  constructor
  · intro H
    induction first generalizing E with
    | nil => exact ⟨E, .nil _, H⟩
    | cons instruction first ih =>
      cases H with
      | cons head tail =>
        obtain ⟨F, hfirst, hsecond⟩ := ih _ tail
        exact ⟨F, .cons head hfirst, hsecond⟩
  · rintro ⟨F, hfirst, hsecond⟩
    exact hfirst.append hsecond

/-- A physical round may consume extra complete hole runs beyond a lower-bound quota. -/
inductive LooseExec : List (Push.Scan.Instruction w h) → Finset (Cell w h) → Finset (Cell w h) → Prop
  | nil (E) : LooseExec [] E E
  | cons {side lane quota actual program E F G} (paid : quota ≤ actual)
      (head : Read side lane actual E F) (tail : LooseExec program F G) :
      LooseExec (.read side lane quota :: program) E G

theorem LooseExec.budget_bound {program : List (Push.Scan.Instruction w h)} {E F : Finset (Cell w h)}
    (H : LooseExec program E F) : F.card + Push.Scan.quota program ≤ E.card := by
  induction H with
  | nil => simp [Push.Scan.quota]
  | @cons side lane quota actual program E F G paid head _ ih =>
    have hc := head.card
    change G.card + (quota + Push.Scan.quota program) ≤ E.card
    omega

theorem LooseExec.subset {program : List (Push.Scan.Instruction w h)} {E F : Finset (Cell w h)}
    (H : LooseExec program E F) : F ⊆ E := by
  induction H with
  | nil => exact Finset.Subset.refl _
  | cons _ head _ ih => exact ih.trans head.subset

theorem LooseExec.append {first second : List (Push.Scan.Instruction w h)}
    {E F G : Finset (Cell w h)} (hEF : LooseExec first E F) (hFG : LooseExec second F G) :
    LooseExec (first ++ second) E G := by
  induction hEF with
  | nil => exact hFG
  | cons paid head _ ih => exact .cons paid head (ih hFG)

theorem LooseExec.append_iff (first second : List (Push.Scan.Instruction w h))
    (E G : Finset (Cell w h)) :
    LooseExec (first ++ second) E G ↔ ∃ F, LooseExec first E F ∧ LooseExec second F G := by
  constructor
  · intro H
    induction first generalizing E with
    | nil => exact ⟨E, .nil _, H⟩
    | cons instruction first ih =>
      cases H with
      | cons paid head tail =>
        obtain ⟨F, hfirst, hsecond⟩ := ih _ tail
        exact ⟨F, .cons paid head hfirst, hsecond⟩
  · rintro ⟨F, hfirst, hsecond⟩
    exact hfirst.append hsecond

end PushPuzzle.PushPush.WholeScan
