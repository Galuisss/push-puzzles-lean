/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Cell
public import PushS.Source.Strip.Sweep.Scan

/-!
# Actual local emission from the strip grid

Source centers and crossing sites are scanned from their original finite lists. Every remaining
nonempty local port list selects the cup, straight, or cap of its original carrier. Instructions
use the actual unchanged frontier prefix as their wire offset.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Site`: original source/edge metadata of a local cell.
* `PushPuzzle.NCL.Strip.Sweep.classify`: the actual grid-site classifier.
* `PushPuzzle.NCL.Strip.Sweep.Instruction`: a selected fragment and its actual wire offset.
* `PushPuzzle.NCL.Strip.Sweep.instruction`: actual local instruction emission.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- Original metadata identifying the actual cell at a grid site. -/
inductive Site (V E : Type*)
  /-- One original graph vertex. -/
  | source (vertex : V)
  /-- One actual bridge/stem crossing event. -/
  | crossing (event : Event E)
  /-- One original edge at a local minimum in scan order. -/
  | cup (edge : E)
  /-- One original edge continuing through the site. -/
  | straight (edge : E)
  /-- One original edge at a local maximum in scan order. -/
  | cap (edge : E)

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- The original source vertex at a grid site, scanned from the explicit vertex list. -/
@[expose] def centerAt (vs : List V) (p : Cslib.Orthogonal.Point) : Option V :=
  vs.find? (fun v => decide (R.center v = p))

/-- Compute the actual source, crossing, or wire cell at a grid site. -/
@[expose] def classify (vs : List V) (es : List E) (p : Cslib.Orthogonal.Point) :
    Option (Site V E) :=
  match centerAt R vs p with
  | some v => some (.source v)
  | none =>
    match R.eventAt es p with
    | some c => some (.crossing c)
    | none =>
      let s := slice R es p
      match (s.incoming ++ s.outgoing).head? with
      | none => none
      | some a =>
        if s.incoming.length = 0 then some (.cup a.edge)
        else if s.outgoing.length = 0 then some (.cap a.edge)
        else some (.straight a.edge)

/-- Exact computational branch facts of the actual site classifier. -/
inductive Selection (vs : List V) (es : List E) (p : Cslib.Orthogonal.Point) :
    Option (Site V E) → Prop
  /-- The site has no selected source, crossing, or actual local port. -/
  | empty (hv : centerAt R vs p = none) (hc : R.eventAt es p = none)
      (hp : ((slice R es p).incoming ++ (slice R es p).outgoing).head? = none) :
      Selection vs es p none
  /-- The source scan selects this original vertex. -/
  | source (v : V) (hv : centerAt R vs p = some v) : Selection vs es p (some (.source v))
  /-- The crossing scan selects this actual event. -/
  | crossing (c : Event E) (hv : centerAt R vs p = none) (hc : R.eventAt es p = some c) :
      Selection vs es p (some (.crossing c))
  /-- The nonempty local port list starts on this carrier and has no inputs. -/
  | cup (a : Arc R) (hv : centerAt R vs p = none) (hc : R.eventAt es p = none)
      (hp : ((slice R es p).incoming ++ (slice R es p).outgoing).head? = some a)
      (hi : (slice R es p).incoming.length = 0) : Selection vs es p (some (.cup a.edge))
  /-- The nonempty local port list starts on this carrier and has ports on both sides. -/
  | straight (a : Arc R) (hv : centerAt R vs p = none) (hc : R.eventAt es p = none)
      (hp : ((slice R es p).incoming ++ (slice R es p).outgoing).head? = some a)
      (hi : (slice R es p).incoming.length ≠ 0) (ho : (slice R es p).outgoing.length ≠ 0) :
      Selection vs es p (some (.straight a.edge))
  /-- The nonempty local port list starts on this carrier and has no outputs. -/
  | cap (a : Arc R) (hv : centerAt R vs p = none) (hc : R.eventAt es p = none)
      (hp : ((slice R es p).incoming ++ (slice R es p).outgoing).head? = some a)
      (hi : (slice R es p).incoming.length ≠ 0) (ho : (slice R es p).outgoing.length = 0) :
      Selection vs es p (some (.cap a.edge))

/-- Every branch certificate is obtained by executing the actual finite site classifier. -/
theorem classify_spec (vs : List V) (es : List E) (p : Cslib.Orthogonal.Point) :
    Selection R vs es p (classify R vs es p) := by
  cases hv : centerAt R vs p with
  | some v => simpa only [classify, hv] using (PushPuzzle.NCL.Strip.Sweep.Selection.source (es := es) v hv)
  | none =>
    cases hc : R.eventAt es p with
    | some c => simpa only [classify, hv, hc] using (PushPuzzle.NCL.Strip.Sweep.Selection.crossing c hv hc)
    | none =>
      cases hp : ((slice R es p).incoming ++ (slice R es p).outgoing).head? with
      | none => simpa only [classify, hv, hc, hp] using (PushPuzzle.NCL.Strip.Sweep.Selection.empty hv hc hp)
      | some a =>
        by_cases hi : (slice R es p).incoming.length = 0
        · simpa only [classify, hv, hc, hp, hi, ite_true] using
            (PushPuzzle.NCL.Strip.Sweep.Selection.cup a hv hc hp hi)
        · by_cases ho : (slice R es p).outgoing.length = 0
          · simpa only [classify, hv, hc, hp, hi, ite_false, ho, ite_true] using
              (PushPuzzle.NCL.Strip.Sweep.Selection.cap a hv hc hp hi ho)
          · simpa only [classify, hv, hc, hp, hi, ho, ite_false] using
              (PushPuzzle.NCL.Strip.Sweep.Selection.straight a hv hc hp hi ho)

/-- Read the actual original weighted source slots or the original carrier colors. -/
@[expose] def Site.fragment (G : ConstraintGraph V E)
    (h3 : ∀ v, (G v).ports.length = 3) (color : E → Color) : Site V E → PushPuzzle.NCL.Strip.Sweep.Cell.Fragment
  | .source v =>
    let p := fun s : Fin 3 => (G v).ports.get (s.cast (h3 v).symm)
    PushPuzzle.NCL.Strip.Sweep.Cell.sourceColors (color (p 0).1.edge) (color (p 1).1.edge) (color (p 2).1.edge)
  | .crossing c => ⟨_, _, .cross (color c.bridge) (color c.stem)⟩
  | .cup e => ⟨_, _, .cup (color e)⟩
  | .straight e => ⟨_, _, .straight (color e)⟩
  | .cap e => ⟨_, _, .cap (color e)⟩

/-- One actual local replacement instruction. -/
structure Instruction where
  /-- Number of unchanged frontier wires above the local cell. -/
  offset : ℕ
  /-- The selected finite cell and its colored interfaces. -/
  fragment : PushPuzzle.NCL.Strip.Sweep.Cell.Fragment

/-- Emit the instruction selected by the actual grid and original graph data. -/
@[expose] def instruction (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) (p : Cslib.Orthogonal.Point) :
    Option Instruction :=
  (classify R vs es p).map (fun s => ⟨(slice R es p).above.length, s.fragment G h3 color⟩)

/-- Expand the selected standard fragment at one actual grid site, or emit the empty word. -/
@[expose] def stepWord (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) (p : Cslib.Orthogonal.Point) : Word :=
  ((instruction R G h3 color vs es p).toList).flatMap
    (fun c => c.fragment.word c.offset)

/-- Expand the actual consecutive grid scan into its selected standard planar fragments. -/
@[expose] def program (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) : Word :=
  (List.range (scanLength R es)).flatMap
    (fun (i : ℕ) => stepWord R G h3 color vs es (scanPoint K i))

/-- Every instruction in the actual emitted program consists of standard plane cells. -/
theorem program_checkPlane (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) :
    (program R G h3 color vs es).checkPlane = true := by
  unfold program stepWord Word.checkPlane
  rw [List.all_flatMap]
  apply List.all_eq_true.mpr
  intro i _
  rw [List.all_flatMap]
  apply List.all_eq_true.mpr
  intro c _
  exact c.fragment.checkPlane_word c.offset

/-- The actual center scan recovers exactly the declared vertex at its physical center. -/
theorem centerAt_eq_some (vs : List V) (p : Cslib.Orthogonal.Point) (v : V) :
    centerAt R vs p = some v ↔ v ∈ vs ∧ R.center v = p := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, of_decide_eq_true
      (List.find?_some (p := fun v => decide (R.center v = p)) h)⟩
  · rintro ⟨hv, hp⟩
    have hs : (centerAt R vs p).isSome :=
      List.find?_isSome.mpr ⟨v, hv, by simpa only [decide_eq_true_eq] using hp⟩
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
    have hwp : R.center w = p := of_decide_eq_true
      (List.find?_some (p := fun v => decide (R.center v = p)) hw)
    have hwv := R.center_injective (hwp.trans hp.symm)
    simpa only [hwv] using hw

end PushPuzzle.NCL.Strip.Sweep
