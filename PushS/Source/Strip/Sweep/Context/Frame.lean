/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Typing
public import PushS.Source.Strip.Sweep.Created

/-!
# Actual labeled local frames of the strip sweep

Each actual classifier branch constructs its finite-cell diagram and its actual unit-arc labeling
together. The resulting frame retains its exact emitted word and outgoing creation labels.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.Frame`: a constructed local diagram with its actual labels.
* `PushPuzzle.NCL.Strip.Sweep.Context.frame`: the actual local frame computed from the original grid scan.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Transport a finite-cell diagram along equal colored boundary lists. -/
@[expose] def retype {a b a' b' : List Color} (D : Diagram Cell a b)
    (ha : a = a') (hb : b = b') : Diagram Cell a' b' :=
  Eq.mp (congrArg₂ (Diagram Cell) ha hb) D

/-- Boundary transport preserves the actual expanded word. -/
theorem retype_word {a b a' b' : List Color} (D : Diagram Cell a b)
    (ha : a = a') (hb : b = b') (k : ℕ) :
    ((retype D ha hb).subst expand).toWord Prim.interp k =
      (D.subst expand).toWord Prim.interp k := by
  cases ha
  cases hb
  rfl

end PushPuzzle.NCL.Strip.Sweep.Cell

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- An actual empty scan site leaves the entire labeled frontier unchanged. -/
theorem empty_frontier (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) :
    PushPuzzle.NCL.Strip.Sweep.frontier C.environment (List.finRange C.source.edgeCount) t =
      PushPuzzle.NCL.Strip.Sweep.frontier C.environment (List.finRange C.source.edgeCount) (t + 1) := by
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K t)
  rw [hc] at hs
  cases hs with
  | empty _ _ hh =>
    obtain ⟨hi, ho⟩ := List.append_eq_nil_iff.mp (List.head?_eq_none_iff.mp hh)
    rw [scan_before C.environment _ t, scan_after C.environment (List.nodup_finRange _) t, hi, ho]

/-- A selected cell has exactly the actual colored frontier context on both boundaries. -/
theorem cell_frontiers (t : ℤ) (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site) :
    let s := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)
    let g := site.fragment C.graph C.arity C.color
    C.frontierColors t = s.above.map (fun a => C.color a.edge) ++
        (g.inputs ++ s.below.map (fun a => C.color a.edge)) ∧
      C.frontierColors (t + 1) = s.above.map (fun a => C.color a.edge) ++
        (g.outputs ++ s.below.map (fun a => C.color a.edge)) := by
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K t)
  have hi := C.selection_interfaces (p := scanPoint K t) (s := site)
    (by simpa only [hc] using hs)
  dsimp only
  constructor
  · rw [frontierColors, scan_before C.environment _ t]
    simp only [List.map_append, ← hi.1, List.append_assoc]
  · rw [frontierColors, scan_after C.environment (List.nodup_finRange _) t]
    simp only [List.map_append, ← hi.2, List.append_assoc]

/-- An empty actual scan site emits the identity diagram on its unchanged frontier. -/
@[expose] def emptyDiagram (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) :
    Diagram Cell (C.frontierColors t) (C.frontierColors (t + 1)) :=
  PushPuzzle.NCL.Strip.Sweep.Cell.retype (Diagram.id (C.frontierColors t)) rfl
    (congrArg (List.map (fun a : Arc C.environment => C.color a.edge)) (C.empty_frontier t hc))

/-- An actual selected cell padded by its actual unchanged frontier prefix and suffix. -/
@[expose] def cellDiagram (t : ℤ)
    (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site) :
    Diagram Cell (C.frontierColors t) (C.frontierColors (t + 1)) :=
  let s := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)
  PushPuzzle.NCL.Strip.Sweep.Cell.retype (Diagram.pad (s.above.map (fun a => C.color a.edge))
      (.gen (site.fragment C.graph C.arity C.color).generator)
      (s.below.map (fun a => C.color a.edge)))
    (C.cell_frontiers t site hc).1.symm (C.cell_frontiers t site hc).2.symm

end PushPuzzle.NCL.Strip.Sweep.Context

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Diagram

/-- The actual ordered incoming/outgoing labels on one local finite-cell generator. -/
@[expose] def genLabeling {Label : Type*} {a b : List Color} (g : Cell a b)
    (x y : List Label) (hx : x.length = a.length) (hy : y.length = b.length) :
    Labeling (Diagram.gen g) x y where
  label := Sum.elim (fun i => x.get (i.cast hx.symm)) (fun j => y.get (j.cast hy.symm))
  top_eq := by
    change List.ofFn (fun i => x.get (i.cast hx.symm)) = x
    rw [List.ofFn_congr hx.symm]
    simp
  bot_eq := by
    change List.ofFn (fun i => y.get (i.cast hy.symm)) = y
    rw [List.ofFn_congr hy.symm]
    simp

/-- The actual context and local port labels on a padded finite-cell generator. -/
@[expose] def padLabeling {Label : Type*} {a b : List Color} (g : Cell a b)
    (color : Label → Color) (pre x y post : List Label)
    (hx : x.length = a.length) (hy : y.length = b.length) :
    Labeling (Diagram.pad (pre.map color) (.gen g) (post.map color))
      (pre ++ (x ++ post)) (pre ++ (y ++ post)) :=
  (Labeling.id (Γ := Cell) (pre.map color) pre (by simp)).tensor
    ((genLabeling g x y hx hy).tensor (Labeling.id (post.map color) post (by simp)))

/-- Changing equal colored interfaces preserves the actual edge labeling. -/
@[expose] def retypeLabeling {Label : Type*} {a b a' b' : List Color}
    {D : Diagram Cell a b} {x y : List Label} (L : Labeling D x y)
    (ha : a = a') (hb : b = b') : Labeling (retype D ha hb) x y := by
  cases ha
  cases hb
  exact L

/-- A local generator creates precisely its actual outgoing port labels. -/
private theorem genLabeling_created {Label : Type*} {a b : List Color} (g : Cell a b)
    (x y : List Label) (hx : x.length = a.length) (hy : y.length = b.length) :
    (PushPuzzle.NCL.Diagram.createdLabels (Diagram.gen g)) (genLabeling g x y hx hy).label = y :=
  (genLabeling g x y hx hy).bot_eq

/-- A padded local cell creates exactly its actual outgoing port labels. -/
private theorem padLabeling_created {Label : Type*} {a b : List Color} (g : Cell a b)
    (color : Label → Color) (pre x y post : List Label)
    (hx : x.length = a.length) (hy : y.length = b.length) :
    (PushPuzzle.NCL.Diagram.createdLabels (Diagram.pad (pre.map color) (.gen g) (post.map color)))
      (padLabeling g color pre x y post hx hy).label = y := by
  simp only [Diagram.pad, padLabeling]
  rw [PushPuzzle.NCL.Diagram.Labeling.createdLabels_tensor, PushPuzzle.NCL.Diagram.Labeling.createdLabels_tensor, genLabeling_created]
  simp only [createdLabels, List.nil_append, List.append_nil]

/-- Transporting equal colored boundaries retains the actual created-edge labels. -/
theorem retypeLabeling_created {Label : Type*} {a b a' b' : List Color}
    {D : Diagram Cell a b} {x y : List Label} (L : Labeling D x y)
    (ha : a = a') (hb : b = b') :
    (PushPuzzle.NCL.Diagram.createdLabels (retype D ha hb)) (retypeLabeling L ha hb).label = (PushPuzzle.NCL.Diagram.createdLabels D) L.label := by
  cases ha
  cases hb
  rfl

private theorem id_retype_created {Label : Type*} (color : Label → Color)
    (x y : List Label) (h : x = y) :
    (PushPuzzle.NCL.Diagram.createdLabels (retype (Diagram.id (x.map color)) rfl (congrArg (List.map color) h)))
      (retypeLabeling (Labeling.id (Γ := Cell) (x.map color) x (by simp)) rfl
        (congrArg (List.map color) h)).label = [] := by
  cases h
  rfl

end PushPuzzle.NCL.Strip.Sweep.Cell

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Diagram

variable {A K : ℕ} (C : Context A K)

/-- The actual unchanged frontier labels on an empty grid site. -/
@[expose] def emptyLabeling (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) :
    Labeling (C.emptyDiagram t hc) (C.frontier t) (C.frontier (t + 1)) :=
  let L := PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling
    (Labeling.id (Γ := Cell) (C.frontierColors t) (C.frontier t)
      (by simp only [frontierColors, frontier, List.length_map]))
    rfl (congrArg (List.map (fun a : Arc C.environment => C.color a.edge)) (C.empty_frontier t hc))
  { label := L.label
    top_eq := L.top_eq
    bot_eq := L.bot_eq.trans (C.empty_frontier t hc) }

/-- Actual local port labels and unchanged context on one selected original source/wire/crossing.
-/
@[expose] def cellLabeling (t : ℤ)
    (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site) :
    Labeling (C.cellDiagram t site hc) (C.frontier t) (C.frontier (t + 1)) := by
  let s := slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)
  let g := site.fragment C.graph C.arity C.color
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K t)
  have hi := C.selection_interfaces (p := scanPoint K t) (s := site)
    (by simpa only [hc] using hs)
  let L := PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling
    (PushPuzzle.NCL.Strip.Sweep.Cell.padLabeling g.generator (fun a => C.color a.edge) s.above s.incoming s.outgoing s.below
      (by rw [hi.1, List.length_map]) (by rw [hi.2, List.length_map]))
    (C.cell_frontiers t site hc).1.symm (C.cell_frontiers t site hc).2.symm
  refine { label := L.label, top_eq := ?_, bot_eq := ?_ }
  · exact L.top_eq.trans ((List.append_assoc _ _ _).symm.trans (scan_before C.environment _ t).symm)
  · exact L.bot_eq.trans ((List.append_assoc _ _ _).symm.trans
      (scan_after C.environment (List.nodup_finRange _) t).symm)

/-- An actual empty site creates no unit-arc labels. -/
theorem emptyLabeling_created (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) :
    (PushPuzzle.NCL.Diagram.createdLabels (C.emptyDiagram t hc)) (C.emptyLabeling t hc).label = [] := by
  simpa only [emptyDiagram, emptyLabeling, frontierColors, frontier] using
    Cell.id_retype_created (fun a : Arc C.environment => C.color a.edge)
      (C.frontier t) (C.frontier (t + 1)) (C.empty_frontier t hc)

/-- An actual selected site creates precisely its actual outgoing unit-arc labels. -/
theorem cellLabeling_created (t : ℤ)
    (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site) :
    (PushPuzzle.NCL.Diagram.createdLabels (C.cellDiagram t site hc)) (C.cellLabeling t site hc).label =
      (slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)).outgoing := by
  simp only [cellDiagram, cellLabeling, PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_created,
    PushPuzzle.NCL.Strip.Sweep.Cell.padLabeling_created]

/-- The actual empty site emits the empty local standard word. -/
theorem emptyDiagram_word (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) :
    ((C.emptyDiagram t hc).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 =
      stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K t) := by
  simp only [stepWord, instruction, hc, Option.map_none, Option.toList_none, List.flatMap_nil]
  exact PushPuzzle.NCL.Strip.Sweep.Cell.retype_word (Diagram.id (C.frontierColors t)) rfl
    (congrArg (List.map (fun a : Arc C.environment => C.color a.edge)) (C.empty_frontier t hc)) 0

/-- The actual padded selected cell emits its exact local standard word. -/
theorem cellDiagram_word (t : ℤ)
    (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site) :
    ((C.cellDiagram t site hc).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 =
      stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K t) := by
  simp only [cellDiagram, PushPuzzle.NCL.Strip.Sweep.Cell.retype_word]
  simp only [Diagram.pad, Diagram.subst, Diagram.toWord, List.nil_append, List.append_nil,
    Nat.zero_add, List.length_map]
  simp only [stepWord, instruction, hc, Option.map_some, Option.toList_some, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, PushPuzzle.NCL.Strip.Sweep.Cell.Fragment.word]

private theorem empty_outgoing (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) :
    (slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)).outgoing = [] := by
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) (scanPoint K t)
  rw [hc] at hs
  cases hs with
  | empty _ _ hh => exact (List.append_eq_nil_iff.mp (List.head?_eq_none_iff.mp hh)).2

/-- A computed local frame, with its actual diagram and actual unit-arc labels kept together. -/
structure Frame (t : ℤ) where
  /-- The actual padded finite-cell diagram. -/
  diagram : Diagram Cell (C.frontierColors t) (C.frontierColors (t + 1))
  /-- The actual unit arcs at both consecutive frontiers. -/
  labeling : Labeling diagram (C.frontier t) (C.frontier (t + 1))
  /-- The expanded diagram is the actual selected local emitted word. -/
  word_eq : (diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 =
    stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t)
  /-- Precisely the actual outgoing unit-arc labels are created. -/
  created_eq : (PushPuzzle.NCL.Diagram.createdLabels diagram) labeling.label =
    (slice C.environment (List.finRange C.source.edgeCount) (scanPoint K t)).outgoing

/-- The computed frame of an actually empty grid site. -/
@[expose] def emptyFrame (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none) : C.Frame t :=
    { diagram := C.emptyDiagram t hc
      labeling := C.emptyLabeling t hc
      word_eq := C.emptyDiagram_word t hc
      created_eq := by exact (C.emptyLabeling_created t hc).trans (C.empty_outgoing t hc).symm }

/-- The computed frame of an actually selected grid cell. -/
@[expose] def cellFrame (t : ℤ) (site : Site (Fin C.vertices.length) (Fin C.source.edgeCount))
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = some site) : C.Frame t :=
    { diagram := C.cellDiagram t site hc
      labeling := C.cellLabeling t site hc
      word_eq := C.cellDiagram_word t site hc
      created_eq := C.cellLabeling_created t site hc }

/-- Construct the actual diagram, labels, and checked local invariants of the computed grid cell. -/
@[expose] def frame (t : ℤ) : C.Frame t :=
  match hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) with
  | none => C.emptyFrame t hc
  | some site => C.cellFrame t site hc

/-- A property of the actual computed frame follows from its two executed classifier branches. -/
theorem frame_cases (t : ℤ) (P : C.Frame t → Prop)
    (he : ∀ hc, P (C.emptyFrame t hc))
    (hg : ∀ site hc, P (C.cellFrame t site hc)) : P (C.frame t) := by
  unfold frame
  split
  · exact he _
  · exact hg _ _

end PushPuzzle.NCL.Strip.Sweep.Context
