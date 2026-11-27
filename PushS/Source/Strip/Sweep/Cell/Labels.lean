/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Frame

/-!
# Weighted ports under actual local cell labels

Reading a threshold cell through its actual incoming/outgoing labels gives the corresponding
weighted vertex, in incoming-then-outgoing order.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Cell.genVertex_labels`: the actual labeled weighted vertex of a local generator.
* `PushPuzzle.NCL.Strip.Sweep.Cell.retypeLabeling_legal`: boundary transport retains labeled legality.
* `PushPuzzle.NCL.Strip.Sweep.Cell.padLabeling_legal`: unchanged context contributes no vertex constraints.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Reading a threshold vertex through the actual port labels retains their colors and directions.
-/
theorem genVertex_labels {Label : Type*} {a b : List Color} (g : Cell a b)
    (color : Label → Color) (x y : List Label)
    (hx : x.length = a.length) (hy : y.length = b.length)
    (ha : a = x.map color) (hb : b = y.map color) (n : ℕ) :
    (genVertex a b n).map (genLabeling g x y hx hy).label =
      ⟨x.map (fun q => ⟨⟨q, true⟩, (color q).weight⟩) ++
        y.map (fun q => ⟨⟨q, false⟩, (color q).weight⟩), n⟩ := by
  change (genVertex a b n).map
    (Sum.elim (fun i => x.get (i.cast hx.symm)) (fun j => y.get (j.cast hy.symm))) = _
  subst a
  subst b
  simp only [genVertex, Vertex.map]
  congr 1
  rw [List.map_append]
  simp only [List.map_map]
  apply congrArg₂ (· ++ ·)
  · rw [← List.ofFn_eq_map, List.ofFn_congr hx.symm]
    simpa [WeightedPort.map, Port.map, List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map x (fun q => (⟨⟨q, true⟩, (color q).weight⟩ : WeightedPort Label)))
  · rw [← List.ofFn_eq_map, List.ofFn_congr hy.symm]
    simpa [WeightedPort.map, Port.map, List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map y (fun q => (⟨⟨q, false⟩, (color q).weight⟩ : WeightedPort Label)))

/-- An actual single-threshold generator checks its actual weighted incoming/outgoing labels. -/
theorem genLabeling_legal {Label : Type*} {a b : List Color} (g : Cell a b)
    (color : Label → Color) (x y : List Label)
    (hx : x.length = a.length) (hy : y.length = b.length)
    (ha : a = x.map color) (hb : b = y.map color) (n : ℕ)
    (hr : raw g = [genVertex a b n]) (s : Label → Bool) :
    ((Diagram.gen g).graph interp).Legal (s ∘ (genLabeling g x y hx hy).label) ↔
      (Vertex.mk (x.map (fun q => ⟨⟨q, true⟩, (color q).weight⟩) ++
        y.map (fun q => ⟨⟨q, false⟩, (color q).weight⟩)) n).Sat s := by
  refine (genLegal_iff (I := interp) g _).symm.trans ?_
  change (∀ w ∈ raw g, w.Sat _) ↔ _
  rw [hr]
  simp only [List.mem_singleton, forall_eq]
  exact (Vertex.sat_map _ _ s).symm.trans
    (Iff.of_eq (congrArg (fun w => w.Sat s) (genVertex_labels g color x y hx hy ha hb n)))

/-- The actual crossing labels check the two original carrier joints independently. -/
theorem crossLabeling_legal {Label : Type*} (c d : Color) (a b t r : Label)
    (s : Label → Bool) :
    ((Diagram.gen (PushPuzzle.NCL.Strip.Sweep.Cell.cross c d)).graph interp).Legal
        (s ∘ (genLabeling (.cross c d) [a, b] [t, r] rfl rfl).label) ↔
      (Vertex.mk [⟨⟨a, true⟩, c.weight⟩, ⟨⟨r, false⟩, c.weight⟩] c.weight).Sat s ∧
      (Vertex.mk [⟨⟨b, true⟩, d.weight⟩, ⟨⟨t, false⟩, d.weight⟩] d.weight).Sat s := by
  refine (genLegal_iff (I := interp) (.cross c d) _).symm.trans ?_
  simp only [GenLegal, interp, raw, Prim.cross, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  rfl

/-- Equal actual boundary lists give the same actual local edge labels. -/
theorem genLabeling_congr {Label : Type*} {a b : List Color} (g : Cell a b)
    (x y x' y' : List Label) (hx : x.length = a.length) (hy : y.length = b.length)
    (hx' : x'.length = a.length) (hy' : y'.length = b.length) (he : x = x') (hf : y = y') :
    (genLabeling g x y hx hy).label = (genLabeling g x' y' hx' hy').label := by
  cases he
  cases hf
  rfl

/-- Changing equal colored boundaries retains every actual labeled vertex constraint. -/
theorem retypeLabeling_legal {Label : Type*} {a b a' b' : List Color}
    {D : Diagram Cell a b} {x y : List Label} (L : Labeling D x y)
    (ha : a = a') (hb : b = b') (s : Label → Bool) :
    ((retype D ha hb).graph interp).Legal (s ∘ (retypeLabeling L ha hb).label) ↔
      (D.graph interp).Legal (s ∘ L.label) := by
  cases ha
  cases hb
  rfl

/-- An identity transported along equal actual boundary labels has no vertex constraint. -/
theorem id_retypeLabeling_legal {Label : Type*} (color : Label → Color)
    (x y : List Label) (h : x = y) (s : Label → Bool) :
    ((retype (Diagram.id (x.map color)) rfl (congrArg (List.map color) h)).graph interp).Legal
      (s ∘ (retypeLabeling (Labeling.id (Γ := Cell) (x.map color) x (by simp)) rfl
        (congrArg (List.map color) h)).label) := by
  cases h
  exact legal_id _ _

/-- Actual unchanged frontier context adds no local vertex constraints. -/
theorem padLabeling_legal {Label : Type*} {a b : List Color} (g : Cell a b)
    (color : Label → Color) (pre x y post : List Label)
    (hx : x.length = a.length) (hy : y.length = b.length) (s : Label → Bool) :
    ((Diagram.pad (pre.map color) (.gen g) (post.map color)).graph interp).Legal
        (s ∘ (padLabeling g color pre x y post hx hy).label) ↔
      ((Diagram.gen g).graph interp).Legal (s ∘ (genLabeling g x y hx hy).label) := by
  simp only [Diagram.pad, padLabeling, Labeling.legal_tensor, Diagram.legal_id, true_and,
    and_true]

end PushPuzzle.NCL.Strip.Sweep.Cell
