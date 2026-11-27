/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Native source properties used by the internal strip compiler. -/

public section
namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL

attribute [fun_prop] encPort_mk_polyTime encWeightedPort_mk_polyTime encVertex_mk_polyTime
  encPort_edge_polyTime encPort_dir_polyTime encWeightedPort_port_polyTime
  encWeightedPort_weight_polyTime encVertex_ports_polyTime encVertex_minInflow_polyTime

open _root_.Turing.MultiTapeTM

private theorem vertex3_polyTime {α E : Type} {input : α ↪ List Bool} {encE : E ↪ List Bool}
    {a b c : α → Port E} (ha : ComputableInPolyTime a input (encPort encE))
    (hb : ComputableInPolyTime b input (encPort encE)) (hc : ComputableInPolyTime c input (encPort encE))
    (w₁ w₂ w₃ need : ℕ) :
    ComputableInPolyTime
      (fun x => (⟨[⟨a x, w₁⟩, ⟨b x, w₂⟩, ⟨c x, w₃⟩], need⟩ : Vertex E)) input (encVertex encE) :=
  encVertex_mk_polyTime encE
    (ComputableInPolyTime.cons' (encWeightedPort_mk_polyTime encE ha (ComputableInPolyTime.const w₁))
      (ComputableInPolyTime.cons' (encWeightedPort_mk_polyTime encE hb (ComputableInPolyTime.const w₂))
        (ComputableInPolyTime.cons' (encWeightedPort_mk_polyTime encE hc (ComputableInPolyTime.const w₃))
          (ComputableInPolyTime.const [])))) (ComputableInPolyTime.const need)

@[fun_prop] theorem vertex_and_polyTime {α E : Type} {input : α ↪ List Bool} {encE : E ↪ List Bool}
    {a b c : α → Port E} (ha : ComputableInPolyTime a input (encPort encE))
    (hb : ComputableInPolyTime b input (encPort encE)) (hc : ComputableInPolyTime c input (encPort encE)) :
    ComputableInPolyTime (fun x => Vertex.and (a x) (b x) (c x)) input (encVertex encE) :=
  vertex3_polyTime ha hb hc 1 1 2 2

@[fun_prop] theorem vertex_or_polyTime {α E : Type} {input : α ↪ List Bool} {encE : E ↪ List Bool}
    {a b c : α → Port E} (ha : ComputableInPolyTime a input (encPort encE))
    (hb : ComputableInPolyTime b input (encPort encE)) (hc : ComputableInPolyTime c input (encPort encE)) :
    ComputableInPolyTime (fun x => Vertex.or (a x) (b x) (c x)) input (encVertex encE) :=
  vertex3_polyTime ha hb hc 2 2 2 2

/-- Injective edge renaming preserves port identity. -/
theorem port_map_injective {E F : Type*} {f : E → F} (hf : Function.Injective f) :
    Function.Injective (Port.map f) := by
  rintro ⟨e, d⟩ ⟨e', d'⟩ h
  have he := hf (congrArg Port.edge h)
  have hd := congrArg Port.dir h
  cases he
  cases hd
  rfl

/-- The strip construction uses a valid native AND/OR graph with no repeated edge at a vertex. -/
@[expose] def SourceValid (g : AndOrGraph) : Prop :=
  g.Bounded ∧ g.graph.IsAndOr ∧ g.graph.WellFormed ∧ g.graph.LoopFree

namespace SourceValid

open Cslib.Complexity Cslib.Complexity.NCL

/-- Forget the separate loop-freedom requirement. -/
theorem toValid {g : AndOrGraph} (h : SourceValid g) : g.Valid :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem isAndOr {g : AndOrGraph} (h : SourceValid g) : g.graph.IsAndOr := h.2.1

theorem wellFormed {g : AndOrGraph} (h : SourceValid g) : g.graph.WellFormed := h.2.2.1

theorem loopFree {g : AndOrGraph} (h : SourceValid g) : g.graph.LoopFree := h.2.2.2

/-- Record the two standard source properties together. -/
theorem ofValid {g : AndOrGraph} (h : g.Valid) (hl : g.graph.LoopFree) : SourceValid g :=
  ⟨h.1, h.2.1, h.2.2, hl⟩

end SourceValid

instance {g : AndOrGraph} : Coe (SourceValid g) g.Valid := ⟨SourceValid.toValid⟩

end PushPuzzle.NCL
