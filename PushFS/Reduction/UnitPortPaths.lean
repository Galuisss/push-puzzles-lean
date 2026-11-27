/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.UnitPaths
public import PushFS.Reduction.SourceEdgeMetadata

/-! Every pair of actual creating and consuming roles is joined by its complete directed ordinary-cell path. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan

open Cslib.Complexity.NCL

theorem port_unitPath {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (e : Fin w.compile.edgeCount) (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3)
    (he : (g.ports.port r).edge=e.val) (ho : (g.ports.port r).dir=false)
    (h : VertexData) (hh : h∈vertexRecords w) (s : Fin 3)
    (he' : (h.ports.port s).edge=e.val) (hi : (h.ports.port s).dir=true) :
    UnitReach (Route.edgeSegments (refinedProgram w,e.val)) (refinePoint g.point) (refinePoint h.point) ∧
      refinePoint g.point≠refinePoint h.point := by
  obtain ⟨p,q,_,_,hf,hr⟩:=complete_unitPath hP hT e
  have hgo:=vertexRecord_tangent hP hT hg r
  have hhi:=vertexRecord_tangent hP hT hh s
  dsimp only at hgo hhi
  simp only [ho,Bool.false_eq_true,ite_false,he] at hgo
  simp only [hi,ite_true,he'] at hhi
  have hsource : refinePoint g.point=refinePoint p := by
    by_contra hn
    obtain ⟨d,hd⟩:=(hf.incoming_iff _).mpr ⟨hgo.point,hn⟩
    exact vertexRecord_not_internal hP hT hg hd hgo
  have htarget : refinePoint h.point=refinePoint q := by
    by_contra hn
    obtain ⟨d,hd⟩:=(hf.outgoing_iff _).mpr ⟨hhi.point,hn⟩
    exact vertexRecord_not_internal hP hT hh hhi hd
  have hne:=((hf.outgoing_iff _).mp ⟨g.portDirection r,hgo⟩).2
  exact ⟨hsource.symm ▸htarget.symm ▸hr,fun heq=>hne (heq.trans htarget)⟩

end PushPuzzle.PushFS.Reduction.Plan
