/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.ProgramFlowData
public import PushFS.Reduction.RefinedFlow

/-! Every real compiled source edge has its complete actual directed unit path between its original vertices. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

private theorem active_flow {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b) :
    b=[] → ∀ st,Numbered st → st.wires.length=a.length → ∀ y (i : Fin st.wires.length),
    ∃ p,InputEndpoint w st y (st.wires.getD i.val 0) p ∧
      Connects (Route.edgeSegments (programFrom w st y,st.wires.getD i.val 0)) (4*i.val,y) p ∧
      UnitFlow (Route.edgeSegments (programFrom w st y,st.wires.getD i.val 0)) (4*i.val,y) p := by
  induction D with
  | nil a =>
    intro hb st _ hlen y i
    have hi:=i.isLt
    simp only [hb,List.length_nil] at hlen
    omega
  | @cons sl w a b c layer rest ih =>
    intro hc st hn hlen y i
    let l : Layer := ⟨sl,st⟩
    have hl : l.HasDrawing := ⟨a,b,layer,hlen⟩
    have hn' := l.after_numbered hn hl
    have hlen' := drawn_after_length layer st hlen
    let ss := (l.incomingRoute i.val).path.map (fun s=>s.translate 0 y)
    have hdata : Route.edgeSegments (programFrom (sl::w) st y,st.wires.getD i.val 0)=
        ss++Route.edgeSegments (programFrom w (sl.run st) (y+l.height),st.wires.getD i.val 0) := by
      rw [programFrom_edgeSegments_cons,l.incoming_segments hn i]
    cases hx : l.exitIndex i.val with
    | none =>
      let p : GridRouting.Point := (l.vertexPoint.1,l.vertexPoint.2+y)
      have hf : UnitFlow ss (4*i.val,y) p := by
        simpa only [Layer.incomingTarget,hx,Option.elim_none,Nat.add_zero,Nat.zero_add] using
          (l.incoming_unitFlow hl i).translate 0 y
      have hconn : Connects ss (4*i.val,y) p := by
        simpa only [Layer.incomingTarget,hx,Option.elim_none,Nat.add_zero,Nat.zero_add] using
          (l.incoming_connects hl i).translate 0 y
      have hnext : st.next≤(sl.run st).next := by
        change l.before.next≤l.after.next
        rw [l.after_next hl]
        omega
      have hzero := programFrom_segments_absent rest (sl.run st) hn' hlen'
        ((hn.getD_lt i.isLt).trans_le hnext) (l.consumed_absent hn hl i hx) (y+l.height)
      refine ⟨p,incoming_endpoint i hx,?_,?_⟩
      · rw [hdata,hzero,List.append_nil]
        exact hconn
      · rw [hdata,hzero,List.append_nil]
        exact hf
    | some j =>
      have hj := l.exitIndex_lt hl i.isLt hx
      obtain ⟨p,hmeta,hcT,hfT⟩ := ih hc (sl.run st) hn' hlen' (y+l.height) ⟨j,hj⟩
      have hedge := l.exitIndex_edge hl hx
      change (sl.run st).wires.getD j 0=st.wires.getD i.val 0 at hedge
      rw [hedge] at hmeta hcT hfT
      have hf : UnitFlow ss (4*i.val,y) (4*j,y+l.height) := by
        simpa only [Layer.incomingTarget,hx,Option.elim_some,Nat.add_zero,Nat.zero_add,Nat.add_comm] using
          (l.incoming_unitFlow hl i).translate 0 y
      have hconn : Connects ss (4*i.val,y) (4*j,y+l.height) := by
        simpa only [Layer.incomingTarget,hx,Option.elim_some,Nat.add_zero,Nat.zero_add,Nat.add_comm] using
          (l.incoming_connects hl i).translate 0 y
      have huniq : ∀ p,HasPoint (Route.edgeSegments (programFrom w (sl.run st) (y+l.height),st.wires.getD i.val 0)) p →
          p.2=y+l.height → p=(4*j,y+l.height) :=
        fun p hp hy=>programFrom_named_top rest (sl.run st) hn' hlen' (y+l.height) ⟨j,hj⟩ hedge hp hy
      refine ⟨p,InputEndpoint.later hmeta,?_,?_⟩
      · rw [hdata]
        exact hconn.append hcT
      · rw [hdata]
        exact hf.append_at_row hfT hconn hcT huniq

private theorem allocated_flow {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b) :
    b=[] → ∀ st,Numbered st → st.wires.length=a.length → ∀ y e,st.next≤e → e<(Word.run w st).next →
    ∃ p q,OutputEndpoint w st y e p ∧ InputEndpoint w st y e q ∧
      Connects (Route.edgeSegments (programFrom w st y,e)) p q ∧ UnitFlow (Route.edgeSegments (programFrom w st y,e)) p q := by
  induction D with
  | nil a => intro _ st _ _ y e hlo hhi; change e<st.next at hhi; omega
  | @cons sl w a b c layer rest ih =>
    intro hc st hn hlen y e hlo hhi
    let l : Layer := ⟨sl,st⟩
    have hl : l.HasDrawing := ⟨a,b,layer,hlen⟩
    have hn' := l.after_numbered hn hl
    have hlen' := drawn_after_length layer st hlen
    change e<(Word.run w (sl.run st)).next at hhi
    by_cases he : e<l.after.next
    · let j := e-st.next
      have hj : j<sl.data.outputs.length := by
        rw [l.after_next hl] at he
        change e<st.next+sl.data.outputs.length at he
        dsimp [j]
        omega
      have hej : st.next+j=e := by dsimp [j]; omega
      let ix := sl.data.offset+j
      have hix : ix<(sl.run st).wires.length := l.outputIndex_lt hl ⟨j,hj⟩
      obtain ⟨q,hmeta,hcT,hfT⟩ := active_flow rest hc (sl.run st) hn' hlen' (y+l.height) ⟨ix,hix⟩
      have hedge : (sl.run st).wires.getD ix 0=e := (l.after_output hl ⟨j,hj⟩).trans hej
      rw [hedge] at hmeta hcT hfT
      let p : GridRouting.Point := (l.vertexPoint.1,l.vertexPoint.2+y)
      let ss := (l.createdRoute j).path.map (fun s=>s.translate 0 y)
      have hf : UnitFlow ss p (4*ix,y+l.height) := by
        simpa only [ss,p,ix,Nat.add_zero,Nat.zero_add,Nat.add_comm] using (l.created_unitFlow hl ⟨j,hj⟩).translate 0 y
      have hconn : Connects ss p (4*ix,y+l.height) := by
        simpa only [ss,p,ix,Nat.add_zero,Nat.zero_add,Nat.add_comm] using (l.created_connects hl ⟨j,hj⟩).translate 0 y
      have hout : OutputEndpoint (sl::w) st y e p := by
        simpa only [Layer.outputPort,hej] using OutputEndpoint.here sl w st y ⟨j,hj⟩
      have hdata : Route.edgeSegments (programFrom (sl::w) st y,e)=
          ss++Route.edgeSegments (programFrom w (sl.run st) (y+l.height),e) := by
        rw [programFrom_edgeSegments_cons,← hej,l.created_segments hn ⟨j,hj⟩]
      have huniq : ∀ r,HasPoint (Route.edgeSegments (programFrom w (sl.run st) (y+l.height),e)) r →
          r.2=y+l.height → r=(4*ix,y+l.height) :=
        fun r hr hy=>programFrom_named_top rest (sl.run st) hn' hlen' (y+l.height) ⟨ix,hix⟩ hedge hr hy
      refine ⟨p,q,hout,InputEndpoint.later hmeta,?_,?_⟩
      · rw [hdata]
        exact hconn.append hcT
      · rw [hdata]
        exact hf.append_at_row hfT hconn hcT huniq
    · have he' : (sl.run st).next≤e := by change l.after.next≤e; omega
      obtain ⟨p,q,hout,hin,hconn,hf⟩ := ih hc (sl.run st) hn' hlen' (y+l.height) e he' hhi
      have hzero : Route.edgeSegments (l.connections,e)=[] := by
        unfold Route.edgeSegments
        apply List.flatMap_eq_nil_iff.mpr
        intro r hr
        have hb := l.connection_edge_lt hn hl hr
        have hne : r.edge≠e := by omega
        simp only [hne,ite_false]
      have hdata : Route.edgeSegments (programFrom (sl::w) st y,e)=
          Route.edgeSegments (programFrom w (sl.run st) (y+l.height),e) := by
        rw [programFrom_edgeSegments_cons,hzero]
        rfl
      refine ⟨p,q,OutputEndpoint.later hout,InputEndpoint.later hin,?_,?_⟩
      · rw [hdata]; exact hconn
      · rw [hdata]; exact hf

/-- Every actual finite source edge has its complete ordinary unit-flow contract on the emitted instruction table. -/
theorem complete_flow {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] []) (e : Fin w.compile.edgeCount) :
    ∃ p q,OutputEndpoint w ⟨[],0,[]⟩ 0 e.val p ∧ InputEndpoint w ⟨[],0,[]⟩ 0 e.val q ∧
      Connects (Route.edgeSegments (program w,e.val)) p q ∧ UnitFlow (Route.edgeSegments (program w,e.val)) p q := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  exact allocated_flow D rfl ⟨[],0,[]⟩ ⟨by simp,by simp⟩ rfl 0 e.val (Nat.zero_le _) e.isLt

/-- The actual refined source program retains that full contract at every intervening new integer pixel. -/
theorem complete_refined_flow {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] []) (e : Fin w.compile.edgeCount) :
    ∃ p q,OutputEndpoint w ⟨[],0,[]⟩ 0 e.val p ∧ InputEndpoint w ⟨[],0,[]⟩ 0 e.val q ∧
      UnitFlow (Route.edgeSegments (refinedProgram w,e.val)) (refinePoint p) (refinePoint q) := by
  obtain ⟨p,q,hp,hq,_,hf⟩ := complete_flow hP hT e
  refine ⟨p,q,hp,hq,?_⟩
  rw [refinedProgram,Route.edgeSegments_refined]
  exact hf.refined

end PushPuzzle.PushFS.Reduction.Plan
