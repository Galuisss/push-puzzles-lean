/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortDecodedLegalStep
import all PushS.PortBackground

/-! Every actual successful canonical play decodes to legal native input arrays at every prefix. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem propagate {α : Type} {P : α → Prop} {a b : α}
    (hr : Relation.ReflTransGen (fun x y => P x → P y) a b) (ha : P a) : P b := by
  induction hr with
  | refl => exact ha
  | tail _ hm ih => exact hm ih

/-- Every readout at every prefix of a successful actual canonical play satisfies the complete original InputLegal. -/
theorem canonicalInstance_axisReadout_legal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : List Bool) (hstart : l.InputLegal initial) (hgoal : l.InputLegal target)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM ha initial target).board none
      (l.canonicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.canonicalInstance p hl hM ha initial target).board.goals)
    {axes : List Bool} (decoded : l.AxisReadout p u axes) : l.InputLegal axes := by
  let I := l.canonicalInstance p hl hM ha initial target
  let Inv (s : State (p.W + 1) (p.H + 1)) := ∀ axes, l.AxisReadout p s axes → l.InputLegal axes
  have hbase : Inv I.initial := by
    intro axes hr
    have heq := l.canonicalInstance_decoded_initial p hl hM ha initial target hstart.axes_length hr
    rw [heq]
    exact hstart
  have hpath : Relation.ReflTransGen (fun a b => Inv a → Inv b) I.initial u := by
    apply enrich_path hsu
    intro a b hIa hstep hbu ha' next hb
    obtain ⟨before, hread⟩ := l.physicalInstance_axisReadout_exists p hl hM ha (l.canonical initial) (l.canonical target)
      hIa ((Relation.ReflTransGen.single hstep).trans (hbu.trans hut)) ht
    exact l.physicalInstance_decoded_legal_step p hl hM ha (l.canonical initial) target hgoal hIa hstep
      (hbu.trans hut) ht hread hb (ha' before hread)
  exact propagate hpath hbase axes decoded

end PushPuzzle.PushS.PortLayout
