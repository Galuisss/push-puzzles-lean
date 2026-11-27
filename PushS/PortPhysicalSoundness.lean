/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortDecodedLegal
public import PushS.PortAxisDecodeStep
import all PushS.PortDecodedLegal
import all PushS.PortBackground

/-! Actual wall-free storage solutions project to original legal single-axis reconfiguration paths. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
  (initial target : List Bool) (hstart : l.InputLegal initial) (hgoal : l.InputLegal target)

local notation "I" => l.canonicalInstance p hl hM ha initial target

include hstart hgoal

/-- Every actual successful canonical step decodes to stuttering or one original legal axis flip. -/
theorem canonicalInstance_axisReadout_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (targetReadout : l.AxisReadout p v next) :
    axes = next ∨ l.AxisStep axes next := by
  have hs := l.canonicalInstance_axisReadout_legal p hl hM ha initial target hstart hgoal hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht source
  have ht' := l.canonicalInstance_axisReadout_legal p hl hM ha initial target hstart hgoal (hsu.tail hm) hvt ht targetReadout
  exact l.physicalInstance_axisReadout_step p hl hM ha (l.canonical initial) (l.canonical target) hsu hm hvt ht source targetReadout hs ht'

/-- Every decoded actual prefix lies on an original legal axis path from the original complete initial word. -/
theorem canonicalInstance_axisReadout_reachable {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {axes : List Bool} (decoded : l.AxisReadout p u axes) :
    Relation.ReflTransGen l.AxisStep initial axes := by
  let Inv (s : State (p.W + 1) (p.H + 1)) := ∀ axes, l.AxisReadout p s axes → Relation.ReflTransGen l.AxisStep initial axes
  have hbase : Inv (I).initial := by
    intro axes hr
    have heq := l.canonicalInstance_decoded_initial p hl hM ha initial target hstart.axes_length hr
    rw [heq]
  have hpath : Relation.ReflTransGen (fun a b => Inv a → Inv b) (I).initial u := by
    apply enrich_path hsu
    intro a b hIa hstep hbu ha' next hb
    obtain ⟨before, hread⟩ := l.physicalInstance_axisReadout_exists p hl hM ha (l.canonical initial) (l.canonical target)
      hIa ((Relation.ReflTransGen.single hstep).trans (hbu.trans hut)) ht
    have hprefix := ha' before hread
    rcases l.canonicalInstance_axisReadout_step p hl hM ha initial target hstart hgoal hIa hstep (hbu.trans hut) ht hread hb with heq | hflip
    · exact heq ▸ hprefix
    · exact hprefix.tail hflip
  exact propagate hpath hbase axes decoded

/-- Solving the original emitted wall-free storage instance yields a legal path of original interface-axis flips. -/
theorem canonicalInstance_solvable_implies_axisReachable (hsol : (I).Solvable) :
    Relation.ReflTransGen l.AxisStep initial target := by
  obtain ⟨t, hr, ht⟩ := hsol
  obtain ⟨axes, decoded⟩ := l.physicalInstance_axisReadout_exists p hl hM ha (l.canonical initial) (l.canonical target) hr .refl ht
  have hp := l.canonicalInstance_axisReadout_reachable p hl hM ha initial target hstart hgoal hr .refl ht decoded
  have heq := l.canonicalInstance_decoded_goal p hl hM ha initial target hgoal.axes_length ht decoded
  exact heq ▸ hp

end Canonical
end PushPuzzle.PushS.PortLayout
