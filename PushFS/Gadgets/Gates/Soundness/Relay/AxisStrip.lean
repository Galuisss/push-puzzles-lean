/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.Data

/-! A vertical closed strip uses the same real two-identity obstruction after transposing its entire physical path. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


open Wires.Soundness Wires.Polyline

variable {I : Instance} {Label : Type} [Fintype Label]

/-- The vertical version only transports real steps; all track and terminal facts come from the original instance. -/
theorem vertical_strip_good {M : SlotMatching I Label} {S final : LabelledState Label I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (A : AxisTracks I) (lo hi x : ℕ) (i j : Label)
    (hw : StripWalls ((GridIsometry.transpose I.width I.height).board I.board) lo hi x)
    (hicol : A.name (M.source i)=.vertical x) (hjcol : A.name (M.source j)=.vertical x)
    (hij : (M.source i).2.val<(M.source j).2.val)
    (hstart : (M.source i).2.val+1<lo ∨ hi+1<(M.source j).2.val)
    (hfinish : (M.target i).2.val+1<lo ∨ hi+1<(M.target j).2.val) :
    (S.position i).2.val+1<lo ∨ hi+1<(S.position j).2.val := by
  let e:=GridIsometry.transpose I.width I.height
  have shape U (hu : Successful M U final) : Shape x (pair (I:=e.reorientInstance I) (orientLabels e U) i j) :=
    ⟨(orientLabels e U).position_mem i,(orientLabels e U).position_mem j,
      hu.line A false x i hicol,hu.line A false x j hjcol,hu.order A false x i j hicol hjcol hij⟩
  have step U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) : GeometricStep (e.board I.board) x
        (pair (I:=e.reorientInstance I) (orientLabels e U) i j)
        (pair (I:=e.reorientInstance I) (orientLabels e V) i j) :=
    ⟨shape U hu,shape V hv,pair_tracked (I:=e.reorientInstance I) (orient_step e hs) i j⟩
  have hb:=map_successful (fun U=>pair (I:=e.reorientInstance I) (orientLabels e U) i j)
    h.before .refl h.after h.solved step
  have ha:=map_successful (fun U=>pair (I:=e.reorientInstance I) (orientLabels e U) i j)
    h.after h.before .refl h.solved step
  have ht:=h.target ho cert
  have hf : Good lo hi (pair (I:=e.reorientInstance I) (orientLabels e final) i j) := by
    change (final.position i).2.val+1<lo ∨ hi+1<(final.position j).2.val
    rw [ht]
    exact hfinish
  exact good_on_successful_path
    (initial:=pair (I:=e.reorientInstance I) (orientLabels e M.initialLabelled) i j)
    (S:=pair (I:=e.reorientInstance I) (orientLabels e S) i j)
    (final:=pair (I:=e.reorientInstance I) (orientLabels e final) i j) hw hstart hf hb ha

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay
