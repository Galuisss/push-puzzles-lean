/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEncoding
public import PushS.Source.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Standard native constraint data of the actual port layout

Each actual upper wire contributes its two upper inputs and threshold one. A lower wire uses
its two lower inputs and threshold one; the actual lower AND/OR triple retains its native
weights and threshold two. The existing native graph serializer supplies the finite semantics.

## Main definitions

* `PortLayout.graphData`: standard native constraint records of the actual numerical groups.

## Main results

* `PortLayout.computableInPolyTime_graphData`: standard polynomial-time native serialization.
-/

public section

namespace PushPuzzle.PushS.PortLayout

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

private def upperVertex (p : ℕ × ℕ) : NCL.Vertex ℕ :=
  ⟨[⟨⟨p.1, true⟩, 1⟩, ⟨⟨p.2, true⟩, 1⟩], 1⟩

private def gateVertex (kind : Shuttle.Kind) (first : ℕ) : NCL.Vertex ℕ :=
  if kind = .andGate then
    .and ⟨first, false⟩ ⟨first + 1, false⟩ ⟨first + 2, false⟩
  else .or ⟨first, false⟩ ⟨first + 1, false⟩ ⟨first + 2, false⟩

private def lowerVertex : LowerGroup → NCL.Vertex ℕ
  | .wire a b => ⟨[⟨⟨a, false⟩, 1⟩, ⟨⟨b, false⟩, 1⟩], 1⟩
  | .gate kind first => gateVertex kind first

/-- The actual original groups as standard native finite constraint-graph records. -/
def graphData (l : PortLayout) : NCL.AndOrGraph where
  vertices := l.upperPairs.map upperVertex ++ l.lowerGroups.map lowerVertex
  edgeCount := l.portCount

/-- The actual standard native graph retains precisely the original interface axes. -/
theorem graphData_edgeCount (l : PortLayout) : l.graphData.edgeCount = l.portCount := by
  rfl

private theorem computableInPolyTime_wireVertex (dir : Bool) :
    ComputableInPolyTime (fun p : ℕ × ℕ =>
      (⟨[⟨⟨p.1, dir⟩, 1⟩, ⟨⟨p.2, dir⟩, 1⟩], 1⟩ : NCL.Vertex ℕ))
      (encPair encUnary encUnary) (NCL.encVertex encNat) := by
  have ha := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.fst encUnary encUnary)
  have hb := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd encUnary encUnary)
  exact NCL.encVertex_mk_polyTime encNat
    (ComputableInPolyTime.cons'
      (NCL.encWeightedPort_mk_polyTime encNat (NCL.encPort_mk_polyTime encNat ha (ComputableInPolyTime.const dir)) (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.cons'
        (NCL.encWeightedPort_mk_polyTime encNat (NCL.encPort_mk_polyTime encNat hb (ComputableInPolyTime.const dir)) (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.const []))) (ComputableInPolyTime.const 1)

private theorem computableInPolyTime_upperVertex :
    ComputableInPolyTime upperVertex (encPair encUnary encUnary) (NCL.encVertex encNat) :=
  computableInPolyTime_wireVertex true

private theorem computableInPolyTime_gateVertex :
    ComputableInPolyTime (fun p : Shuttle.Kind × ℕ => gateVertex p.1 p.2)
      (encPair Shuttle.encKind encUnary) (NCL.encVertex encNat) := by
  have hf := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.snd Shuttle.encKind encUnary)
  have hk : ComputableInPolyTime (fun p : Shuttle.Kind × ℕ => decide (p.1 = .andGate))
      (encPair Shuttle.encKind encUnary) encBool :=
    (ComputableInPolyTime.of_finite (encIn := Shuttle.encKind) (encOut := encBool)
      (fun kind : Shuttle.Kind => decide (kind = .andGate))).comp
        (ComputableInPolyTime.fst Shuttle.encKind encUnary)
  unfold gateVertex
  fun_prop

private theorem computableInPolyTime_lowerVertex :
    ComputableInPolyTime lowerVertex encLowerGroup (NCL.encVertex encNat) := by
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ =>
      (⟨[⟨⟨p.1, false⟩, 1⟩, ⟨⟨p.2, false⟩, 1⟩], 1⟩ : NCL.Vertex ℕ))
      (encPair encUnary encUnary) (NCL.encVertex encNat) :=
    computableInPolyTime_wireVertex false
  have h := encLowerGroup_elim_polyTime (encP := encBool) (encE := NCL.encVertex encNat)
    (g0 := fun p => (⟨[⟨⟨p.2.1, false⟩, 1⟩, ⟨⟨p.2.2, false⟩, 1⟩], 1⟩ : NCL.Vertex ℕ))
    (g1 := fun p => gateVertex p.2.1 p.2.2)
    (hw.comp (ComputableInPolyTime.snd _ _))
    (computableInPolyTime_gateVertex.comp (ComputableInPolyTime.snd _ _))
  exact (h.comp (ComputableInPolyTime.const false |>.prod ComputableInPolyTime.id')).of_enc_eq (by
    intro group
    cases group <;> rfl)

/-- Standard native constraint data of the same actual port layout emits in polynomial time. -/
theorem computableInPolyTime_graphData :
    ComputableInPolyTime graphData encPortLayout NCL.encAndOrGraph := by
  have hu : ComputableInPolyTime (fun l : PortLayout => l.upperPairs.map upperVertex)
      encPortLayout (encList (NCL.encVertex encNat)) := by
    apply ComputableInPolyTime.mapWithInput
      (encPortLayout_upperPairs_polyTime ComputableInPolyTime.id')
    exact computableInPolyTime_upperVertex.comp (ComputableInPolyTime.snd _ _)
  have hl : ComputableInPolyTime (fun l : PortLayout => l.lowerGroups.map lowerVertex)
      encPortLayout (encList (NCL.encVertex encNat)) := by
    apply ComputableInPolyTime.mapWithInput
      (encPortLayout_lowerGroups_polyTime ComputableInPolyTime.id')
    exact computableInPolyTime_lowerVertex.comp (ComputableInPolyTime.snd _ _)
  have hc := ComputableInPolyTime.unary_to_binary.comp
    (encPortLayout_portCount_polyTime ComputableInPolyTime.id')
  have hv : ComputableInPolyTime
      (fun l : PortLayout => l.upperPairs.map upperVertex ++ l.lowerGroups.map lowerVertex)
      encPortLayout (encList (NCL.encVertex encNat)) := by fun_prop
  unfold graphData
  exact NCL.encAndOrGraph_mk_polyTime hv hc

end PushPuzzle.PushS.PortLayout
