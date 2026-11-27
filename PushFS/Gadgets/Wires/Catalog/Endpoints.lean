/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RawEndpoints

/-! Exact owned endpoint identities, canonical phase positions and the two-cell end-to-start seam convention. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def firstBaseLabel : (k : Kind)→Labels k
  | .east | .west=>Polyline.ChainEnds.first 200000 (by decide)
  | .south=>Polyline.ChainEnds.first 198061 (by decide)
  | .westSouth=>Polyline.L.inputLabel 99970 98999 (by decide)
  | .southWest=>Polyline.L.inputLabel 99001 99969 (by decide)
  | .eastSouth=>Out.firstLabel 99970 98979 (by decide)
  | .southEast=>In.firstLabel 98981 99969 (by decide)

def lastBaseLabel : (k : Kind)→Labels k
  | .east | .west=>Polyline.ChainEnds.last 200000 (by decide)
  | .south=>Polyline.ChainEnds.last 198061 (by decide)
  | .westSouth=>Polyline.L.outputLabel 99970 98999 (by decide)
  | .southWest=>Polyline.L.outputLabel 99001 99969 (by decide)
  | .eastSouth=>Out.lastLabel 99970 98979
  | .southEast=>In.lastLabel 98981 99969 (by decide)

def firstLabel (k : Kind) : (_i : Fin 1)×Labels k := ⟨0,firstBaseLabel k⟩
def lastLabel (k : Kind) : (_i : Fin 1)×Labels k := ⟨0,lastBaseLabel k⟩
def sourceFirst (k : Kind) (a b : Bool) : Cell := (slotMatching k a b).source (firstLabel k)
def sourceLast (k : Kind) (a b : Bool) : Cell := (slotMatching k a b).source (lastLabel k)

def firstPoint (k : Kind) (a : Bool) : Cell :=
  match k with
  | .east | .eastSouth=>(⟨2+a.toNat,by cases a <;> decide⟩,99033)
  | .west | .westSouth=>(⟨200002-a.toNat,by cases a <;> decide⟩,99033)
  | .south | .southEast | .southWest=>(100002,⟨2+a.toNat,by cases a <;> decide⟩)

def lastPoint (k : Kind) (a : Bool) : Cell :=
  match k with
  | .east | .southEast=>(⟨200000+a.toNat,by cases a <;> decide⟩,99033)
  | .west | .southWest=>(⟨4-a.toNat,by cases a <;> decide⟩,99033)
  | .south | .westSouth | .eastSouth=>(100002,⟨198061+a.toNat,by cases a <;> decide⟩)

/-- Every actual owned first box is exactly at its declared canonical input position. -/
theorem source_first (k : Kind) (a b : Bool) : sourceFirst k a b=firstPoint k a := by
  have ha : a.toNat≤1 := by cases a <;> decide
  cases k
  · apply Prod.ext <;> apply Fin.ext
    · change 0+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.first 200000 (by decide))).1.val=2+a.toNat
      rw [Polyline.ChainEnds.first_x]
      omega
    · change 99023+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.first 200000 (by decide))).2.val=99033
      rw [Chain.position_row]
  · apply Prod.ext <;> apply Fin.ext
    · change 0+(200005-((Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.first 200000 (by decide))).1.val+1))=200002-a.toNat
      rw [Polyline.ChainEnds.first_x]
      omega
    · change 99023+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.first 200000 (by decide))).2.val=99033
      rw [Chain.position_row]
  · apply Prod.ext <;> apply Fin.ext
    · change 99992+(21-((Chain.position 198061 (by decide) (Chain.uniform 198061 a) (Polyline.ChainEnds.first 198061 (by decide))).2.val+1))=100002
      rw [Chain.position_row]
    · change 0+(Chain.position 198061 (by decide) (Chain.uniform 198061 a) (Polyline.ChainEnds.first 198061 (by decide))).1.val=2+a.toNat
      rw [Polyline.ChainEnds.first_x]
      omega
  · let p:=(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (Polyline.L.inputLabel 99970 98999 (by decide))
    have hh : p.1.val+a.toNat=100010 ∧p.2.val=10 := normal_first_coordinates 99970 98999 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 99992+p.1.val=200002-a.toNat
      omega
    · change 99023+p.2.val=99033
      omega
  · let p:=(Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (Out.firstLabel 99970 98979 (by decide))
    have hh : p.1.val+a.toNat=100010 ∧p.2.val=10 := Out.first_coordinates 99970 98979 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 0+(100013-(p.1.val+1))=2+a.toNat
      omega
    · change 99023+p.2.val=99033
      omega
  · let p:=(In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (In.firstLabel 98981 99969 (by decide))
    have hh : p.1.val+a.toNat=99041 ∧p.2.val=10 := In.first_coordinates 98981 99969 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 99992+p.2.val=100002
      omega
    · change 0+(99044-(p.1.val+1))=2+a.toNat
      omega
  · let p:=(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (Polyline.L.inputLabel 99001 99969 (by decide))
    have hh : p.1.val+a.toNat=99041 ∧p.2.val=10 := normal_first_coordinates 99001 99969 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 0+(100013-(p.2.val+1))=100002
      omega
    · change 0+(99044-(p.1.val+1))=2+a.toNat
      omega

/-- Every actual owned last box is exactly at its declared canonical output position. -/
theorem source_last (k : Kind) (a b : Bool) : sourceLast k a b=lastPoint k a := by
  have ha : a.toNat≤1 := by cases a <;> decide
  cases k
  · apply Prod.ext <;> apply Fin.ext
    · change 0+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.last 200000 (by decide))).1.val=200000+a.toNat
      rw [Polyline.ChainEnds.last_x]
      omega
    · change 99023+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.last 200000 (by decide))).2.val=99033
      rw [Chain.position_row]
  · apply Prod.ext <;> apply Fin.ext
    · change 0+(200005-((Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.last 200000 (by decide))).1.val+1))=4-a.toNat
      rw [Polyline.ChainEnds.last_x]
      omega
    · change 99023+(Chain.position 200000 (by decide) (Chain.uniform 200000 a) (Polyline.ChainEnds.last 200000 (by decide))).2.val=99033
      rw [Chain.position_row]
  · apply Prod.ext <;> apply Fin.ext
    · change 99992+(21-((Chain.position 198061 (by decide) (Chain.uniform 198061 a) (Polyline.ChainEnds.last 198061 (by decide))).2.val+1))=100002
      rw [Chain.position_row]
    · change 0+(Chain.position 198061 (by decide) (Chain.uniform 198061 a) (Polyline.ChainEnds.last 198061 (by decide))).1.val=198061+a.toNat
      rw [Polyline.ChainEnds.last_x]
      omega
  · let p:=(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (Polyline.L.outputLabel 99970 98999 (by decide))
    have hh : p.1.val=10 ∧p.2.val=99038+a.toNat := normal_last_coordinates 99970 98999 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 99992+p.1.val=100002
      omega
    · change 99023+p.2.val=198061+a.toNat
      omega
  · let p:=(Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (Out.lastLabel 99970 98979)
    have hh : p.1.val=10 ∧p.2.val=99038+a.toNat := Out.last_coordinates 99970 98979 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 0+(100013-(p.1.val+1))=100002
      omega
    · change 99023+p.2.val=198061+a.toNat
      omega
  · let p:=(In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (In.lastLabel 98981 99969 (by decide))
    have hh : p.1.val=10 ∧p.2.val=100008+a.toNat := In.last_coordinates 98981 99969 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 99992+p.2.val=200000+a.toNat
      omega
    · change 0+(99044-(p.1.val+1))=99033
      omega
  · let p:=(Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).source
      (Polyline.L.outputLabel 99001 99969 (by decide))
    have hh : p.1.val=10 ∧p.2.val=100008+a.toNat := normal_last_coordinates 99001 99969 (by decide) (by decide) a b
    apply Prod.ext <;> apply Fin.ext
    · change 0+(100013-(p.2.val+1))=4-a.toNat
      omega
    · change 0+(99044-(p.1.val+1))=99033
      omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
