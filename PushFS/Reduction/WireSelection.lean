/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.NamedSegments
public import PushFS.Reduction.DownwardRoutes
public import PushFS.Gadgets.Wires.Catalog.Bitmap
public import PushFS.Gadgets.Wires.Catalog.Endpoints
import Mathlib.Tactic.DeriveFintype

/-! Executable selection of the seven actual physical wire cells from real source unit-arc masks. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Raster


open Cslib.Complexity.NCL Plan Gadgets.Wires Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction

deriving instance Fintype for Mask

/-- One actual incoming or outgoing direction. -/
def Mask.single (d : Direction) : Mask :=
  ⟨decide (d=.north),decide (d=.east),decide (d=.south),decide (d=.west)⟩

theorem Mask.single_get (d e : Direction) : (Mask.single d).get e=decide (e=d) := by
  cases d <;> cases e <;> rfl

private theorem Mask.ext_get {m n : Mask} (h : ∀ d,m.get d=n.get d) : m=n := by
  cases m
  cases n
  congr 1
  · exact h .north
  · exact h .east
  · exact h .south
  · exact h .west

/-- The input mask points to the predecessor; the output mask points to the successor. -/
def selectWire (q : Mask × Mask) : Option Catalog.Kind :=
  if q=(Mask.single .west,Mask.single .east) then some .east
  else if q=(Mask.single .east,Mask.single .west) then some .west
  else if q=(Mask.single .north,Mask.single .south) then some .south
  else if q=(Mask.single .east,Mask.single .south) then some .westSouth
  else if q=(Mask.single .west,Mask.single .south) then some .eastSouth
  else if q=(Mask.single .north,Mask.single .east) then some .southEast
  else if q=(Mask.single .north,Mask.single .west) then some .southWest else none

theorem selectWire_correct : ∀ (m n : Mask) (k : Catalog.Kind),
    selectWire (m,n)=some k ↔ m=Mask.single (Catalog.sourceDirection k).opposite ∧
      n=Mask.single (Catalog.targetDirection k) := by decide +kernel

private theorem selectWire_polyTime :
    ComputableInPolyTime selectWire (encPair encMask encMask) (encOption Catalog.encKind) := of_finite _

/-- The actual polynomial-time glyph lookup used at an ordinary named source-wire pixel. -/
def wireAt (q : Word × (ℕ × GridRouting.Point)) : Option Catalog.Kind :=
  selectWire (incomingMask q,outgoingMask q)

theorem wireAt_polyTime :
    ComputableInPolyTime wireAt (encPair encWord (encPair encUnary Bitmap.encPoint)) (encOption Catalog.encKind) := by
  have hs := selectWire_polyTime
  unfold wireAt
  fun_prop

/-- The unit query reads exactly the ordered instruction list of that original named source edge. -/
theorem outgoing_named (d : Direction) (w : Word) (e : ℕ) (p : GridRouting.Point) :
    outgoing d (w,(e,p))=true ↔ HasArc (Route.edgeSegments (refinedProgram w,e)) d p :=
  (outgoing_correct d w e p).trans (Route.edgeSegments_arcs _ _ _ _).symm

theorem incoming_named (d : Direction) (w : Word) (e : ℕ) (p : GridRouting.Point) :
    incoming d (w,(e,p))=true ↔ HasIncoming (Route.edgeSegments (refinedProgram w,e)) d p := by
  rw [incoming_eq_neighbor]
  cases hn : neighbor d p with
  | none => simp [HasIncoming,hn]
  | some q =>
    simp only [Option.elim_some]
    rw [outgoing_named]
    simp [HasIncoming,hn]

private theorem outgoingMask_of_flow {w : Word} {e : ℕ} {p source target : GridRouting.Point}
    (f : UnitFlow (Route.edgeSegments (refinedProgram w,e)) source target) {d : Direction}
    (hd : HasArc (Route.edgeSegments (refinedProgram w,e)) d p) : outgoingMask (w,(e,p))=Mask.single d := by
  apply Mask.ext_get
  intro a
  rw [outgoingMask_get,Mask.single_get]
  apply Bool.eq_iff_iff.mpr
  rw [outgoing_named,decide_eq_true_eq]
  exact ⟨fun ha=>f.outgoing_unique p a d ha hd,fun he=>he.symm ▸ hd⟩

private theorem incomingMask_of_flow {w : Word} {e : ℕ} {p source target : GridRouting.Point}
    (f : UnitFlow (Route.edgeSegments (refinedProgram w,e)) source target) {d : Direction}
    (hd : HasIncoming (Route.edgeSegments (refinedProgram w,e)) d p) : incomingMask (w,(e,p))=Mask.single d := by
  apply Mask.ext_get
  intro a
  rw [incomingMask_get,Mask.single_get]
  apply Bool.eq_iff_iff.mpr
  rw [incoming_named,decide_eq_true_eq]
  exact ⟨fun ha=>f.incoming_unique p a d ha hd,fun he=>he.symm ▸ hd⟩

private theorem directions_checked : ∀ (d e : Direction), d≠.south → e≠.north → d≠e →
    ∃ k : Catalog.Kind,(Catalog.sourceDirection k).opposite=d ∧ Catalog.targetDirection k=e := by decide +kernel

/-- Ordinary pixels of a true downward source path select an actual physical glyph with exactly the right two ports. -/
theorem wireAt_of_flow {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {e : ℕ} {p source target : GridRouting.Point}
    (f : UnitFlow (Route.edgeSegments (refinedProgram w,e)) source target)
    (hp : HasPoint (Route.edgeSegments (refinedProgram w,e)) p) (hsource : p≠source) (htarget : p≠target) :
    ∃ k,wireAt (w,(e,p))=some k := by
  obtain ⟨di,hi⟩ := (f.incoming_iff p).mpr ⟨hp,hsource⟩
  obtain ⟨do_,ho⟩ := (f.outgoing_iff p).mpr ⟨hp,htarget⟩
  have hdi : di≠.south := by
    intro he
    subst di
    have hh := (incoming_named .south w e p).mpr hi
    rw [incoming_south_false hP hT] at hh
    contradiction
  have hdo : do_≠.north := by
    intro he
    subst do_
    have hh := (outgoing_named .north w e p).mpr ho
    rw [outgoing_north_false hP hT] at hh
    contradiction
  have hne : di≠do_ := fun he=>f.no_uturn p di hi (he.symm ▸ ho)
  obtain ⟨k,hkIn,hkOut⟩ := directions_checked di do_ hdi hdo hne
  refine ⟨k,?_⟩
  apply (selectWire_correct _ _ k).mpr
  rw [incomingMask_of_flow f hi,outgoingMask_of_flow f ho,hkIn,hkOut]
  exact ⟨rfl,rfl⟩

end PushPuzzle.PushFS.Reduction.Raster
