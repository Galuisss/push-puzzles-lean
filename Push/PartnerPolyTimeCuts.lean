/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerPolyTime
public import Push.PartnerCutsRepair

/-! Total standard polynomial-time emission of an actual simultaneous partner cut. -/

public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS Turing.MultiTapeTM
open scoped PushPuzzle.PushS PushPuzzle.Push.Partner

@[fun_prop] theorem crosses_polyTime : ComputableInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => crosses p.1 p.2) (encPair encUnary encPortPair) encBool := by
  unfold crosses encPortPair
  fun_prop

/-- Sort precisely the actual crossing arcs, charging the binary decorated-key sorting machine. -/
@[fun_prop] theorem active_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ => active p.1 p.2)
    (encPair encPortLayout encUnary) (encList encPortPair) := by
  have hkey : ComputableInPolyTime Prod.fst encPortPair encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.fst _ _)
  apply (Comb.Sort.computableInPolyTime_run encPortPair hkey (0, 0)).comp
  fun_prop

@[fun_prop] theorem passive_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ => passive p.1 p.2)
    (encPair encPortLayout encUnary) (encList encPortPair) := by
  unfold passive
  fun_prop

@[fun_prop] theorem shift_polyTime : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ => shift p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encUnary := by
  unfold shift
  fun_prop

@[fun_prop] theorem mapPair_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (ℕ × ℕ) => mapPair p.1.1 p.1.2 p.2)
    (encPair encPortPair encPortPair) encPortPair := by
  unfold mapPair encPortPair
  fun_prop

@[fun_prop] theorem mapGroup_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × LowerGroup => mapGroup p.1.1 p.1.2 p.2)
    (encPair encPortPair encLowerGroup) encLowerGroup := by
  have h := encLowerGroup_elim_polyTime (encP := encPortPair) (encE := encLowerGroup)
    (g0 := fun p => .wire (shift p.1.1 p.1.2 p.2.1) (shift p.1.1 p.1.2 p.2.2))
    (g1 := fun p => .gate p.2.1 (shift p.1.1 p.1.2 p.2.2)) (by unfold encPortPair; fun_prop)
      (by unfold encPortPair; fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨_, g⟩; cases g <;> rfl)

@[fun_prop] theorem left_polyTime : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ => left p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encUnary := by unfold left; fun_prop

@[fun_prop] theorem right_polyTime : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ => right p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encUnary := by unfold right; fun_prop

@[fun_prop] theorem upperPiece_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) => upperPiece p.1.1 p.1.2 p.2)
    (encPair encPortPair (encPair encPortPair encUnary)) (encList encPortPair) := by
  unfold upperPiece encPortPair
  fun_prop

@[fun_prop] theorem lowerPiece_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) => lowerPiece p.1.1 p.1.2 p.2)
    (encPair encPortPair (encPair encPortPair encUnary)) encLowerGroup := by
  unfold lowerPiece encPortPair
  fun_prop

private theorem indexed_args_polyTime : ComputableInPolyTime
    (fun p : (ℕ × List (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => ((p.1.1, p.1.2.length), p.2))
    (encPair (encPair encUnary (encList encPortPair)) (encPair encPortPair encUnary))
    (encPair encPortPair (encPair encPortPair encUnary)) := by
  unfold encPortPair
  fun_prop

private theorem upperPieces_polyTime : ComputableInPolyTime
    (fun p : ℕ × List (ℕ × ℕ) => p.2.zipIdx.flatMap (upperPiece p.1 p.2.length))
    (encPair encUnary (encList encPortPair)) (encList encPortPair) := by
  have hz : ComputableInPolyTime (fun p : ℕ × List (ℕ × ℕ) => p.2.zipIdx)
      (encPair encUnary (encList encPortPair)) (encList (encPair encPortPair encUnary)) := by fun_prop
  have hraw := upperPiece_polyTime.comp indexed_args_polyTime
  have hcallback : ComputableInPolyTime
      (fun p : (ℕ × List (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => upperPiece p.1.1 p.1.2.length p.2)
      (encPair (encPair encUnary (encList encPortPair)) (encPair encPortPair encUnary))
      (encList encPortPair) := hraw.of_enc_eq (by intro p; rfl)
  have hm : ComputableInPolyTime
      (fun p : ℕ × List (ℕ × ℕ) => p.2.zipIdx.map (upperPiece p.1 p.2.length))
      (encPair encUnary (encList encPortPair)) (encList (encList encPortPair)) :=
    ComputableInPolyTime.mapWithInput hz hcallback
  have hf := (ComputableInPolyTime.flatten encPortPair).comp hm
  exact hf.of_enc_eq (by intro p; simp only [List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq])

private theorem lowerPieces_polyTime : ComputableInPolyTime
    (fun p : ℕ × List (ℕ × ℕ) => p.2.zipIdx.map (lowerPiece p.1 p.2.length))
    (encPair encUnary (encList encPortPair)) (encList encLowerGroup) := by
  have hz : ComputableInPolyTime (fun p : ℕ × List (ℕ × ℕ) => p.2.zipIdx)
      (encPair encUnary (encList encPortPair)) (encList (encPair encPortPair encUnary)) := by fun_prop
  exact ComputableInPolyTime.mapWithInput (encA := encPair encPortPair encUnary) (encB := encLowerGroup)
    (f := fun (p : ℕ × List (ℕ × ℕ)) (x : (ℕ × ℕ) × ℕ) => lowerPiece p.1 p.2.length x)
    hz (lowerPiece_polyTime.comp indexed_args_polyTime)

private theorem oldUpper_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List (ℕ × ℕ) => p.2.map (mapPair p.1.1 p.1.2))
    (encPair encPortPair (encList encPortPair)) (encList encPortPair) := by
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  have hp : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List (ℕ × ℕ)) × (ℕ × ℕ) => (p.1.1, p.2))
    (encPair (encPair encPortPair (encList encPortPair)) encPortPair) (encPair encPortPair encPortPair) := by
      unfold encPortPair
      fun_prop
  exact mapPair_polyTime.comp hp

private theorem oldLower_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List LowerGroup => p.2.map (mapGroup p.1.1 p.1.2))
    (encPair encPortPair (encList encLowerGroup)) (encList encLowerGroup) := by
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  have hp : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List LowerGroup) × LowerGroup => (p.1.1, p.2))
    (encPair (encPair encPortPair (encList encLowerGroup)) encLowerGroup)
    (encPair encPortPair encLowerGroup) := by unfold encPortPair; fun_prop
  exact mapGroup_polyTime.comp hp

/-- The full simultaneous-cut array emitter is polynomial-time on every raw layout. -/
@[fun_prop] theorem compile_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ => compile p.1 p.2) (encPair encPortLayout encUnary) encPortLayout := by
  have hcut := ComputableInPolyTime.snd encPortLayout encUnary
  have hcount : ComputableInPolyTime (fun p : PortLayout × ℕ => (active p.1 p.2).length)
      (encPair encPortLayout encUnary) encUnary := by fun_prop
  have hargs := hcut.prod hcount
  have hupper := upperPieces_polyTime.comp (hcut.prod active_polyTime)
  have hlower := lowerPieces_polyTime.comp (hcut.prod active_polyTime)
  have hpassive := oldUpper_polyTime.comp (hargs.prod passive_polyTime)
  have hgroups : ComputableInPolyTime (fun p : PortLayout × ℕ => p.1.lowerGroups)
      (encPair encPortLayout encUnary) (encList encLowerGroup) := by fun_prop
  have hold := oldLower_polyTime.comp (hargs.prod hgroups)
  unfold compile
  dsimp only
  fun_prop

@[fun_prop] theorem safeTest_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ => safeTest p.1 p.2) (encPair encPortLayout encUnary) encBool := by
  have htest : ComputableInPolyTime
      (fun p : ℕ × LowerGroup => match p.2 with
        | .wire .. => true
        | .gate _ first => decide (p.1 ≤ first ∨ first + 2 < p.1))
      (encPair encUnary encLowerGroup) encBool := by
    have h := encLowerGroup_elim_polyTime (encP := encUnary) (encE := encBool)
      (g0 := fun _ => true) (g1 := fun p => decide (p.1 ≤ p.2.2 ∨ p.2.2 + 2 < p.1))
      (by fun_prop) (by fun_prop)
    exact h.of_enc_eq (by intro p; rcases p with ⟨_, g⟩; cases g <;> rfl)
  unfold safeTest
  apply ComputableInPolyTime.allWithInput
  · fun_prop
  · have hp : ComputableInPolyTime
        (fun p : (PortLayout × ℕ) × LowerGroup => (p.1.2, p.2))
        (encPair (encPair encPortLayout encUnary) encLowerGroup) (encPair encUnary encLowerGroup) := by
      fun_prop
    exact (htest.comp hp).of_enc_eq (by intro p; rcases p with ⟨_, g⟩; cases g <;> rfl)

/-- The actual safe-cut decision and optional layout/port-table update are total polynomial-time. -/
@[fun_prop] theorem cutAt_polyTime : ComputableInPolyTime
    (fun p : BufferState × ℕ => cutAt p.1 p.2) (encPair encBufferState encUnary) encBufferState := by
  unfold cutAt
  fun_prop

end PushPuzzle.Push.Partner.Cuts
