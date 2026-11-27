/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Compiler
public import PushPush.Doors.LayoutEncoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! Polynomial-time compilation from binary door labels to unary physical coordinates. -/

public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity
open Turing.MultiTapeTM
open scoped SelfClosingDoor

@[fun_prop] theorem doorBase_polyTime :
    ComputableInPolyTime doorBase encUnary encUnary := by unfold doorBase; fun_prop

@[fun_prop] theorem slots_polyTime :
    ComputableInPolyTime slots SelfClosingDoor.encInstance encUnary := by
  unfold slots
  fun_prop

@[fun_prop] theorem chamberHeight_polyTime :
    ComputableInPolyTime chamberHeight SelfClosingDoor.encInstance encUnary := by
  unfold chamberHeight
  fun_prop

@[fun_prop] theorem roomCount_polyTime :
    ComputableInPolyTime roomCount SelfClosingDoor.encInstance encUnary := by
  unfold roomCount
  fun_prop

@[fun_prop] theorem roomBase_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ × ℕ => roomBase q.1 q.2.1 q.2.2)
      (encPair SelfClosingDoor.encInstance (encPair encUnary encUnary)) encUnary := by
  unfold roomBase
  fun_prop

@[fun_prop] theorem inputRow_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ × ℕ × ℕ => inputRow q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair SelfClosingDoor.encInstance (encPair encUnary (encPair encUnary encUnary)))
      encUnary := by
  unfold inputRow
  fun_prop

@[fun_prop] theorem upperRow_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ × ℕ => upperRow q.1 q.2.1 q.2.2)
      (encPair SelfClosingDoor.encInstance (encPair encUnary encUnary)) encUnary := by
  unfold upperRow
  fun_prop

@[fun_prop] theorem lowerRow_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ × ℕ => lowerRow q.1 q.2.1 q.2.2)
      (encPair SelfClosingDoor.encInstance (encPair encUnary encUnary)) encUnary := by
  unfold lowerRow
  fun_prop

@[fun_prop] theorem channel_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ => channel q.1 q.2)
      (encPair SelfClosingDoor.encInstance encUnary) SelfClosingDoor.encTunnel := by
  have hm : ComputableInPolyTime (fun j : ℕ => j % 2) encUnary encUnary := by fun_prop
  have hb : ComputableInPolyTime (fun q : Instance × ℕ => channelBit q.2)
      (encPair SelfClosingDoor.encInstance encUnary) encBool := by
    unfold channelBit
    fun_prop
  have hd : ComputableInPolyTime (fun q : Instance × ℕ => q.1.doors.getD (q.2 / 2) default)
      (encPair SelfClosingDoor.encInstance encUnary) SelfClosingDoor.encDoor := by fun_prop
  unfold channel
  exact SelfClosingDoor.Door.computableInPolyTime_tunnel hd hb

@[fun_prop] theorem channelBit_polyTime :
    ComputableInPolyTime channelBit encUnary encBool := by
  have hm : ComputableInPolyTime (fun j : ℕ => j % 2) encUnary encUnary := by fun_prop
  unfold channelBit
  fun_prop

@[fun_prop] theorem upperUsed_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ × ℕ => upperUsed q.1 q.2.1 q.2.2)
      (encPair SelfClosingDoor.encInstance (encPair encUnary encUnary)) encBool := by
  unfold upperUsed
  fun_prop

@[fun_prop] theorem lowerUsed_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ × ℕ => lowerUsed q.1 q.2.1 q.2.2)
      (encPair SelfClosingDoor.encInstance (encPair encUnary encUnary)) encBool := by
  unfold lowerUsed
  fun_prop

@[fun_prop] theorem internalWires_polyTime :
    ComputableInPolyTime internalWires SelfClosingDoor.encInstance (encList encWire) := by
  unfold internalWires
  fun_prop

@[fun_prop] theorem arrivalWires_polyTime :
    ComputableInPolyTime arrivalWires SelfClosingDoor.encInstance (encList encWire) := by
  have ha : ComputableInPolyTime (fun q : Instance × ℕ => arrivalWire q.1 q.2)
      (encPair SelfClosingDoor.encInstance encUnary) encWire := by
    unfold arrivalWire
    fun_prop
  unfold arrivalWires
  fun_prop

@[fun_prop] theorem choiceWires_polyTime :
    ComputableInPolyTime choiceWires SelfClosingDoor.encInstance (encList encWire) := by
  unfold choiceWires
  fun_prop

@[fun_prop] theorem skipWires_polyTime :
    ComputableInPolyTime skipWires SelfClosingDoor.encInstance (encList encWire) := by
  unfold skipWires
  fun_prop

@[fun_prop] theorem targetRow_polyTime :
    ComputableInPolyTime targetRow SelfClosingDoor.encInstance encUnary := by
  unfold targetRow
  fun_prop

@[fun_prop] theorem cleanupWires_polyTime :
    ComputableInPolyTime cleanupWires SelfClosingDoor.encInstance (encList encWire) := by
  unfold cleanupWires
  fun_prop

@[fun_prop] theorem wires_polyTime (storage : Bool) :
    ComputableInPolyTime (wires storage) SelfClosingDoor.encInstance (encList encWire) := by
  unfold wires
  fun_prop

@[fun_prop] theorem dataRows_polyTime :
    ComputableInPolyTime dataRows SelfClosingDoor.encInstance (encList encUnary) := by
  unfold dataRows
  fun_prop

-- Compose the recipe fields and their nested list emitters in one certificate.
set_option maxHeartbeats 800000 in
/-- The complete physical recipe has a standard machine polynomial-time certificate. -/
@[fun_prop] theorem layout_polyTime (storage : Bool) :
    ComputableInPolyTime (layout storage) SelfClosingDoor.encInstance encLayout := by
  unfold layout
  fun_prop

end PushPuzzle.PushPush.Doors.Source
