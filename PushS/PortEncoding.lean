/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max

/-!
# Standard encodings of the physical port layout and signals

Port counts and indices use unary natural-number words. Groups use the native tagged
sum-of-fields encoding; layouts and states use `enc_structure` and framed lists.

## Main definitions

* `encLowerGroup`: tagged WIRE or labelled consecutive three-port data.
* `encPortLayout`: the actual two-page lists and their unary port count.
* `encSignalState`: the axis and internal Boolean arrays.
-/

public section

namespace PushPuzzle.PushS


open _root_.Turing.MultiTapeTM

namespace Shuttle

instance : FinEnum Kind := FinEnum.ofList [.andGate, .orGate] (by
  intro k
  cases k <;> simp)

/-- The constructive unary rank of the two-element gate alphabet. -/
abbrev encKind : Kind ↪ List Bool := encFinEnum Kind

end Shuttle

namespace PageLevels

/-- Tagged ordinary pairs and consecutive three-port groups, with unary port indices. -/
enc_inductive encGroup : Group where
  | wire : encUnary, encUnary
  | triple : encUnary

/-- A unary port count and the actual framed group list. -/
enc_structure encPage : Page where
  portCount : encUnary, groups : (encList encGroup)

/-- The common unary port count and the two framed group lists. -/
enc_structure encPages : Pages where
  portCount : encUnary, upper : (encList encGroup), lower : (encList encGroup)

end PageLevels

/-- Tagged WIRE endpoints or gate kind and first port, using the native inductive codec. -/
enc_inductive encLowerGroup : LowerGroup where
  | wire : encUnary, encUnary
  | gate : Shuttle.encKind, encUnary

/-- Unary port count, mathematical endpoint pairs, and the labelled lower groups. -/
enc_structure encPortLayout : PortLayout where
  portCount : encUnary,
  upperPairs : (encList (encPair encUnary encUnary)), lowerGroups : (encList encLowerGroup)

/-- The two physical Boolean arrays in axis and internal edge order. -/
enc_structure encSignalState : SignalState where
  axes : (encList encBool), internal : (encList encBool)

end PushPuzzle.PushS
