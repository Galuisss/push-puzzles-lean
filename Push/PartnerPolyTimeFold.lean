/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerPolyTimeConfiguration
public import Push.PartnerResourcesEncoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold

/-! Uniform polynomial-time certificates for the actual repair folds on all raw inputs. -/

public section
namespace PushPuzzle.Push.Partner

open PushS Turing.MultiTapeTM
open scoped PushPuzzle.PushS PushPuzzle.Push.Partner

namespace BufferState

@[fun_prop] theorem scan_polyTime : ComputableInPolyTime
    (fun p : BufferState × List ℕ => p.1.scan p.2)
    (encPair encBufferState (encList encUnary)) encBufferState := by
  have hl : ComputableInPolyTime (fun p : BufferState × List ℕ => p.2)
      (encPair encBufferState (encList encUnary)) (encList encUnary) := by fun_prop
  have hs : ComputableInPolyTime (fun p : BufferState × List ℕ => p.1)
      (encPair encBufferState (encList encUnary)) encBufferState := by fun_prop
  have hsize := hs.polyBounded_length
  have hlist := hl.polyBounded_length
  exact ComputableInPolyTime.foldl' hl hs bufferAt_polyTime
    (B := fun p => 100 * ((encBufferState p.1).length + 2 * (encList encUnary p.2).length + 3) ^ 2)
    (PolyBounded.mul (PolyBounded.const 100)
      (((hsize.add ((PolyBounded.const 2).mul hlist)).add (PolyBounded.const 3)).pow 2))
    (by intro p i _; exact Resources.internal_prefix_code p.1 p.2 i)

end BufferState
namespace Cuts

@[fun_prop] theorem scan_polyTime : ComputableInPolyTime
    (fun p : BufferState × List ℕ => scan p.1 p.2)
    (encPair encBufferState (encList encUnary)) encBufferState := by
  have hl : ComputableInPolyTime (fun p : BufferState × List ℕ => p.2)
      (encPair encBufferState (encList encUnary)) (encList encUnary) := by fun_prop
  have hs : ComputableInPolyTime (fun p : BufferState × List ℕ => p.1)
      (encPair encBufferState (encList encUnary)) encBufferState := by fun_prop
  have hsize := hs.polyBounded_length
  have hlist := hl.polyBounded_length
  exact ComputableInPolyTime.foldl' hl hs cutAt_polyTime
    (B := fun p => 100 * ((encBufferState p.1).length +
      2 * (encBufferState p.1).length * (encList encUnary p.2).length + 3) ^ 2)
    (PolyBounded.mul (PolyBounded.const 100)
      (((hsize.add (((PolyBounded.const 2).mul hsize).mul hlist)).add (PolyBounded.const 3)).pow 2))
    (by intro p i _; exact Resources.cut_prefix_code p.1 p.2 i)

end Cuts

@[fun_prop] theorem bufferInternal_polyTime : ComputableInPolyTime
    bufferInternal encPortLayout encBufferState := by
  unfold bufferInternal
  fun_prop

namespace Cuts

@[fun_prop] theorem repair_polyTime : ComputableInPolyTime
    repair encPortLayout encBufferState := by
  unfold repair
  fun_prop

end Cuts
end PushPuzzle.Push.Partner
