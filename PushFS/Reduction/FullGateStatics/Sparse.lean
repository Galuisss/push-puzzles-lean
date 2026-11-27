/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Primitive

/-! Every canonical goal pair within a complete wire or protected corner primitive is physically separated. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Gadgets Gadgets.Wires
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem isometry_sparse {I : Instance} {W H : ℕ}
    (hs : ∀p∈I.board.goals,∀q∈I.board.goals,∀d,¬Adjacent d p q) (e : GridIsometry I.width I.height W H) :
    ∀p∈(e.reorientInstance I).board.goals,∀q∈(e.reorientInstance I).board.goals,∀d,¬Adjacent d p q := by
  intro p hp q hq d ha
  change p∈I.board.goals.map e.cells.toEmbedding at hp
  change q∈I.board.goals.map e.cells.toEmbedding at hq
  change Adjacent (w:=W) (h:=H) d p q at ha
  obtain ⟨u,hu,rfl⟩:=Finset.mem_map.mp hp
  obtain ⟨v,hv,rfl⟩:=Finset.mem_map.mp hq
  change Adjacent d (e.cells u) (e.cells v) at ha
  exact hs u hu v hv (e.directions.symm d)
    ((e.adjacent (e.directions.symm d) u v).mp (by simpa only [Equiv.apply_symm_apply] using ha))

theorem west_sparse (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    ∀p∈((GateLead.westIso kind n).reorientInstance (Chain.puzzle n hn a b)).board.goals,
      ∀q∈((GateLead.westIso kind n).reorientInstance (Chain.puzzle n hn a b)).board.goals,∀d,¬Adjacent d p q :=
  isometry_sparse (I:=Chain.puzzle n hn a b) (Catalog.chainStrong n hn a b).sparse (GateLead.westIso kind n)

theorem north_sparse (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    ∀p∈((GateLead.northIso n).reorientInstance (Chain.puzzle n hn a b)).board.goals,
      ∀q∈((GateLead.northIso n).reorientInstance (Chain.puzzle n hn a b)).board.goals,∀d,¬Adjacent d p q :=
  isometry_sparse (I:=Chain.puzzle n hn a b) (Catalog.chainStrong n hn a b).sparse (GateLead.northIso n)

theorem east_sparse (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    ∀p∈((GateLead.eastIso n).reorientInstance (Chain.puzzle n hn a b)).board.goals,
      ∀q∈((GateLead.eastIso n).reorientInstance (Chain.puzzle n hn a b)).board.goals,∀d,¬Adjacent d p q :=
  isometry_sparse (I:=Chain.puzzle n hn a b) (Catalog.chainStrong n hn a b).sparse (GateLead.eastIso n)

private theorem lineBase_sparse (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    ∀p∈(lineBase flip n hn a b).board.goals,∀q∈(lineBase flip n hn a b).board.goals,∀d,¬Adjacent d p q := by
  cases flip
  · exact (Catalog.chainStrong n hn a b).sparse
  · intro p hp q hq d
    change p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals at hp
    change q∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals at hq
    rw [FlippedChain.goals_eq] at hp hq
    exact FlippedChain.sparse_targets n hn b hp hq d

theorem line_sparse (k : Key) (i : ℕ) (hi : i<(curve k).length) (a b : Bool) :
    ∀p∈(linePiece k i hi a b).board.goals,∀q∈(linePiece k i hi a b).board.goals,∀d,¬Adjacent d p q :=
  isometry_sparse (I:=lineBase (fillerFlip k i) (fillerSpan k i) (filler_shape k i hi).2.1 a b)
    (lineBase_sparse (fillerFlip k i) (fillerSpan k i) (filler_shape k i hi).2.1 a b)
    ((lineOrientation (original k i).travel (fillerFlip k i)).axis _ _).geometry

private theorem short_sparse (kind : ShortCorners.Kind) (a b : Bool) :
    ∀p∈(ShortCorners.puzzle kind a b).board.goals,∀q∈(ShortCorners.puzzle kind a b).board.goals,∀d,¬Adjacent d p q := by
  intro p hp q hq d
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hq
  exact ShortCorners.sparse_slots kind b i j d

theorem corner_sparse (k : Key) (i : ℕ) (a b : Bool) :
    ∀p∈(cornerPiece k i a b).board.goals,∀q∈(cornerPiece k i a b).board.goals,∀d,¬Adjacent d p q :=
  isometry_sparse (I:=ShortCorners.puzzle (cornerKind k i) a b) (short_sparse (cornerKind k i) a b) (cornerIso k i).geometry

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
