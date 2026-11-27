/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutOrder
public import PushFS.Gadgets.Wires.Catalog.InOrder
public import PushFS.Gadgets.Wires.Catalog.AlignedPlacement
public import PushFS.Gadgets.Wires.Polyline.StrongTransport
public import PushFS.Gadgets.Wires.Catalog.Data

/-! Actual supported rail/sink certificates of every native finite-cell D4 placement. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

structure StrongTracks (I : Instance) where
  axes : AxisTracks I
  strong : ∀p q, axes.name p≠.outside→Displacement I.board p q→(axes.name p).Strong (axes.name q)
  sparse : ∀p∈I.board.goals, ∀q∈I.board.goals, ∀d, ¬Adjacent d p q

namespace StrongTracks

variable {I : Instance}

def rotate (A : StrongTracks I) {W H : ℕ} (e : AxisIsometry I.width I.height W H) :
    StrongTracks (e.geometry.reorientInstance I) where
  axes:=Polyline.reorientedAxisTracks A.axes A.strong A.sparse e
  strong p q hp hd:=by
    obtain ⟨p,rfl⟩:=e.geometry.cells.surjective p
    obtain ⟨q,rfl⟩:=e.geometry.cells.surjective q
    change (e.name (A.axes.name (e.geometry.cells.symm (e.geometry.cells p)))).Strong
      (e.name (A.axes.name (e.geometry.cells.symm (e.geometry.cells q))))
    change e.name (A.axes.name (e.geometry.cells.symm (e.geometry.cells p)))≠.outside at hp
    simp only [Equiv.symm_apply_apply] at hp ⊢
    apply e.strong
    apply A.strong
    · intro he
      exact hp ((e.outside _).mpr he)
    · exact (e.geometry.displacement_iff I.board p q).mp hd
  sparse p hp q hq d:=by
    change p∈I.board.goals.map e.geometry.cells.toEmbedding at hp
    change q∈I.board.goals.map e.geometry.cells.toEmbedding at hq
    obtain ⟨p,hpLocal,rfl⟩:=Finset.mem_map.mp hp
    obtain ⟨q,hqLocal,rfl⟩:=Finset.mem_map.mp hq
    intro ha
    change Adjacent d (e.geometry.cells p) (e.geometry.cells q) at ha
    exact A.sparse p hpLocal q hqLocal (e.geometry.directions.symm d)
      ((e.geometry.adjacent _ _ _).mp (by simpa only [Equiv.apply_symm_apply] using ha))

private theorem rotate_name (A : StrongTracks I) {W H : ℕ} (e : AxisIsometry I.width I.height W H)
    (p : PushFS.Cell I.width I.height) :
    (A.rotate e).axes.name (e.geometry.cells p)=e.name (A.axes.name p) := by
  change e.name (A.axes.name (e.geometry.cells.symm (e.geometry.cells p)))=_
  rw [Equiv.symm_apply_apply]

theorem rotate_active (A : StrongTracks I) {W H : ℕ} (e : AxisIsometry I.width I.height W H)
    (p : PushFS.Cell I.width I.height) (hp : (A.rotate e).axes.name (e.geometry.cells p)≠.outside) :
    A.axes.name p≠.outside := by
  rw [A.rotate_name] at hp
  exact fun he=>hp ((e.outside _).mpr he)

end StrongTracks

def chainStrong (n : ℕ) (hn : 2301≤n) (a b : Bool) : StrongTracks (Chain.puzzle n hn a b) where
  axes:=Chain.axisTracks n hn a b
  strong p q hp hd:=by
    have hrow : p.2.val=10 := by by_contra he; exact hp (by simp [Chain.axisTracks,Chain.axisName,he])
    have hq:=Chain.displacement_row n hn _ hrow hd
    exact Or.inl (by simp [Chain.axisTracks,Chain.axisName,hrow,hq])
  sparse p hp q hq d:=by
    change p∈Chain.boxes n hn (Chain.uniform n b) at hp
    change q∈Chain.boxes n hn (Chain.uniform n b) at hq
    rw [Chain.boxes_image] at hp hq
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hq
    exact Chain.sparse_targets n hn b i j d

def normalStrong (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    StrongTracks (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle where
  axes:=Polyline.L.axisTracks m n hm hn a b
  strong _ _ hp hd:=Polyline.L.actual_strong m n hm hn a b hp hd
  sparse:=Polyline.L.actual_sparse m n hm hn a b

def outStrong (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    StrongTracks (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).puzzle where
  axes:=Out.axisTracks m n hm hn a b
  strong p q hp hd:=by
    change Displacement (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).board p q at hd
    rw [Out.board_eq] at hd
    exact Out.strong_displacement m n hm hn _ hp hd
  sparse p hp q hq d:=by
    change p∈(Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).board.goals at hp
    change q∈(Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).board.goals at hq
    rw [Out.goals_eq] at hp hq
    exact Out.sparse_targets m n hm hn b hp hq d

def inStrong (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    StrongTracks (In.atlas m n hm hn (In.uniform a) (In.uniform b)).puzzle where
  axes:=In.axisTracks m n hm hn a b
  strong p q hp hd:=by
    change Displacement (In.atlas m n hm hn (In.uniform a) (In.uniform b)).board p q at hd
    rw [In.board_eq] at hd
    exact In.strong_displacement m n hm hn _ hp hd
  sparse p hp q hq d:=by
    change p∈(In.atlas m n hm hn (In.uniform a) (In.uniform b)).board.goals at hp
    change q∈(In.atlas m n hm hn (In.uniform a) (In.uniform b)).board.goals at hq
    rw [In.goals_eq] at hp hq
    exact In.sparse_targets m n hm hn b hp hq d

/-- These are classifiers of the complete true native wall union, including all helper inventories and each D4 operation. -/
def baseStrong (k : Kind) (a b : Bool) : StrongTracks (base k a b) :=
  match k with
  | .east=>chainStrong 200000 (by decide) a b
  | .west=>(chainStrong 200000 (by decide) a b).rotate (AxisIsometry.reflectX _ _)
  | .south=>((chainStrong 198061 (by decide) a b).rotate (AxisIsometry.transpose _ _)).rotate (AxisIsometry.reflectX _ _)
  | .westSouth=>normalStrong 99970 98999 (by decide) (by decide) a b
  | .eastSouth=>(outStrong 99970 98979 (by decide) (by decide) a b).rotate (AxisIsometry.reflectX _ _)
  | .southEast=>((inStrong 98981 99969 (by decide) (by decide) a b).rotate (AxisIsometry.reflectX _ _)).rotate (AxisIsometry.transpose _ _)
  | .southWest=>(((normalStrong 99001 99969 (by decide) (by decide) a b).rotate (AxisIsometry.reflectX _ _)).rotate
      (AxisIsometry.transpose _ _)).rotate (AxisIsometry.reflectX _ _)

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
