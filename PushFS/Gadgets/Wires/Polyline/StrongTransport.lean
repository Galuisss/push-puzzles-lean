/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AxisIsometry
public import PushFS.Gadgets.Wires.Polyline.Reorientation
public import PushFS.Gadgets.Wires.Polyline.LOrder

/-! Actual strong rail/sink stencils give full storage-track certificates in every D4 orientation. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


variable {I : Instance}

def axisClassifier (A : AxisTracks I) : AxisClassifier I.board := ⟨A.name,A.supported,A.displacement⟩

/-- Supported strong stencils and actual sparse goal cells survive complete-board reorientation. -/
def reorientedAxisTracks (A : AxisTracks I)
    (hstrong : ∀ p q, A.name p≠.outside → Displacement I.board p q → (A.name p).Strong (A.name q))
    (hsparse : ∀ p∈I.board.goals, ∀ q∈I.board.goals, ∀d, ¬Adjacent d p q)
    {W H : ℕ} (e : AxisIsometry I.width I.height W H) : AxisTracks (e.geometry.reorientInstance I) where
  name p := e.name (A.name (e.geometry.cells.symm p))
  supported p := by
    have hh := e.supported (e.geometry.cells.symm p) _ (A.supported _)
    change (e.name (A.name (e.geometry.cells.symm p))).Supports p
    have he : e.geometry.cells (e.geometry.cells.symm p)=p := e.geometry.cells.apply_symm_apply p
    rw [he] at hh
    exact hh
  active p hp := by
    change p∈I.initial.boxes.map e.geometry.cells.toEmbedding at hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    change e.name (A.name (e.geometry.cells.symm (e.geometry.cells q)))≠.outside
    simp only [Equiv.symm_apply_apply]
    exact fun hh => A.active q hq ((e.outside _).mp hh)
  displacement p q hd := (e.classifier (axisClassifier A) hstrong).displacement p q hd
  separated p hp q hq _ d := by
    change p∈I.board.goals.map e.geometry.cells.toEmbedding at hp
    change q∈I.board.goals.map e.geometry.cells.toEmbedding at hq
    obtain ⟨p,hpLocal,rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q,hqLocal,rfl⟩ := Finset.mem_map.mp hq
    intro ha
    change Adjacent d (e.geometry.cells p) (e.geometry.cells q) at ha
    exact hsparse p hpLocal q hqLocal (e.geometry.directions.symm d)
      ((e.geometry.adjacent _ _ _).mp (by simpa only [Equiv.apply_symm_apply] using ha))

namespace L

variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

theorem actual_strong (a b : Bool) {p q : C m n} (hp : (axisTracks m n hm hn a b).name p≠.outside)
    (hd : Displacement (atlas m n hm hn (uniform a) (uniform b)).puzzle.board p q) :
    ((axisTracks m n hm hn a b).name p).Strong ((axisTracks m n hm hn a b).name q) := by
  change Displacement (atlas m n hm hn (uniform a) (uniform b)).board p q at hd
  rw [board_eq] at hd
  exact strong_displacement m n hm hn _ hp hd

theorem actual_sparse (a b : Bool) (p : C m n) (hp : p∈(atlas m n hm hn (uniform a) (uniform b)).puzzle.board.goals)
    (q : C m n) (hq : q∈(atlas m n hm hn (uniform a) (uniform b)).puzzle.board.goals) (d : Direction) : ¬Adjacent d p q := by
  change p∈(atlas m n hm hn (uniform a) (uniform b)).board.goals at hp
  change q∈(atlas m n hm hn (uniform a) (uniform b)).board.goals at hq
  rw [goals_eq] at hp hq
  exact sparse_targets m n hm hn b hp hq d

/-- Every rotated/reflected complete L board inherits its genuine supported track certificate. -/
def orientedAxisTracks (a b : Bool) {W H : ℕ} (e : AxisIsometry (m+43) (n+44) W H) :
    AxisTracks (e.geometry.reorientInstance (atlas m n hm hn (uniform a) (uniform b)).puzzle) :=
  reorientedAxisTracks (axisTracks m n hm hn a b) (fun _ _ hp hd => actual_strong m n hm hn a b hp hd)
    (actual_sparse m n hm hn a b) e

/-- All C1–C3 conclusions remain true after every supplied physical grid isometry. -/
theorem oriented_certificate (a b : Bool) {W H : ℕ} (e : AxisIsometry (m+43) (n+44) W H) :
    Certificate (e.geometry.reorientInstance (atlas m n hm hn (uniform a) (uniform b)).puzzle) :=
  (orientedAxisTracks m n hm hn a b e).toStaticTracks.certificate
    ((atlas m n hm hn (uniform a) (uniform b)).slotMatching.reorient e.geometry)

end L
end PushPuzzle.PushFS.Gadgets.Wires.Polyline
