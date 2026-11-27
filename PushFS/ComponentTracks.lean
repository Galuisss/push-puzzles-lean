/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.AxisIsometry
public import PushFS.AxisTracks

/-! Coordinate-supported SCC names transport through every rectangle orientation. -/

@[expose] public section
namespace PushPuzzle.PushFS

/-- Successful-path readers need supported names constant on SCCs. -/
structure ComponentTracks (I : Instance) where
  name : Cell I.width I.height → AxisTrack
  supported : ∀ p, (name p).Supports p
  active : ∀ p ∈ I.initial.boxes, name p ≠ .outside
  component : ∀ p q, SameComponent I.board p q → name p = name q

def AxisTracks.componentTracks {I : Instance} (A : AxisTracks I) : ComponentTracks I where
  name := A.name
  supported := A.supported
  active := A.active
  component _ _ h := A.toStaticTracks.name_eq_of_component_eq (component_eq_iff.mpr h)

namespace ComponentTracks

theorem name_eq_of_component_eq {I : Instance} (A : ComponentTracks I) {p q : Cell I.width I.height}
    (h : PushFS.component I.board p = PushFS.component I.board q) : A.name p = A.name q :=
  A.component p q (component_eq_iff.mp h)

theorem horizontal_of_active_component {I : Instance} (A : ComponentTracks I) {p q : Cell I.width I.height}
    (h : SameComponent I.board p q) (hne : p.1.val ≠ q.1.val) (ha : A.name p ≠ .outside) :
    A.name p = .horizontal p.2.val := by
  have hp := A.supported p
  have hq := A.supported q
  rw [←A.component p q h] at hq
  cases hn : A.name p with
  | outside => exact False.elim (ha hn)
  | horizontal row =>
    simp only [hn,AxisTrack.Supports] at hp
    exact congrArg AxisTrack.horizontal hp.symm
  | vertical col =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.trans hq.symm))
  | sink x y =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.1.trans hq.1.symm))

theorem vertical_of_active_component {I : Instance} (A : ComponentTracks I) {p q : Cell I.width I.height}
    (h : SameComponent I.board p q) (hne : p.2.val ≠ q.2.val) (ha : A.name p ≠ .outside) :
    A.name p = .vertical p.1.val := by
  have hp := A.supported p
  have hq := A.supported q
  rw [←A.component p q h] at hq
  cases hn : A.name p with
  | outside => exact False.elim (ha hn)
  | horizontal row =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.trans hq.symm))
  | vertical col =>
    simp only [hn,AxisTrack.Supports] at hp
    exact congrArg AxisTrack.vertical hp.symm
  | sink x y =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.2.trans hq.2.symm))

/-- SCC names, unlike a fixed horizontal/vertical ranking, survive every axis isometry. -/
def reorient {I : Instance} (A : ComponentTracks I) {W H : ℕ} (e : AxisIsometry I.width I.height W H) :
    ComponentTracks (e.geometry.reorientInstance I) where
  name p := e.name (A.name (e.geometry.cells.symm p))
  supported p := by
    have h := e.supported (e.geometry.cells.symm p) _ (A.supported _)
    rw [e.geometry.cells.apply_symm_apply p] at h
    exact h
  active p hp := by
    change p ∈ I.initial.boxes.map e.geometry.cells.toEmbedding at hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    change e.name (A.name (e.geometry.cells.symm (e.geometry.cells q))) ≠ .outside
    rw [e.geometry.cells.symm_apply_apply q]
    exact fun h => A.active q hq ((e.outside _).mp h)
  component p q h := by
    change SameComponent (e.geometry.board I.board) p q at h
    obtain ⟨p,rfl⟩ := e.geometry.cells.surjective p
    obtain ⟨q,rfl⟩ := e.geometry.cells.surjective q
    rw [e.geometry.cells.symm_apply_apply p,e.geometry.cells.symm_apply_apply q]
    exact congrArg e.name (A.component p q ((e.geometry.sameComponent_iff I.board p q).mp h))

theorem reorient_sink {I : Instance} (A : ComponentTracks I) {W H : ℕ}
    (e : AxisIsometry I.width I.height W H) (p : Cell I.width I.height)
    (hp : A.name p = .sink p.1.val p.2.val) :
    (A.reorient e).name (e.geometry.cells p) =
      .sink (e.geometry.cells p).1.val (e.geometry.cells p).2.val := by
  have hk : ((A.reorient e).name (e.geometry.cells p)).Sink := by
    change (e.name (A.name (e.geometry.cells.symm (e.geometry.cells p)))).Sink
    rw [e.geometry.cells.symm_apply_apply p,hp]
    exact e.sink _ trivial
  have hs := (A.reorient e).supported (e.geometry.cells p)
  cases hn : (A.reorient e).name (e.geometry.cells p) <;> simp only [hn,AxisTrack.Sink] at hk
  simp only [hn,AxisTrack.Supports] at hs
  exact congrArg₂ AxisTrack.sink hs.1.symm hs.2.symm

end ComponentTracks
end PushPuzzle.PushFS
