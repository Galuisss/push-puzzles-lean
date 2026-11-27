/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.ComponentTracks
public import PushFS.Gadgets.Wires.Soundness.Pair
public import PushFS.Gadgets.Gates.Soundness.Bounds

/-! Successful physical trajectories need only supported SCC names for line, order, gap and barriers. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness.Successful

variable {I : Instance} {Label : Type} [Fintype Label] {M : SlotMatching I Label}
    {S final : LabelledState Label I.width I.height}

theorem line_component (h : Successful M S final) (A : ComponentTracks I) (axis : Bool) (line : ℕ)
    (i : Label) (hi : A.name (M.source i) = lineTag axis line) : cross axis (S.position i) = line := by
  have he := A.name_eq_of_component_eq (h.component i)
  have hs := A.supported (S.position i)
  rw [←he,hi] at hs
  cases axis <;> exact hs

private theorem order_component (h : Successful M S final) (A : ComponentTracks I) (axis : Bool)
    (line : ℕ)
    (i j : Label) (hi : A.name (M.source i) = lineTag axis line)
    (hj : A.name (M.source j) = lineTag axis line)
    (hij : coord axis (M.source i) < coord axis (M.source j)) :
    coord axis (S.position i) < coord axis (S.position j) := by
  obtain ⟨hb,ha,hsol⟩ := h
  induction hb with
  | refl => exact hij
  | @tail U V hr hs ih =>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    exact step_order axis hs i j
      ((hv.line_component A axis line i hi).trans (hv.line_component A axis line j hj).symm)
      (ih (ha.head hs))

theorem gap_component (h : Successful M S final) (cert : Certificate I) (A : ComponentTracks I)
    (axis : Bool) (line : ℕ) (i j : Label)
    (hi : A.name (M.source i) = lineTag axis line) (hj : A.name (M.source j) = lineTag axis line)
    (hc : PushFS.component I.board (M.source i) = PushFS.component I.board (M.source j))
    (hij : coord axis (M.source i) < coord axis (M.source j)) :
    coord axis (S.position i)+2 ≤ coord axis (S.position j) := by
  have ho := h.order_component A axis line i j hi hj hij
  have hrowi := h.line_component A axis line i hi
  have hrowj := h.line_component A axis line j hj
  by_contra he
  have hadj : ∃d, Adjacent d (S.position i) (S.position j) := by
    cases axis
    · refine ⟨.south,Fin.ext ?_,?_⟩ <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at * <;> omega
    · refine ⟨.east,?_,Fin.ext ?_⟩ <;> simp only [coord,cross,↓reduceIte] at * <;> omega
  apply cert.no_adjacentPair
    (h.before.forget.mono (cap' := none) (fun _ _ => trivial))
    (h.after.forget.mono (cap' := none) (fun _ _ => trivial)) h.solved
  exact ⟨S.position i,S.position_mem i,S.position j,S.position_mem j,
    (h.component i).symm,(h.component j).symm.trans hc.symm,hadj⟩

private theorem avoids_component (h : Successful M S final) (A : ComponentTracks I) (i : Label)
    (p : Cell I.width I.height)
    (hne : A.name p ≠ A.name (M.source i)) : S.position i ≠ p := by
  intro he
  have hn := A.name_eq_of_component_eq (h.component i)
  exact hne (by rw [he] at hn; exact hn.symm)

private theorem cell_ext (axis : Bool) {p q : Cell I.width I.height}
    (hc : coord axis p = coord axis q) (ht : cross axis p = cross axis q) : p = q := by
  cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at * <;>
    exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))

theorem above_barrier_component (h : Successful M S final) (A : ComponentTracks I) (axis : Bool) (line : ℕ)
    (i : Label) (hi : A.name (M.source i) = lineTag axis line)
    (p : Cell I.width I.height) (hcross : cross axis p = line)
    (hne : A.name p ≠ A.name (M.source i))
    (hstart : coord axis p < coord axis (M.source i)) : coord axis p < coord axis (S.position i) := by
  obtain ⟨hb,ha,hsol⟩ := h
  induction hb with
  | refl => exact hstart
  | @tail U V hr hs ih =>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    have hcoordne : coord axis (V.position i) ≠ coord axis p := by
      intro he
      exact hv.avoids_component A i p hne
        (cell_ext axis he ((hv.line_component A axis line i hi).trans hcross.symm))
    have hbound := step_coord_bound hs axis i
    have hh := ih (ha.head hs)
    omega

theorem below_barrier_component (h : Successful M S final) (A : ComponentTracks I) (axis : Bool) (line : ℕ)
    (i : Label) (hi : A.name (M.source i) = lineTag axis line)
    (p : Cell I.width I.height) (hcross : cross axis p = line)
    (hne : A.name p ≠ A.name (M.source i))
    (hstart : coord axis (M.source i) < coord axis p) : coord axis (S.position i) < coord axis p := by
  obtain ⟨hb,ha,hsol⟩ := h
  induction hb with
  | refl => exact hstart
  | @tail U V hr hs ih =>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    have hcoordne : coord axis (V.position i) ≠ coord axis p := by
      intro he
      exact hv.avoids_component A i p hne
        (cell_ext axis he ((hv.line_component A axis line i hi).trans hcross.symm))
    have hbound := step_coord_bound hs axis i
    have hh := ih (ha.head hs)
    omega

private theorem pair_shape_component (h : Successful M S final) (A : ComponentTracks I) (y : ℕ)
    (i j : Label)
    (hi : A.name (M.source i) = .horizontal y) (hj : A.name (M.source j) = .horizontal y)
    (hij : (M.source i).1.val < (M.source j).1.val) : Shape y (pair S i j) :=
  ⟨S.position_mem i,S.position_mem j,h.line_component A true y i hi,h.line_component A true y j hj,
    h.order_component A true y i j hi hj hij⟩

theorem strip_good_component (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (A : ComponentTracks I) (lo hi y : ℕ) (i j : Label)
    (hw : StripWalls I.board lo hi y)
    (hirow : A.name (M.source i) = .horizontal y) (hjrow : A.name (M.source j) = .horizontal y)
    (hij : (M.source i).1.val < (M.source j).1.val)
    (hstart : (M.source i).1.val+1 < lo ∨ hi+1 < (M.source j).1.val)
    (hfinish : (M.target i).1.val+1 < lo ∨ hi+1 < (M.target j).1.val) : Good lo hi (pair S i j) := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) : GeometricStep I.board y (pair U i j) (pair V i j) :=
    ⟨hu.pair_shape_component A y i j hirow hjrow hij,hv.pair_shape_component A y i j hirow hjrow hij,pair_tracked hs i j⟩
  have hb := map_successful (fun U => pair U i j) h.before (.refl) h.after h.solved hstep
  have ha := map_successful (fun U => pair U i j) h.after h.before (.refl) h.solved hstep
  apply good_on_successful_path (initial := pair M.initialLabelled i j)
    (S := pair S i j) (final := pair final i j) hw hstart (hbefore := hb) (hafter := ha)
  have ht := h.target ho cert
  simpa only [Good,pair,ht] using hfinish

end PushPuzzle.PushFS.Gadgets.Wires.Soundness.Successful
