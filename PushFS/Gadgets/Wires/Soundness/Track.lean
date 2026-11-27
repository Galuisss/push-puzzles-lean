/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AxisTracks
public import PushFS.LabelOrder

/-! Physical identities, tracks and spacing at every point of an actual successful trajectory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness


variable {I : Instance} {Label : Type} [Fintype Label]

/-- The selected state lies on one real physical trajectory ending in unlabelled storage. -/
structure Successful (M : SlotMatching I Label)
    (S final : LabelledState Label I.width I.height) : Prop where
  before : LabelledState.Reachable I.board M.initialLabelled S
  after : LabelledState.Reachable I.board S final
  solved : final.state.boxes = I.board.goals

namespace Successful

variable {M : SlotMatching I Label} {S final : LabelledState Label I.width I.height}

/-- Every physical label keeps its initial static component. -/
theorem component (h : Successful M S final) (i : Label) :
    PushFS.component I.board (M.source i) = PushFS.component I.board (S.position i) :=
  h.before.component_eq
    (potential_eq_on_successful_path M.componentBalanced h.before.forget h.after.forget h.solved).symm i

/-- Exact terminal physical identities follow from the compiler's static order contract. -/
theorem target (h : Successful M S final) (ho : M.Ordered) (cert : Certificate I) :
    final.position = M.target := ho.matches_target cert (h.before.trans h.after) h.solved

end Successful

/-- Coordinate along the selected horizontal/vertical axis. -/
def coord (axis : Bool) (p : Cell I.width I.height) : ℕ := if axis then p.1.val else p.2.val
/-- Actual transverse coordinate. -/
def cross (axis : Bool) (p : Cell I.width I.height) : ℕ := if axis then p.2.val else p.1.val
/-- The coordinate-valued rail name for the chosen axis. -/
def lineTag (axis : Bool) (line : ℕ) : AxisTrack := if axis then .horizontal line else .vertical line

namespace Successful

variable {M : SlotMatching I Label} {S final : LabelledState Label I.width I.height}

/-- Track classification supplies the actual intermediate row/column, without a Shape premise. -/
theorem line (h : Successful M S final) (A : AxisTracks I) (axis : Bool) (line : ℕ)
    (i : Label) (hi : A.name (M.source i) = lineTag axis line) : cross axis (S.position i) = line := by
  have he := A.toStaticTracks.name_eq_of_component_eq (h.component i)
  change A.name (M.source i) = A.name (S.position i) at he
  have hs := A.supported (S.position i)
  rw [← he,hi] at hs
  cases axis <;> exact hs

end Successful

private theorem coord_ext {p q : Cell I.width I.height} (axis : Bool)
    (hc : coord axis p = coord axis q) (ht : cross axis p = cross axis q) : p = q := by
  cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at * <;>
    exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))

theorem step_order {S T : LabelledState Label I.width I.height}
    (axis : Bool) (hs : LabelledState.Step I.board S T) (i j : Label)
    (hcross : cross axis (T.position i) = cross axis (T.position j))
    (horder : coord axis (S.position i) < coord axis (S.position j)) :
    coord axis (T.position i) < coord axis (T.position j) := by
  have hij : i ≠ j := by intro he; subst j; omega
  have hne : coord axis (T.position i) ≠ coord axis (T.position j) := by
    intro he
    exact hij (T.injective (coord_ext axis he hcross))
  obtain ⟨d,_,hwalk|hpush⟩ := hs
  · simpa only [hwalk.2] using horder
  · obtain ⟨q,_,hq,_,_,hpos⟩ := hpush
    have hbound : coord axis q ≤ coord axis T.state.player+1 ∧
        coord axis T.state.player ≤ coord axis q+1 := by
      cases axis <;> cases d <;> simp only [coord,Adjacent,Bool.false_eq_true,↓reduceIte] at * <;>
        constructor <;> omega
    by_cases hi : S.position i = T.state.player
    · have hj : S.position j ≠ T.state.player := fun hj => hij (S.injective (hi.trans hj.symm))
      simp only [hpos,Function.comp_apply,hi,shiftBox_source,shiftBox_other hj] at hne ⊢
      rw [hi] at horder
      omega
    · by_cases hj : S.position j = T.state.player
      · simp only [hpos,Function.comp_apply,hj,shiftBox_source,shiftBox_other hi] at hne ⊢
        rw [hj] at horder
        omega
      · simpa only [hpos,Function.comp_apply,shiftBox_other hi,shiftBox_other hj] using horder

namespace Successful

variable {M : SlotMatching I Label} {S final : LabelledState Label I.width I.height}

/-- Actual single-box motion cannot overtake another physical box on the same rail. -/
theorem order (h : Successful M S final) (A : AxisTracks I) (axis : Bool) (line : ℕ)
    (i j : Label) (hi : A.name (M.source i) = lineTag axis line)
    (hj : A.name (M.source j) = lineTag axis line)
    (hij : coord axis (M.source i) < coord axis (M.source j)) :
    coord axis (S.position i) < coord axis (S.position j) := by
  obtain ⟨hb,ha,hsol⟩ := h
  induction hb with
  | refl => exact hij
  | @tail U V hr hs ih =>
    have hu : Successful M U final := ⟨hr,ha.head hs,hsol⟩
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    exact step_order axis hs i j ((hv.line A axis line i hi).trans (hv.line A axis line j hj).symm)
      (ih (ha.head hs))

/-- On a successful C1–C3 path, ordered labels in the same source SCC have a full empty-cell gap. -/
theorem gap (h : Successful M S final) (cert : Certificate I) (A : AxisTracks I)
    (axis : Bool) (line : ℕ) (i j : Label)
    (hi : A.name (M.source i) = lineTag axis line) (hj : A.name (M.source j) = lineTag axis line)
    (hc : PushFS.component I.board (M.source i) = PushFS.component I.board (M.source j))
    (hij : coord axis (M.source i) < coord axis (M.source j)) :
    coord axis (S.position i)+2 ≤ coord axis (S.position j) := by
  have ho := h.order A axis line i j hi hj hij
  have hrowi := h.line A axis line i hi
  have hrowj := h.line A axis line j hj
  by_contra he
  have hadj : ∃d, Adjacent d (S.position i) (S.position j) := by
    cases axis
    · refine ⟨.south,Fin.ext ?_,?_⟩ <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at * <;> omega
    · refine ⟨.east,?_,Fin.ext ?_⟩ <;> simp only [coord,cross,↓reduceIte] at * <;> omega
  apply cert.no_adjacentPair
    (h.before.forget.mono (cap' := none) (fun _ _ => trivial))
    (h.after.forget.mono (cap' := none) (fun _ _ => trivial)) h.solved
  exact ⟨S.position i,S.position_mem i,S.position j,S.position_mem j,
    (h.component i).symm, (h.component j).symm.trans hc.symm,hadj⟩

end Successful

/-- One physical identity changes its axial coordinate by at most one per actual move. -/
theorem step_coord_bound {S T : LabelledState Label I.width I.height}
    (hs : LabelledState.Step I.board S T) (axis : Bool) (i : Label) :
    coord axis (S.position i) ≤ coord axis (T.position i)+1 ∧
      coord axis (T.position i) ≤ coord axis (S.position i)+1 := by
  obtain ⟨d,_,hw|hp⟩ := hs
  · simp only [hw.2]
    omega
  · obtain ⟨q,_,hq,_,_,ht⟩ := hp
    by_cases hi : S.position i = T.state.player
    · rw [ht]
      simp only [Function.comp_apply,hi,shiftBox_source]
      cases axis <;> cases d <;> simp only [coord,Adjacent,Bool.false_eq_true,↓reduceIte] at * <;>
        constructor <;> omega
    · simp only [ht,Function.comp_apply,shiftBox_other hi]
      omega

namespace Successful
variable {M : SlotMatching I Label} {S final : LabelledState Label I.width I.height}

/-- A different named corner cannot be occupied by a rail identity on a successful path. -/
theorem avoids (h : Successful M S final) (A : AxisTracks I) (i : Label) (p : Cell I.width I.height)
    (hne : A.name p ≠ A.name (M.source i)) : S.position i ≠ p := by
  intro he
  have hn := A.toStaticTracks.name_eq_of_component_eq (h.component i)
  exact hne (by simpa only [AxisTracks.toStaticTracks,he] using hn.symm)

/-- A one-cell corner of a different track name prevents a physical identity from crossing its coordinate. -/
theorem above_barrier (h : Successful M S final) (A : AxisTracks I) (axis : Bool) (line : ℕ)
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
      exact hv.avoids A i p hne (coord_ext axis he ((hv.line A axis line i hi).trans hcross.symm))
    have hbound := step_coord_bound hs axis i
    have hh := ih (ha.head hs)
    omega

end Successful

/-- Map a specified subpath using properties derived from its surrounding real successful path. -/
theorem map_successful {M : SlotMatching I Label} {S T final : LabelledState Label I.width I.height}
    {α : Type} (f : LabelledState Label I.width I.height → α) {R : α → α → Prop}
    (hr : LabelledState.Reachable I.board S T)
    (hbefore : LabelledState.Reachable I.board M.initialLabelled S)
    (hafter : LabelledState.Reachable I.board T final) (hsol : final.state.boxes = I.board.goals)
    (hstep : ∀ U V, Successful M U final → Successful M V final →
      LabelledState.Step I.board U V → R (f U) (f V)) :
    Relation.ReflTransGen R (f S) (f T) := by
  induction hr with
  | refl => exact .refl
  | @tail U V hr hs ih =>
    exact (ih (hafter.head hs)).tail
      (hstep U V ⟨hbefore.trans hr,hafter.head hs,hsol⟩ ⟨hbefore.trans (hr.tail hs),hafter,hsol⟩ hs)

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
