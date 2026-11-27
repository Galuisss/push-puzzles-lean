/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Pair

/-! A real source SCC with two different axial coordinates determines its physical row or column through C2 alone. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Soundness

variable {I : Instance} {L : Type} [Fintype L]

/-- Pure static witnesses locating one actual occupied source component on a physical rail. -/
structure SourceRail (M : SlotMatching I L) (axis : Bool) (line : ℕ) where
  anchor : L
  witness : PushFS.Cell I.width I.height
  connected : component I.board witness=component I.board (M.source anchor)
  different : coord axis witness≠coord axis (M.source anchor)
  anchor_cross : cross axis (M.source anchor)=line

namespace SourceRail

variable {M : SlotMatching I L} {axis : Bool} {line : ℕ} (r : SourceRail M axis line)

/-- C2 selects the actual rail orientation from the two distinct static source-component points. -/
private theorem supported (cert : Certificate I) (p : PushFS.Cell I.width I.height)
    (hp : component I.board p=component I.board (M.source r.anchor)) : cross axis p=line := by
  have ha : M.source r.anchor∈I.initial.boxes := by
    rw [←M.source_image]
    exact Finset.mem_map.mpr ⟨r.anchor,Finset.mem_univ _,rfl⟩
  have hl:=cert.linear (M.source r.anchor) ha
  have hcross:=r.anchor_cross
  cases axis
  · rcases hl with hc|hr
    · have hh:=hc p (M.source r.anchor) hp rfl
      change p.1.val=line
      change (M.source r.anchor).1.val=line at hcross
      exact (congrArg Fin.val hh).trans hcross
    · have hh:=hr r.witness (M.source r.anchor) r.connected rfl
      exact False.elim (r.different (congrArg Fin.val hh))
  · rcases hl with hc|hr
    · have hh:=hc r.witness (M.source r.anchor) r.connected rfl
      exact False.elim (r.different (congrArg Fin.val hh))
    · have hh:=hr p (M.source r.anchor) hp rfl
      change p.2.val=line
      change (M.source r.anchor).2.val=line at hcross
      exact (congrArg Fin.val hh).trans hcross

/-- Every physical identity in that real source SCC stays on the same actual row/column on a successful path. -/
theorem current_line {S final : LabelledState L I.width I.height} (h : Successful M S final) (cert : Certificate I)
    (i : L) (hi : component I.board (M.source i)=component I.board (M.source r.anchor)) :
    cross axis (S.position i)=line := r.supported cert _ ((h.component i).symm.trans hi)

end SourceRail

private theorem coord_ext {p q : PushFS.Cell I.width I.height} (axis : Bool)
    (hc : coord axis p=coord axis q) (ht : cross axis p=cross axis q) : p=q := by
  cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at * <;>
    exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))

private theorem step_order {S T : LabelledState L I.width I.height} (axis : Bool)
    (hs : LabelledState.Step I.board S T) (i j : L)
    (hcross : cross axis (T.position i)=cross axis (T.position j))
    (horder : coord axis (S.position i)<coord axis (S.position j)) :
    coord axis (T.position i)<coord axis (T.position j) := by
  have hij : i≠j := by intro he; subst j; omega
  have hne : coord axis (T.position i)≠coord axis (T.position j) := by
    intro he
    exact hij (T.injective (coord_ext axis he hcross))
  obtain ⟨d,_,hw|hp⟩:=hs
  · simpa only [hw.2] using horder
  · obtain ⟨q,_,hq,_,_,hpos⟩:=hp
    have hb : coord axis q≤coord axis T.state.player+1 ∧ coord axis T.state.player≤coord axis q+1 := by
      cases axis <;> cases d <;> simp only [coord,Adjacent,Bool.false_eq_true,↓reduceIte] at * <;> omega
    by_cases hi : S.position i=T.state.player
    · have hj : S.position j≠T.state.player := fun hj=>hij (S.injective (hi.trans hj.symm))
      simp only [hpos,Function.comp_apply,hi,shiftBox_source,shiftBox_other hj] at hne ⊢
      rw [hi] at horder
      omega
    · by_cases hj : S.position j=T.state.player
      · simp only [hpos,Function.comp_apply,hj,shiftBox_source,shiftBox_other hi] at hne ⊢
        rw [hj] at horder
        omega
      · simpa only [hpos,Function.comp_apply,shiftBox_other hi,shiftBox_other hj] using horder

namespace SourceRail

variable {M : SlotMatching I L} {axis : Bool} {line : ℕ} (r : SourceRail M axis line)

private theorem order {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I)
    (i j : L) (hi : component I.board (M.source i)=component I.board (M.source r.anchor))
    (hj : component I.board (M.source j)=component I.board (M.source r.anchor))
    (hij : coord axis (M.source i)<coord axis (M.source j)) :
    coord axis (S.position i)<coord axis (S.position j) := by
  obtain ⟨hb,ha,hsol⟩:=h
  induction hb with
  | refl=>exact hij
  | @tail U V hr hs ih=>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    exact step_order axis hs i j ((r.current_line hv cert i hi).trans (r.current_line hv cert j hj).symm)
      (ih (ha.head hs))

theorem gap {S final : LabelledState L I.width I.height} (h : Successful M S final) (cert : Certificate I)
    (i j : L) (hi : component I.board (M.source i)=component I.board (M.source r.anchor))
    (hj : component I.board (M.source j)=component I.board (M.source r.anchor))
    (hij : coord axis (M.source i)<coord axis (M.source j)) :
    coord axis (S.position i)+2≤coord axis (S.position j) := by
  have ho:=r.order h cert i j hi hj hij
  have hri:=r.current_line h cert i hi
  have hrj:=r.current_line h cert j hj
  by_contra he
  have hadj : ∃d,Adjacent d (S.position i) (S.position j) := by
    cases axis
    · refine ⟨.south,Fin.ext ?_,?_⟩ <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at * <;> omega
    · refine ⟨.east,?_,Fin.ext ?_⟩ <;> simp only [coord,cross,↓reduceIte] at * <;> omega
  apply cert.no_adjacentPair
    (h.before.forget.mono (cap':=none) (fun _ _=>trivial)) (h.after.forget.mono (cap':=none) (fun _ _=>trivial)) h.solved
  exact ⟨S.position i,S.position_mem i,S.position j,S.position_mem j,(h.component i).symm,
    (h.component j).symm.trans (hj.trans hi.symm),hadj⟩

/-- An actual protected horizontal strip has its usual successful-path obstruction using only C1–C3 and static SCC witnesses. -/
theorem strip_good {M : SlotMatching I L} {y : ℕ} (r : SourceRail M true y)
    {S final : LabelledState L I.width I.height} (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (lo hi : ℕ) (i j : L) (hw : StripWalls I.board lo hi y)
    (hiC : component I.board (M.source i)=component I.board (M.source r.anchor))
    (hjC : component I.board (M.source j)=component I.board (M.source r.anchor))
    (hij : (M.source i).1.val<(M.source j).1.val)
    (hstart : (M.source i).1.val+1<lo ∨hi+1<(M.source j).1.val)
    (hfinish : (M.target i).1.val+1<lo ∨hi+1<(M.target j).1.val) : Good lo hi (pair S i j) := by
  have shape U (hu : Successful M U final) : Shape y (pair U i j) :=
    ⟨U.position_mem i,U.position_mem j,r.current_line hu cert i hiC,r.current_line hu cert j hjC,
      r.order hu cert i j hiC hjC hij⟩
  have step U V (hu : Successful M U final) (hv : Successful M V final) (hs : LabelledState.Step I.board U V) :
      GeometricStep I.board y (pair U i j) (pair V i j) := ⟨shape U hu,shape V hv,pair_tracked hs i j⟩
  have hb:=map_successful (fun U=>pair U i j) h.before .refl h.after h.solved step
  have ha:=map_successful (fun U=>pair U i j) h.after h.before .refl h.solved step
  apply good_on_successful_path (initial:=pair M.initialLabelled i j) (S:=pair S i j) hw hstart _ hb ha
  have ht:=h.target ho cert
  simpa only [Good,pair,ht] using hfinish

end SourceRail
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
