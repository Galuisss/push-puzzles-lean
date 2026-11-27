/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AxisCharts

/-! Static displacement reflection at active chart ends aligned with the actual ambient boundary. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


variable {w h W H : ℕ}

/-- A local source can meet a chart edge when that edge is the actual finite-board edge. -/
def BoundaryAligned (dx dy : ℕ) (p : PushFS.Cell w h) : Prop :=
  (p.1.val=0→dx=0) ∧ (p.1.val+1=w→dx+w=W) ∧
    (p.2.val=0→dy=0) ∧ (p.2.val+1=h→dy+h=H)

private theorem neighbor_aligned (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H)
    {p : PushFS.Cell w h} (hp : BoundaryAligned (W:=W) (H:=H) dx dy p)
    {d : Direction} {q : PushFS.Cell W H}
    (hq : Adjacent d ((GridEmbedding.translate dx dy hx hy).cells p) q) :
    ∃p' : PushFS.Cell w h, Adjacent d p p' ∧ (GridEmbedding.translate dx dy hx hy).cells p'=q := by
  change Adjacent d (⟨dx+p.1.val,by have:=p.1.isLt; omega⟩,⟨dy+p.2.val,by have:=p.2.isLt; omega⟩) q at hq
  have hb : q.1.val≤dx+p.1.val+1 ∧ dx+p.1.val≤q.1.val+1 ∧
      q.2.val≤dy+p.2.val+1 ∧ dy+p.2.val≤q.2.val+1 := by
    cases d <;> simp only [Adjacent,Fin.ext_iff] at hq <;> omega
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  have hqx:=q.1.isLt
  have hqy:=q.2.isLt
  have hxl : dx≤q.1.val := by
    by_contra he
    have hp0 : p.1.val=0 := by omega
    have hh:=hp.1 hp0
    omega
  have hxh : q.1.val<dx+w := by
    by_contra he
    have hp0 : p.1.val+1=w := by omega
    have hh:=hp.2.1 hp0
    omega
  have hyl : dy≤q.2.val := by
    by_contra he
    have hp0 : p.2.val=0 := by omega
    have hh:=hp.2.2.1 hp0
    omega
  have hyh : q.2.val<dy+h := by
    by_contra he
    have hp0 : p.2.val+1=h := by omega
    have hh:=hp.2.2.2 hp0
    omega
  let p' : PushFS.Cell w h := (⟨q.1.val-dx,by omega⟩,⟨q.2.val-dy,by omega⟩)
  refine ⟨p',?_,?_⟩
  · cases d <;> simp only [Adjacent,Fin.ext_iff] at hq ⊢ <;> dsimp only [p'] <;> omega
  · apply Prod.ext <;> apply Fin.ext
    · change dx+(q.1.val-dx)=q.1.val
      omega
    · change dy+(q.2.val-dy)=q.2.val
      omega

theorem displacement_aligned (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H)
    {B : Board w h} {ambient : Board W H}
    (hw : (GridEmbedding.translate dx dy hx hy).WallsAgree B ambient)
    {p : PushFS.Cell w h} (hp : BoundaryAligned (W:=W) (H:=H) dx dy p)
    {q : PushFS.Cell W H}
    (hd : Displacement ambient ((GridEmbedding.translate dx dy hx hy).cells p) q) :
    ∃q' : PushFS.Cell w h, (GridEmbedding.translate dx dy hx hy).cells q'=q ∧ Displacement B p q' := by
  obtain ⟨hpw,d,rear,hr,hq,hrw,hqw⟩:=hd
  obtain ⟨rear',hr',heRear⟩:=neighbor_aligned dx dy hx hy hp hr.reverse
  obtain ⟨q',hq',heq⟩:=neighbor_aligned dx dy hx hy hp hq
  refine ⟨q',heq,fun h=>hpw ((hw p).mpr h),d,rear',?_,hq',?_,?_⟩
  · simpa only [Direction.opposite_opposite] using hr'.reverse
  · exact fun h=>hrw (heRear ▸ (hw rear').mpr h)
  · exact fun h=>hqw (heq ▸ (hw q').mpr h)

/-- The actual padded name is outside away from the true rectangular source chart. -/
noncomputable def paddedName (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H)
    (name : PushFS.Cell w h→AxisTrack) : PushFS.Cell W H→AxisTrack :=
  Function.extend (GridEmbedding.translate dx dy hx hy).cells
    (AxisTrack.shift dx dy ∘ name) (fun _=>.outside)

theorem paddedName_apply (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H)
    (name : PushFS.Cell w h→AxisTrack) (p : PushFS.Cell w h) :
    paddedName dx dy hx hy name ((GridEmbedding.translate dx dy hx hy).cells p)=AxisTrack.shift dx dy (name p) :=
  (GridEmbedding.translate dx dy hx hy).cells.injective.extend_apply _ _ _

theorem paddedName_outside (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H)
    (name : PushFS.Cell w h→AxisTrack) (p : PushFS.Cell W H)
    (hp : ¬∃q, (GridEmbedding.translate dx dy hx hy).cells q=p) :
    paddedName dx dy hx hy name p=.outside := Function.extend_apply' _ _ _ hp

/-- All actual ambient edges inherit the finite source classifier, including aligned board endpoints. -/
noncomputable def paddedClassifier (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H)
    {B : Board w h} {ambient : Board W H} (C : AxisClassifier B)
    (hw : (GridEmbedding.translate dx dy hx hy).WallsAgree B ambient)
    (aligned : ∀p, C.name p≠.outside→BoundaryAligned (W:=W) (H:=H) dx dy p) : AxisClassifier ambient where
  name:=paddedName dx dy hx hy C.name
  supported p:=by
    classical
    by_cases hp : ∃q, (GridEmbedding.translate dx dy hx hy).cells q=p
    · obtain ⟨q,rfl⟩:=hp
      rw [paddedName_apply]
      exact AxisTrack.shift_supported dx dy hx hy (C.supported q)
    · rw [paddedName_outside dx dy hx hy C.name p hp]
      trivial
  displacement p q hd:=by
    classical
    by_cases hp : paddedName dx dy hx hy C.name p=.outside
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside hp)
    · obtain ⟨p',rfl⟩ : ∃p', (GridEmbedding.translate dx dy hx hy).cells p'=p := by
        by_contra he
        exact hp (paddedName_outside dx dy hx hy C.name p he)
      have hpa : C.name p'≠.outside := by
        intro he
        apply hp
        rw [paddedName_apply,he]
        rfl
      obtain ⟨q',rfl,hd'⟩:=displacement_aligned dx dy hx hy hw (aligned p' hpa) hd
      rw [paddedName_apply,paddedName_apply]
      rcases C.displacement p' q' hd' with he|hl
      · exact Or.inl (congrArg (AxisTrack.shift dx dy) he)
      · exact Or.inr (by simpa only [AxisTrack.level_shift] using hl)

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
