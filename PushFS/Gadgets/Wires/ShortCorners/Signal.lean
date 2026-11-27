/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Geometry
public import PushFS.Gadgets.Wires.Catalog.RectImages

/-! Actual guarded-turn and optional flip identities in each complete short corner. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

open Catalog
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def turnLabels (k : Kind) : Fin 29↪Fin (count k) where
  toFun i:=⟨(if inFlip k then 9 else 0)+i.val,by cases k <;> have:=i.isLt <;> simp only [count,inFlip,Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
  inj' _ _ he:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))

def turnEmbedding (k : Kind) : GridEmbedding 45 41 (width k) (height k) :=
  GridEmbedding.translate 0 1 (by cases k <;> decide) (by cases k <;> decide)

private theorem turn_positions : ∀(k : Kind) (phase : Bool) (i : Fin 29),
    (template k).position phase (turnLabels k i)=(turnEmbedding k).cells (Turn.template.position phase i) := by
  decide +kernel

private theorem turn_walls : ∀(k : Kind) (p : Turn.C),
    (template k).wall ((turnEmbedding k).cells p)=Turn.template.wall p := by
  decide +kernel

/-- Every short corner contains this exact 29-box protected turn, including all true core walls. -/
def turnImage (k : Kind) (a b : Bool) : StorageImage (slotMatching k a b) (Turn.checked.slotMatching a b) where
  dx:=0
  dy:=1
  fit_x:=by change 0+45≤width k; cases k <;> decide
  fit_y:=by change 1+41≤height k; cases k <;> decide
  labels:=turnLabels k
  walls p:=by
    let q : Turn.C:=p
    change (turnEmbedding k).cells q∈(template k).walls ↔q∈Turn.template.walls
    exact ((template k).mem_walls _).trans
      ((congrArg (fun b : Bool=>b=true) (turn_walls k q)).to_iff.trans (Turn.template.mem_walls q).symm)
  sources l:=by exact turn_positions k a l
  targets l:=by exact turn_positions k b l

def nearLabels (k : Kind) : Fin 9↪Fin (count k) where
  toFun i:=⟨i.val,by cases k <;> have:=i.isLt <;> simp only [count] <;> omega⟩
  inj' _ _ he:=Fin.ext (congrArg (fun l : Fin (count k)=>l.val) he)

def nearEmbedding (k : Kind) (hk : inFlip k=true) : GridEmbedding 25 21 (width k) (height k) :=
  GridEmbedding.translate 38 0
    (by cases k <;> simp only [inFlip] at hk <;> cases hk <;> decide)
    (by cases k <;> decide)

private theorem near_positions : ∀(k : Kind) (hk : inFlip k=true) (phase : Bool) (i : Fin 9),
    (template k).position phase (nearLabels k i)=
      (nearEmbedding k hk).cells (In.flipIso.cells (Flip.template.position phase i)) := by
  decide +kernel

private theorem near_walls : ∀(k : Kind) (hk : inFlip k=true) (p : Flip.C),
    (template k).wall ((nearEmbedding k hk).cells (In.flipIso.cells p))=Flip.template.wall p := by
  decide +kernel

/-- The input correction is the real reversed nine-box flip in the complete short template. -/
private def nearImage (k : Kind) (hk : inFlip k=true) (a b : Bool) :
    StorageImage (slotMatching k a b) ((Flip.checked.slotMatching a b).reorient In.flipIso) where
  dx:=38
  dy:=0
  fit_x:=by change 38+25≤width k; cases k <;> simp only [inFlip] at hk <;> cases hk <;> decide
  fit_y:=by change 0+21≤height k; cases k <;> decide
  labels:=nearLabels k
  walls p:=by
    obtain ⟨q,rfl⟩:=In.flipIso.cells.surjective p
    change (nearEmbedding k hk).cells (In.flipIso.cells q)∈(template k).walls ↔
      In.flipIso.cells q∈(In.flipIso.board (Flip.template.board (Flip.template.boxes b))).walls
    rw [In.flipIso.mem_walls]
    change _↔q∈Flip.template.walls
    rw [(template k).mem_walls,Flip.template.mem_walls,near_walls]
  sources l:=by exact near_positions k hk a l
  targets l:=by exact near_positions k hk b l

def farLabels (k : Kind) (hk : outFlip k=true) : Fin 9↪Fin (count k) where
  toFun i:=⟨count k-9+i.val,by cases k <;> simp only [outFlip] at hk <;> cases hk <;> have:=i.isLt <;> simp only [count] <;> omega⟩
  inj' _ _ he:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))

def farEmbedding (k : Kind) (hk : outFlip k=true) : GridEmbedding 21 25 (width k) (height k) :=
  GridEmbedding.translate 0 39 (by cases k <;> decide)
    (by cases k <;> simp only [outFlip] at hk <;> cases hk <;> decide)

private theorem far_positions : ∀(k : Kind) (hk : outFlip k=true) (phase : Bool) (i : Fin 9),
    (template k).position phase (farLabels k hk i)=
      (farEmbedding k hk).cells (Out.flipIso.cells (Flip.template.position phase i)) := by
  decide +kernel

private theorem far_walls : ∀(k : Kind) (hk : outFlip k=true) (p : Flip.C),
    (template k).wall ((farEmbedding k hk).cells (Out.flipIso.cells p))=Flip.template.wall p := by
  decide +kernel

/-- The output correction retains the exact clockwise nine-box flip and its full literal wall stencil. -/
private def farImage (k : Kind) (hk : outFlip k=true) (a b : Bool) :
    StorageImage (slotMatching k a b) ((Flip.checked.slotMatching a b).reorient Out.flipIso) where
  dx:=0
  dy:=39
  fit_x:=by change 0+21≤width k; cases k <;> decide
  fit_y:=by change 39+25≤height k; cases k <;> simp only [outFlip] at hk <;> cases hk <;> decide
  labels:=farLabels k hk
  walls p:=by
    obtain ⟨q,rfl⟩:=Out.flipIso.cells.surjective p
    change (farEmbedding k hk).cells (Out.flipIso.cells q)∈(template k).walls ↔
      Out.flipIso.cells q∈(Out.flipIso.board (Flip.template.board (Flip.template.boxes b))).walls
    rw [Out.flipIso.mem_walls]
    change _↔q∈Flip.template.walls
    rw [(template k).mem_walls,Flip.template.mem_walls,far_walls]
  sources l:=by exact far_positions k hk a l
  targets l:=by exact far_positions k hk b l

private theorem near_component_check : ∀(k : Kind) (_hk : inFlip k=true) (phase : Bool),
    Gadgets.Gates.staticRun (template k).wall ((template k).position phase (turnLabels k 0))
      (Template.slotDirections ((template k).position phase (turnLabels k 0))
        ((template k).position phase (nearLabels k 8)))=
      some ((template k).position phase (nearLabels k 8)) ∧
    Gadgets.Gates.staticRun (template k).wall ((template k).position phase (nearLabels k 8))
      (Template.slotDirections ((template k).position phase (nearLabels k 8))
        ((template k).position phase (turnLabels k 0)))=
      some ((template k).position phase (turnLabels k 0)) := by decide +kernel

private theorem far_component_check : ∀(k : Kind) (hk : outFlip k=true) (phase : Bool),
    Gadgets.Gates.staticRun (template k).wall ((template k).position phase (turnLabels k 28))
      (Template.slotDirections ((template k).position phase (turnLabels k 28))
        ((template k).position phase (farLabels k hk 0)))=
      some ((template k).position phase (farLabels k hk 0)) ∧
    Gadgets.Gates.staticRun (template k).wall ((template k).position phase (farLabels k hk 0))
      (Template.slotDirections ((template k).position phase (farLabels k hk 0))
        ((template k).position phase (turnLabels k 28)))=
      some ((template k).position phase (turnLabels k 28)) := by decide +kernel

private theorem near_component (k : Kind) (hk : inFlip k=true) (a b : Bool) :
    SameComponent (puzzle k a b).board ((slotMatching k a b).source (turnLabels k 0))
      ((slotMatching k a b).source (nearLabels k 8)) :=
  ⟨Gates.staticRun_sound ((template k).wall_correct ((template k).boxes b)) (near_component_check k hk a).1,
    Gates.staticRun_sound ((template k).wall_correct ((template k).boxes b)) (near_component_check k hk a).2⟩

private theorem far_component (k : Kind) (hk : outFlip k=true) (a b : Bool) :
    SameComponent (puzzle k a b).board ((slotMatching k a b).source (turnLabels k 28))
      ((slotMatching k a b).source (farLabels k hk 0)) :=
  ⟨Gates.staticRun_sound ((template k).wall_correct ((template k).boxes b)) (far_component_check k hk a).1,
    Gates.staticRun_sound ((template k).wall_correct ((template k).boxes b)) (far_component_check k hk a).2⟩

private theorem seam_order_check : ∀(k : Kind) (a : Bool),
    (inFlip k=true→((template k).position a (turnLabels k 0)).1.val<
      ((template k).position a (nearLabels k 8)).1.val) ∧
    (∀hk : outFlip k=true,((template k).position a (turnLabels k 28)).2.val<
      ((template k).position a (farLabels k hk 0)).2.val) := by decide +kernel

open Soundness Polyline
variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {a b : Bool} {S T : LabelledState L I.width I.height}

private theorem west_flip_signal (g : StorageImage M ((Flip.checked.slotMatching a b).reorient In.flipIso))
    (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : (S.position (g.labels 0)).1.val≤g.dx+21) :
    (S.position (g.labels 8)).1.val≤g.dx+3 := by
  let o : RectOrientation:=⟨false,true,true⟩
  let e:=o.undo I.width I.height
  let z:=StorageImage.straighten (N:=Flip.checked.slotMatching a b) o g
  have hp:=orient_successful M hs e
  have hc:=rectCertificate M cert o.inverse
  have ho:=rectOrdered M ordered o.inverse
  have hx:g.dx+25≤I.width:=g.fit_x
  have hi : z.dx+3≤((orientLabels e S).position (z.labels 0)).1.val := by
    change I.width-g.dx-25+3≤I.width-((S.position (g.labels 0)).1.val+1)
    omega
  let hz : HorizontalRailGlyph (M.reorient e) .flip := {
    dx:=z.dx
    dy:=z.dy
    fit_x:=z.fit_x
    fit_y:=z.fit_y
    initialPhase:=a
    targetPhase:=b
    labels:=z.labels
    walls p:=by exact z.walls p
    sources l:=by exact z.sources l
    targets l:=by exact z.targets l }
  have hsig:=hz.signal hp hc ho hi
  change I.width-g.dx-25+20+1≤I.width-((S.position (g.labels 8)).1.val+1) at hsig
  have hb:=(S.position (g.labels 8)).1.isLt
  omega

private theorem south_flip_signal (g : StorageImage M ((Flip.checked.slotMatching a b).reorient Out.flipIso))
    (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : g.dy+3≤(S.position (g.labels 0)).2.val) :
    g.dy+21≤(S.position (g.labels 8)).2.val := by
  let o : RectOrientation:=⟨true,true,false⟩
  let e:=o.undo I.width I.height
  let z:=StorageImage.straighten (N:=Flip.checked.slotMatching a b) o g
  have hp:=orient_successful M hs e
  have hc:=rectCertificate M cert o.inverse
  have ho:=rectOrdered M ordered o.inverse
  let hz : HorizontalRailGlyph (M.reorient e) .flip := {
    dx:=z.dx
    dy:=z.dy
    fit_x:=z.fit_x
    fit_y:=z.fit_y
    initialPhase:=a
    targetPhase:=b
    labels:=z.labels
    walls p:=by exact z.walls p
    sources l:=by exact z.sources l
    targets l:=by exact z.targets l }
  exact hz.signal hp hc ho hin

/-- The complete short corner, including either real correction flip, transmits on every successful path. -/
theorem signal (k : Kind) (g : StorageImage M (slotMatching k a b))
    (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : (S.position (g.labels (first k))).1.val+1≤g.dx+sourceX k) :
    g.dy+lastY k+1≤(S.position (g.labels (last k))).2.val := by
  let turn:=g.comp (turnImage k a b)
  have hi : (S.position (turn.labels 0)).1.val≤turn.dx+39 := by
    by_cases hk:inFlip k=true
    · have hnear:=west_flip_signal (g.comp (nearImage k hk a b)) hs cert ordered (by
        have he : nearLabels k 0=first k := by cases k <;> rfl
        change (S.position (g.labels (nearLabels k 0))).1.val≤g.dx+38+21
        rw [he]
        have hx:sourceX k=60 := by cases k <;> simp only [inFlip] at hk <;> cases hk <;> rfl
        rw [hx] at hin
        omega)
      have hc:=g.source_component _ _ (near_component k hk a b)
      have hg:=turn.turnGlyph.horizontalRail.gap hs cert (turn.labels 0) (g.labels (nearLabels k 8)) rfl hc.symm (by
        change (M.source (g.labels (turnLabels k 0))).1.val<(M.source (g.labels (nearLabels k 8))).1.val
        rw [g.sources,g.sources]
        exact Nat.add_lt_add_left ((seam_order_check k a).1 hk) _)
      change (S.position (turn.labels 0)).1.val+2≤(S.position (g.labels (nearLabels k 8))).1.val at hg
      change (S.position (g.labels (nearLabels k 8))).1.val≤g.dx+38+3 at hnear
      change (S.position (turn.labels 0)).1.val≤g.dx+0+39
      omega
    · have he : turnLabels k 0=first k := by cases k <;> simp only [inFlip] at hk <;> first | contradiction | rfl
      have hx : sourceX k=40 := by cases k <;> simp only [inFlip] at hk <;> first | contradiction | rfl
      change (S.position (g.labels (turnLabels k 0))).1.val≤g.dx+0+39
      rw [he]
      rw [hx] at hin
      omega
  have ht:=turn.turnGlyph.signal hs cert ordered hi
  by_cases hk:outFlip k=true
  · have hc:=g.source_component _ _ (far_component k hk a b)
    have hturn:=turn.turnGlyph.component 28 14 (Or.inr ⟨by decide,by decide⟩)
    have hg:=turn.turnGlyph.verticalRail.gap hs cert (turn.labels 28) (g.labels (farLabels k hk 0))
      hturn (hc.symm.trans hturn) (by
        change (M.source (g.labels (turnLabels k 28))).2.val<(M.source (g.labels (farLabels k hk 0))).2.val
        rw [g.sources,g.sources]
        exact Nat.add_lt_add_left ((seam_order_check k a).2 hk) _)
    change (S.position (turn.labels 28)).2.val+2≤(S.position (g.labels (farLabels k hk 0))).2.val at hg
    have hfar:=south_flip_signal (g.comp (farImage k hk a b)) hs cert ordered (by
      change g.dy+39+3≤(S.position (g.labels (farLabels k hk 0))).2.val
      change g.dy+1+39≤(S.position (turn.labels 28)).2.val at ht
      omega)
    have he : farLabels k hk 8=last k := by cases k <;> simp only [outFlip] at hk <;> cases hk <;> rfl
    have hy:lastY k=59 := by cases k <;> simp only [outFlip] at hk <;> cases hk <;> rfl
    change g.dy+39+21≤(S.position (g.labels (farLabels k hk 8))).2.val at hfar
    rw [he] at hfar
    rw [hy]
    omega
  · have he : turnLabels k 28=last k := by cases k <;> simp only [outFlip] at hk <;> first | contradiction | rfl
    have hy:lastY k=39 := by cases k <;> simp only [outFlip] at hk <;> first | contradiction | rfl
    change g.dy+1+39≤(S.position (g.labels (turnLabels k 28))).2.val at ht
    rw [he] at ht
    rw [hy]
    omega

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
