/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceNeighborSlots
public import PushS.FiniteSourcePrimitiveProfile
public import PushS.FiniteTurnDockMacros

/-! Complete actual F/G turn updates retain the neighboring lines' literal P/Q identities. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteTools
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height InventoryAssembly.board

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

/-- One real perpendicular junction in the emitted source table. -/
structure TurnStep (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (P : PathSpec) where
  path : PathSite w hw v P
  geometry : P.Geometry w
  index : Fin P.segments.length
  hasTurn : P.hasTurn index.val

namespace TurnStep

variable (s : TurnStep w hw v P)

def incoming : LineSite w hw v := s.path.line s.index
def outgoing : LineSite w hw v := s.path.line ⟨s.index.val+1,s.hasTurn.1⟩
def site : TurnSite w hw v := s.path.turn s.geometry s.index s.hasTurn

theorem contract : JunctionContract w s.incoming.code s.site.code s.outgoing.code :=
  P.junction_contract w s.geometry s.index.val s.hasTurn

def predecessorOwned : (PrimitiveCode.line s.incoming.code).Labels w := by
  change Line.OwnedLabel w s.incoming.atoms s.incoming.code.first s.incoming.code.last
  unfold LineSite.atoms
  refine ⟨Line.penultimateLabel w (segmentLength s.incoming.code.segment) (s.incoming.code.above != s.incoming.code.desiredSide),Or.inr ?_,Or.inr ?_⟩
  all_goals
    rw [Line.penultimate_val]
    have := Line.program_length_ge_six w (segmentLength s.incoming.code.segment) (s.incoming.code.above != s.incoming.code.desiredSide)
    omega

def successorOwned : (PrimitiveCode.line s.outgoing.code).Labels w := by
  change Line.OwnedLabel w s.outgoing.atoms s.outgoing.code.first s.outgoing.code.last
  unfold LineSite.atoms
  refine ⟨Line.secondLabel w (segmentLength s.outgoing.code.segment) (s.outgoing.code.above != s.outgoing.code.desiredSide),Or.inr (by change 0 < 1; omega),Or.inr ?_⟩
  have := Line.program_length_ge_six w (segmentLength s.outgoing.code.segment) (s.outgoing.code.above != s.outgoing.code.desiredSide)
  change 1+1 < _
  exact lt_of_lt_of_le (by omega) this

def label : TurnLabel → (inventory w hw v).PhysicalLabel
  | .predecessor => s.incoming.label s.predecessorOwned
  | .horizontal => s.site.label 0
  | .vertical => s.site.label 1
  | .successor => s.outgoing.label s.successorOwned

private theorem primitive_owner (i : Fin (codes w v).length) (c : PrimitiveCode)
    (hc : ((codes w v).get i).2 = c) (l : c.Labels w) : (primitiveLabel w hw v i c hc l).1 = i := by
  subst c
  rfl

private theorem label_owner (l : TurnLabel) : (s.label l).1 =
    match l with
    | .predecessor => s.incoming.index
    | .horizontal | .vertical => s.site.index
    | .successor => s.outgoing.index := by
  cases l <;> exact primitive_owner _ _ _ _

private theorem incoming_ne_site : s.incoming.index ≠ s.site.index := by
  intro he
  have h := s.incoming.code_eq
  rw [he,s.site.code_eq] at h
  cases h

private theorem outgoing_ne_site : s.outgoing.index ≠ s.site.index := by
  intro he
  have h := s.outgoing.code_eq
  rw [he,s.site.code_eq] at h
  cases h

private theorem incoming_ne_outgoing : s.incoming.index ≠ s.outgoing.index := by
  intro he
  have h := s.incoming.code_eq
  rw [he,s.outgoing.code_eq] at h
  have hc : s.outgoing.code = s.incoming.code := PrimitiveCode.line.inj h
  have hd := congrArg (fun c : LineCode => segmentDirection c.segment) hc
  rw [s.contract.incoming_direction,s.contract.outgoing_direction] at hd
  exact perpendicular_ne s.contract.perpendicular hd.symm

theorem label_injective : Function.Injective s.label := by
  intro a b he
  have hi := congrArg (fun l : (inventory w hw v).PhysicalLabel => l.1) he
  rw [s.label_owner a,s.label_owner b] at hi
  have hv (a b : Fin 2) (he : s.site.label a = s.site.label b) : a = b :=
    primitiveLabel_injective w hw v s.site.index (.turn s.site.code) s.site.code_eq he
  cases a <;> cases b <;> first
    | rfl
    | exact False.elim (s.incoming_ne_site hi)
    | exact False.elim (s.incoming_ne_site hi.symm)
    | exact False.elim (s.outgoing_ne_site hi)
    | exact False.elim (s.outgoing_ne_site hi.symm)
    | exact False.elim (s.incoming_ne_outgoing hi)
    | exact False.elim (s.incoming_ne_outgoing hi.symm)
    | exact False.elim (by have h := hv 0 1 he; cases h)
    | exact False.elim (by have h := hv 1 0 he; cases h)

def labels : TurnLabel ↪ (inventory w hw v).PhysicalLabel := ⟨s.label,s.label_injective⟩

private theorem primitive_surjective (i : Fin (codes w v).length) (c : PrimitiveCode)
    (hc : ((codes w v).get i).2 = c) (l : (inventory w hw v).PhysicalLabel) (hi : l.1 = i) :
    ∃ q,primitiveLabel w hw v i c hc q = l := by
  subst c
  rcases l with ⟨j,l⟩
  dsimp at hi
  subst j
  exact ⟨l,rfl⟩

private theorem cover : (inventory w hw v).pieceLabels s.site.index ⊆ Finset.univ.map s.labels := by
  intro l hl
  obtain ⟨q,hq⟩ := primitive_surjective s.site.index (.turn s.site.code) s.site.code_eq l
    ((inventory w hw v).mem_pieceLabels s.site.index l |>.mp hl)
  change Fin 2 at q
  fin_cases q
  · exact Finset.mem_map.mpr ⟨.horizontal,Finset.mem_univ _,hq⟩
  · exact Finset.mem_map.mpr ⟨.vertical,Finset.mem_univ _,hq⟩

/-- The real incoming stock is low and outgoing stock is high before either turn direction. -/
structure Ready (phase : Fin (codes w v).length → Bool) : Prop where
  fresh : phase s.site.index = false
  predecessor_low : phase s.incoming.index = P.initial
  successor_high : phase s.outgoing.index = !P.initial

private theorem line_current (t : LineSite w hw v) (phase : Fin (codes w v).length → Bool)
    (l : (PrimitiveCode.line t.code).Labels w) :
    PrimitiveProfile.position w hw v phase (t.label l) = t.actualEmbedding.cells
      (Line.cell w hw t.atoms (if phase t.index then t.code.target else t.code.initial) l.val) := by
  have hi := primitive_owner (hw:=hw) t.index (.line t.code) t.code_eq l
  change (t.label l).1 = t.index at hi
  have hs : (inventory w hw v).source (t.label l) = t.actualEmbedding.cells
      (Line.cell w hw t.atoms t.code.initial l.val) :=
    source_primitiveLabel w hw v t.index (.line t.code) t.code_eq l
  have ht : (inventory w hw v).target (t.label l) = t.actualEmbedding.cells
      (Line.cell w hw t.atoms t.code.target l.val) :=
    target_primitiveLabel w hw v t.index (.line t.code) t.code_eq l
  cases hp : phase t.index
  · simpa only [PrimitiveProfile.position,hi,hp,Bool.false_eq_true,ite_false] using hs
  · simpa only [PrimitiveProfile.position,hi,hp,ite_true] using ht

private theorem own_current (phase : Fin (codes w v).length → Bool) (l : Fin 2) :
    PrimitiveProfile.position w hw v phase (s.site.label l) = s.site.actualEmbedding.cells
      (Turn.cell w (if phase s.site.index then P.target else P.initial) l) := by
  have hi := primitive_owner (hw:=hw) s.site.index (.turn s.site.code) s.site.code_eq l
  change (s.site.label l).1 = s.site.index at hi
  have hs : s.site.code.initial = P.initial := rfl
  have ht : s.site.code.target = P.target := rfl
  cases hp : phase s.site.index
  · simpa only [PrimitiveProfile.position,hi,hp,Bool.false_eq_true,ite_false,hs] using s.site.source_actual l
  · simpa only [PrimitiveProfile.position,hi,hp,ite_true,ht] using s.site.target_actual l

/-- The four selected real identities are the prepared full turn inventory. -/
private theorem current_slots (phase : Fin (codes w v).length → Bool) (q : Bool)
    (hq : phase s.site.index = q) (hb : P.target = !P.initial)
    (hp : phase s.incoming.index = P.initial) (hn : phase s.outgoing.index = !P.initial) :
    ∀ l, PrimitiveProfile.position w hw v phase (s.labels l) = s.site.actualEmbedding.cells
      (turnMixedCell w (if q then P.target else P.initial) (if q then P.target else P.initial) l) := by
  intro l
  cases l with
  | predecessor =>
    have h := line_current s.incoming phase s.predecessorOwned
    have hphase : (if phase s.incoming.index then s.incoming.code.target else s.incoming.code.initial) = false := by
      change (if phase s.incoming.index then P.target else P.initial) = false
      rw [hp,hb]
      cases P.initial <;> rfl
    rw [hphase] at h
    exact h.trans (s.path.predecessor_cells s.geometry s.index s.hasTurn)
  | successor =>
    have h := line_current s.outgoing phase s.successorOwned
    have hphase : (if phase s.outgoing.index then s.outgoing.code.target else s.outgoing.code.initial) = true := by
      change (if phase s.outgoing.index then P.target else P.initial) = true
      rw [hn,hb]
      cases P.initial <;> rfl
    rw [hphase] at h
    exact h.trans (s.path.successor_cells s.geometry s.index s.hasTurn)
  | horizontal =>
    have h := s.own_current phase 0
    rw [hq] at h
    exact h
  | vertical =>
    have h := s.own_current phase 1
    rw [hq] at h
    exact h

/-- The full actual turn update starts and ends at its free concave-quadrant dock. -/
theorem run (phase : Fin (codes w v).length → Bool) (R : s.Ready phase)
    (hb : P.target = !P.initial) (B : Board (width w v) (height w v))
    (F : FiniteWireFrame.Frame (turnActive w) s.site.actualEmbedding B
      (PrimitiveProfile.outside w hw v phase (Finset.univ.map s.labels))) :
    Reachable B (some 1)
      (PrimitiveProfile.state w hw v phase (s.site.actualEmbedding.cells (turnDock w)))
      (PrimitiveProfile.state w hw v (Function.update phase s.site.index true)
        (s.site.actualEmbedding.cells (turnDock w))) := by
  have hs := s.current_slots phase false R.fresh hb R.predecessor_low R.successor_high
  have ht := s.current_slots (Function.update phase s.site.index true) true
    (Function.update_self _ _ _) hb (by
      rw [Function.update_of_ne s.incoming_ne_site]
      exact R.predecessor_low) (by
      rw [Function.update_of_ne s.outgoing_ne_site]
      exact R.successor_high)
  apply PrimitiveProfile.selection_run phase s.site.index s.labels s.cover s.site.actualEmbedding
    (turnMixedCell w P.initial P.initial) (turnMixedCell w P.target P.target) hs ht B _ _
  cases hi : P.initial
  · have htarget : P.target = true := by simpa only [hi,Bool.not_false] using hb
    simpa only [hi,htarget,turnBoxes,turnMixedBoxes] using turn_dock_forward_placed w s.site.actualEmbedding F
  · have htarget : P.target = false := by simpa only [hi,Bool.not_true] using hb
    simpa only [hi,htarget,turnBoxes,turnMixedBoxes] using turn_dock_backward_placed w s.site.actualEmbedding F

end TurnStep
end PushPuzzle.PushS.FiniteSourceInventory
