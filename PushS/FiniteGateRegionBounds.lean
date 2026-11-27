/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateActiveRegion
public import PushS.FiniteGateSelected

public import PushS.FiniteGeometrySimp

/-! Literal coordinate bounds of the core macros' working stocks and active footprints. -/

public section
namespace PushPuzzle.PushS.FiniteGateActiveRegion

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateAStraight FiniteSquareLine FiniteLineMacros FiniteGateMacros
open FiniteGateBranchSweeps FiniteGateVertical FiniteGateOutputs FiniteGateInputs
open scoped Classical

attribute [local irreducible] FiniteGeometry.side FiniteTools.side

/-- The left boundary of the core working envelope. -/
@[expose] def minX (w : ℕ) (kind : Bool) : ℕ := if kind then origin w-8*w-18 else origin w-2*w-9
/-- The right boundary of the core working envelope. -/
@[expose] def maxX (w : ℕ) (kind : Bool) : ℕ := if kind then origin w+3*w+14 else origin w+3*w+15
/-- The upper boundary of the core working envelope. -/
@[expose] def minY (w : ℕ) (kind : Bool) : ℕ := if kind then origin w-8*w-33 else origin w-2*w-15

/-- The active rectangle may reach two outward columns only at the selected port. -/
@[expose] def SafeBounds (w : ℕ) (kind : Bool) (selected : Fin 3) (p : ℕ × ℕ) : Prop :=
  Envelope w kind p ∧ (selected ≠ 0 → minX w kind < p.1) ∧
    (selected ≠ 1 → minY w kind < p.2) ∧ (selected ≠ 2 → p.1 < maxX w kind)

attribute [local finite_gate_tool_coords]
  SafeBounds Envelope minX maxX minY coordinates FiniteGateAApproaches.Detour.startPoint FiniteGateAApproaches.Detour.finishPoint s t flipY origin Segment.sweep Sweep.map Line.track Line.laneSegment Segment.base Segment.count Segment.row Segment.lane Segment.hubCoordinate andBSweep inputBLine point orBSweep andOutputSweep outputLine orOutputSweep orInputSweep orInputLine

theorem region_of_safeBounds (w : ℕ) (kind : Bool) (selected : Fin 3)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : SafeBounds w kind selected (coordinates p)) :
    Region w kind selected p := by
  refine ⟨hp.1,?_⟩
  intro role hrole he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  fin_cases role
  · have hh := hp.2.1 (Ne.symm hrole)
    cases kind <;> simp [minX,coordinates,coreWorld,corePort,Line.along,PortAnnulus.innerDirection,origin,
      coreOffset,padding,spacing] at hx hy hh <;> omega
  · have hh := hp.2.2.1 (Ne.symm hrole)
    cases kind <;> simp [minY,coordinates,coreWorld,corePort,Line.along,PortAnnulus.innerDirection,origin,
      coreOffset,padding,spacing] at hx hy hh <;> omega
  · have hh := hp.2.2.2 (Ne.symm hrole)
    cases kind <;> simp [maxX,coordinates,coreWorld,corePort,Line.along,PortAnnulus.innerDirection,origin,
      coreOffset,padding,spacing] at hx hy hh <;> omega

/-- Every literal normal AND slot lies in the common core stock envelope. -/
private theorem and_cell_envelope (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : AndLabel w) :
    Envelope w true (coordinates (andCell w a b c l)) := by
  have hh := andPoint_actor_bounds w hw a b c l
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  dsimp [Envelope,coordinates,andCell,origin] at *
  omega

private theorem or_cell_envelope (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : OrLabel w) :
    Envelope w false (coordinates (orCell w a b c l)) := by
  have hh := orPoint_actor_bounds w hw a b c l
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  dsimp [Envelope,coordinates,orCell,origin] at *
  omega

/-- Every actual mixed AND auxiliary, including temporary A/I slots, remains in the same envelope. -/
theorem and_mixed_envelope (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (l : AndLabel w) :
    Envelope w true (coordinates (andMixedCell w X l)) := by
  cases l with
  | west i => exact and_cell_envelope w hw _ _ _ _
  | upper i => exact and_cell_envelope w hw _ _ _ _
  | lower i => exact and_cell_envelope w hw _ _ _ _
  | guard i => exact and_cell_envelope w hw _ _ _ _
  | branchB i => exact and_cell_envelope w hw _ _ _ _
  | branchC i => exact and_cell_envelope w hw _ _ _ _
  | middle => have hh := X.middle.isLt; dsimp [Envelope,coordinates,andMixedCell,origin]; omega
  | triggerA => have hh := X.triggerA.isLt; dsimp [Envelope,coordinates,andMixedCell,origin]; omega

theorem or_mixed_envelope (w : ℕ) (hw : 2 ≤ w) (X : OrPhases w) (l : OrLabel w) :
    Envelope w false (coordinates (orMixedCell w X l)) := by
  cases l with
  | left i => exact or_cell_envelope w hw _ _ _ _
  | branchB i => exact or_cell_envelope w hw _ _ _ _
  | branchC i => exact or_cell_envelope w hw _ _ _ _
  | triggerA => exact or_cell_envelope w hw _ _ _ _

/-- The small actual cavity footprints are strictly inside every external port support boundary. -/
theorem cavity_safe (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (selected : Fin 3)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (hx : origin w ≤ p.1.val) (hx' : p.1.val ≤ origin w+w+8)
    (hy : origin w-8 ≤ p.2.val) (hy' : p.2.val ≤ origin w) :
    SafeBounds w kind selected (coordinates p) := by
  cases kind <;> dsimp [SafeBounds,Envelope,minX,maxX,minY,coordinates,origin] at * <;> omega

/-- Every normal AND fixed-stock subset lies in the actual core envelope. -/
theorem and_normal_image_envelope (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (L : Finset (AndLabel w))
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ L.image (andCell w a b c)) :
    Envelope w true (coordinates p) := by
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact and_cell_envelope w hw a b c l

theorem or_normal_image_envelope (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (L : Finset (OrLabel w))
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ L.image (orCell w a b c)) :
    Envelope w false (coordinates p) := by
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact or_cell_envelope w hw a b c l

/-- Every mixed AND fixed-stock subset, including the tools' shared neighbors, lies in the actual core envelope. -/
theorem and_mixed_image_envelope (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (L : Finset (AndLabel w))
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ L.image (andMixedCell w X)) :
    Envelope w true (coordinates p) := by
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact and_mixed_envelope w hw X l

theorem or_mixed_image_envelope (w : ℕ) (hw : 2 ≤ w) (X : OrPhases w) (L : Finset (OrLabel w))
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ L.image (orMixedCell w X)) :
    Envelope w false (coordinates p) := by
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact or_mixed_envelope w hw X l

/-- All three real AND tools lie strictly inside the two-step exterior support bounds. -/
theorem protection_safe (w : ℕ) (hw : 2 ≤ w) (selected : Fin 3)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w) :
    SafeBounds w true selected (coordinates ((protectionEmbedding w).cells p)) := by
  have hh := protection_region w hp
  dsimp [SafeBounds,Envelope,minX,maxX,minY,coordinates,s,origin] at *
  omega

theorem upper_safe (w : ℕ) (hw : 2 ≤ w) (selected : Fin 3)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w) :
    SafeBounds w true selected (coordinates ((upperEmbedding w).cells p)) := by
  have hh := upper_region w hp
  dsimp [SafeBounds,Envelope,minX,maxX,minY,coordinates,s,t,origin] at *
  omega

theorem flip_safe (w : ℕ) (hw : 2 ≤ w) (selected : Fin 3)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.flipActive w) :
    SafeBounds w true selected (coordinates ((flipEmbedding w).cells p)) := by
  have hh := flip_region w hp
  dsimp [SafeBounds,Envelope,minX,maxX,minY,coordinates,s,flipY,origin] at *
  omega

/-- The four actual A-branch island detours stay strictly inside every outward support boundary. -/
theorem detour_safe (w : ℕ) (hw : 2 ≤ w) (selected : Fin 3) (k : FiniteGateAApproaches.Detour)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (hp : p ∈ FiniteAtomFrames.walkActive (k.start w) (k.finish w)) :
    SafeBounds w true selected (coordinates p) := by
  obtain ⟨hx,hx',hy,hy'⟩ := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
  have hsx := congrArg Prod.fst (FiniteGateAApproaches.Detour.start_coordinates w k)
  have hsy := congrArg Prod.snd (FiniteGateAApproaches.Detour.start_coordinates w k)
  have hfx := congrArg Prod.fst (FiniteGateAApproaches.Detour.finish_coordinates w k)
  have hfy := congrArg Prod.snd (FiniteGateAApproaches.Detour.finish_coordinates w k)
  dsimp only at hsx hsy hfx hfy
  rw [hsx,hfx] at hx hx'
  rw [hsy,hfy] at hy hy'
  cases k <;>
    dsimp [finite_gate_tool_coords] at hx hx' hy hy' ⊢ <;> omega

/-- The full selected A chain's actual working row and lane fit the real selected-core region. -/
theorem and_sweep_safe (w : ℕ) (hw : 2 ≤ w) (k : FiniteGateAStraight.Segment)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ (k.sweep w).active) :
    SafeBounds w true 0 (coordinates p) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  rw [FiniteSquareLine.Sweep.embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  all_goals
    have hy' := congrArg Fin.val hy
    cases k <;>
      dsimp [finite_gate_tool_coords] at hx hy' ⊢ <;> omega

/-- The complete actual branch stock sweep stays in its selected core region. -/
theorem and_b_sweep_safe (w : ℕ) (hw : 2 ≤ w)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ (andBSweep w).active) :
    SafeBounds w true 1 (coordinates p) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  rw [FiniteSquareLine.Sweep.embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  all_goals
    have hy' := congrArg Fin.val hy
    dsimp [finite_gate_tool_coords]
      at hx hy' ⊢
    omega

/-- The complete actual branch stock sweep stays in its selected core region. -/
theorem or_b_sweep_safe (w : ℕ) (hw : 2 ≤ w)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ (orBSweep w).active) :
    SafeBounds w false 1 (coordinates p) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  rw [FiniteSquareLine.Sweep.embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  all_goals
    have hy' := congrArg Fin.val hy
    dsimp [finite_gate_tool_coords]
      at hx hy' ⊢
    omega

/-- The complete actual branch stock sweep stays in its selected core region. -/
theorem and_c_sweep_safe (w : ℕ) (hw : 2 ≤ w)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ (andOutputSweep w).active) :
    SafeBounds w true 2 (coordinates p) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  rw [FiniteSquareLine.Sweep.embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  all_goals
    have hy' := congrArg Fin.val hy
    dsimp [finite_gate_tool_coords]
      at hx hy' ⊢
    omega

/-- The complete actual branch stock sweep stays in its selected core region. -/
theorem or_c_sweep_safe (w : ℕ) (hw : 2 ≤ w)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ (orOutputSweep w).active) :
    SafeBounds w false 2 (coordinates p) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  rw [FiniteSquareLine.Sweep.embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  all_goals
    have hy' := congrArg Fin.val hy
    dsimp [finite_gate_tool_coords]
      at hx hy' ⊢
    omega

/-- The complete actual branch stock sweep stays in its selected core region. -/
theorem or_a_sweep_safe (w : ℕ) (hw : 2 ≤ w)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ (orInputSweep w).active) :
    SafeBounds w false 0 (coordinates p) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  rw [FiniteSquareLine.Sweep.embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  all_goals
    have hy' := congrArg Fin.val hy
    dsimp [finite_gate_tool_coords]
      at hx hy' ⊢
    omega

end PushPuzzle.PushS.FiniteGateActiveRegion
