/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusCorners
public import PushFS.Reduction.AnnulusCaps
public import PushFS.Reduction.CanonicalPhases
public import PushFS.Reduction.GateTileCore

/-! Complete actual buffered-gate, long-line, protected-corner and zero-box guard inventories of every finite gate tile. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


open Gadgets.Wires Turing.MultiTapeTM ComputableInPolyTime

abbrev ArmIndex (g : GateTileState) :=
  (role : Fin 3) × (Fin (curve (key g role)).length ⊕ Fin ((curve (key g role)).length-1))
abbrev CapIndex (g : GateTileState) := {role : Fin 3 // g.incoming.get role=false}
abbrev Index (g : GateTileState) := Fin 4 ⊕ (ArmIndex g ⊕ CapIndex g)

instance (g : GateTileState) : Fintype (Index g) := by
  unfold Index ArmIndex CapIndex
  infer_instance

def initialPhase (g : GateTileState) (role : Fin 3) : Bool := gateClaim g.core.initial role
def targetPhase (g : GateTileState) (role : Fin 3) : Bool := gateClaim g.core.target role

def piece (g : GateTileState) : Index g → Instance
  | .inl i => (bufferAtlas g).piece i
  | .inr (.inl ⟨role,.inl j⟩) =>
      linePiece (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)
  | .inr (.inl ⟨role,.inr j⟩) =>
      cornerPiece (key g role) j.val (initialPhase g role) (targetPhase g role)
  | .inr (.inr role) => capPiece (g.key role.val)

def Labels (g : GateTileState) : Index g → Type
  | .inl i => GateLead.Labels g.core.isAND 2301 i
  | .inr (.inl ⟨role,.inl j⟩) => lineLabels (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
  | .inr (.inl ⟨role,.inr j⟩) => Fin (ShortCorners.count (cornerKind (key g role) j.val))
  | .inr (.inr _) => Fin 0

instance (g : GateTileState) (i : Index g) : Fintype (Labels g i) := by
  rcases i with i | (⟨role,j | j⟩ | role) <;> unfold Labels <;> infer_instance

def matching (g : GateTileState) : (i : Index g)→SlotMatching (piece g i) (Labels g i)
  | .inl i => (bufferAtlas g).matching i
  | .inr (.inl ⟨role,.inl j⟩) =>
      lineSlotMatching (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)
  | .inr (.inl ⟨role,.inr j⟩) =>
      cornerMatching (key g role) j.val (initialPhase g role) (targetPhase g role)
  | .inr (.inr role) => capSlotMatching (g.key role.val)

def offset (g : GateTileState) : Index g → ℕ×ℕ
  | .inl i => ((bufferAtlas g).dx i,(bufferAtlas g).dy i)
  | .inr (.inl ⟨role,.inl j⟩) => lineOffset (key g role) j.val
  | .inr (.inl ⟨role,.inr j⟩) => cornerOffset (key g role) j.val
  | .inr (.inr role) => capOffset (g.key role.val)

theorem fits (g : GateTileState) (i : Index g) :
    (offset g i).1+(piece g i).width≤200007 ∧ (offset g i).2+(piece g i).height≤198068 := by
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact ⟨(bufferAtlas g).fitsX i,(bufferAtlas g).fitsY i⟩
  · change (lineOffset (key g role) j.val).1+
      (linePiece (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)).width≤200007 ∧
      (lineOffset (key g role) j.val).2+
      (linePiece (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)).height≤198068
    rw [(linePiece_dimensions (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)).1,
      (linePiece_dimensions (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)).2]
    exact line_fits _ _ j.isLt
  · exact corner_fits _ _ (by have := j.isLt; omega)
  · exact cap_fits _

/-- Each listed patch is the full standard bitmap of its genuine physical storage piece. -/
def patch (g : GateTileState) (i : Index g) : Bitmap.Patch :=
  ⟨(offset g i).1,(offset g i).2,Encoding.data (piece g i)⟩

/-- Explicit source-role order retains every primitive piece and emits exactly the actual output guard caps. -/
def indices (g : GateTileState) : List (Index g) :=
  (List.finRange 4).map Sum.inl ++ (List.finRange 3).flatMap fun role =>
    (List.finRange (curve (key g role)).length).map (fun j=>.inr (.inl ⟨role,.inl j⟩)) ++
    (List.finRange ((curve (key g role)).length-1)).map (fun j=>.inr (.inl ⟨role,.inr j⟩)) ++
    (if h : g.incoming.get role=false then [.inr (.inr ⟨role,h⟩)] else [])

theorem mem_indices (g : GateTileState) (i : Index g) : i∈indices g := by
  rcases i with i | (⟨role,j | j⟩ | ⟨role,hr⟩)
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨i,by simp,rfl⟩)
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨role,by simp,?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨j,by simp,rfl⟩))
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨role,by simp,?_⟩
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j,by simp,rfl⟩))
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨role,by simp,?_⟩
    apply List.mem_append_right
    simp only [hr,dite_eq_left,List.mem_singleton]

def patches (g : GateTileState) : List Bitmap.Patch := (indices g).map (patch g)

/-- The complete actual physical rendering input with the same true central player as the buffered core. -/
def input (g : GateTileState) : Bitmap.Input :=
  ⟨200007,198068,(bufferInput g).playerX,(bufferInput g).playerY,patches g⟩

theorem input_polyTime : ComputableInPolyTime input encGateTileState Bitmap.encInput := of_finite _

def data (g : GateTileState) : Encoding.Data := Bitmap.emit (input g)

/-- Finite gate lookup followed by the real full-rectangle machine rasterizer. -/
theorem data_polyTime : ComputableInPolyTime data encGateTileState Encoding.encData :=
  Bitmap.emit_polyTime.comp input_polyTime

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
