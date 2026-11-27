/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusContacts

/-! The complete annular inventory has its real single player on floor and outside every initial box. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


def playerCoordinates (g : GateTileState) : ℕ×ℕ :=
  ((GateAnnulus.coreOffset g.core.isAND).1+43,(GateAnnulus.coreOffset g.core.isAND).2+85)

def player (g : GateTileState) : Cell 200007 198068 := (bufferAtlas g).player

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem player_coordinates (g : GateTileState) :
    ((player g).1.val,(player g).2.val)=playerCoordinates g := by
  change ((bufferOffset g.core.isAND).1+(2301+10+40),(bufferOffset g.core.isAND).2+(2301+20+82))=_
  have hx : (bufferOffset g.core.isAND).1+2311=(GateAnnulus.coreOffset g.core.isAND).1+3 := by
    cases g.core.isAND <;> decide +kernel
  have hy : (bufferOffset g.core.isAND).2+2321=(GateAnnulus.coreOffset g.core.isAND).2+3 := by
    cases g.core.isAND <;> decide +kernel
  apply Prod.ext <;> dsimp only [playerCoordinates] <;> omega

def Rectangle.Contains (r : Rectangle) (p : ℕ×ℕ) : Prop :=
  r.x≤p.1 ∧ p.1<r.x+r.width ∧ r.y≤p.2 ∧ p.2<r.y+r.height

instance (r : Rectangle) (p : ℕ×ℕ) : Decidable (r.Contains p) := by unfold Rectangle.Contains; infer_instance

def external (g : GateTileState) : Index g→Bool
  | .inl _ => false
  | _ => true

private def playerTest (k : Geometry) : Bool :=
  let g := ofGeometry k
  (indices g).all fun i=>if external g i then decide (¬(rectangle g i).Contains (playerCoordinates g)) else true

private theorem player_checked : ∀ k : Geometry,playerTest k=true := by decide +kernel

private theorem external_geometry (g : GateTileState) (i : Index g) :
    external (ofGeometry (geometry g)) i=external g i := by
  rcases i with i | (⟨r,s | t⟩ | u) <;> rfl

private theorem rectangle_geometry (g : GateTileState) (i : Index g) :
    rectangle (ofGeometry (geometry g)) i=rectangle g i := by
  rcases i with i | (⟨r,s | t⟩ | u) <;> rfl

private theorem player_outside (g : GateTileState) (i : Index g) (hi : external g i=true) :
    ¬(rectangle g i).Contains (playerCoordinates g) := by
  change Index (ofGeometry (geometry g)) at i
  have hh := player_checked (geometry g)
  have hp := List.all_eq_true.mp hh i (mem_indices (ofGeometry (geometry g)) i)
  have hi' : external (ofGeometry (geometry g)) i=true := (external_geometry g i).trans hi
  have hp' : ¬(rectangle (ofGeometry (geometry g)) i).Contains (playerCoordinates (ofGeometry (geometry g))) := by
    simpa only [hi',ite_true,decide_eq_true_eq] using hp
  rw [rectangle_geometry g i] at hp'
  exact hp'

private theorem player_external_no_incidence (g : GateTileState) (i : Index g)
    (hi : external g i=true)
    (p : Cell (piece g i).width (piece g i).height) :
    ((player g).1.val,(player g).2.val)≠((offset g i).1+p.1.val,(offset g i).2+p.2.val) := by
  intro he
  have hx := p.1.isLt
  have hy := p.2.isLt
  have hd := piece_dimensions g i
  apply player_outside g i hi
  rw [←player_coordinates g,he]
  dsimp only [Rectangle.Contains,rectangle]
  rw [geometricOffset_eq]
  omega

theorem player_floor (g : GateTileState) (i : Index g) (p : Cell (piece g i).width (piece g i).height)
    (hp : p∈(piece g i).board.walls) :
    ((player g).1.val,(player g).2.val)≠((offset g i).1+p.1.val,(offset g i).2+p.2.val) := by
  cases i with
  | inl i => exact (bufferAtlas g).player_floor i p hp
  | inr i => exact player_external_no_incidence g (.inr i) rfl p

theorem player_empty (g : GateTileState) (i : Index g) (l : Labels g i) :
    ((player g).1.val,(player g).2.val)≠
      ((offset g i).1+((matching g i).source l).1.val,(offset g i).2+((matching g i).source l).2.val) := by
  cases i with
  | inl i => exact (bufferAtlas g).player_empty i l
  | inr i => exact player_external_no_incidence g (.inr i) rfl _

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
