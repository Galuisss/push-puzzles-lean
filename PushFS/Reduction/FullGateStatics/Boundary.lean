/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Shape

/-! Small endpoint coverage checks imply actual safe local ownership of every static rail cell. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Gadgets.Wires.Catalog
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

theorem perimeter_complete (s : Shape) (p : ℕ×ℕ) (hx : p.1<s.width) (hy : p.2<s.height)
    (he : p.1=0 ∨p.1+1=s.width ∨p.2=0 ∨p.2+1=s.height) : p∈s.perimeter := by
  rcases p with ⟨x,y⟩
  dsimp only at hx hy he
  rcases he with he|he|he|he
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨y,List.mem_range.mpr hy,by simp only [he]⟩))
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨y,List.mem_range.mpr hy,by apply Prod.ext <;> dsimp only; omega⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨x,List.mem_range.mpr hx,by simp only [he]⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨x,List.mem_range.mpr hx,by apply Prod.ext <;> dsimp only; omega⟩

theorem not_aligned_boundary {w h : ℕ} (dx dy : ℕ) (p : Cell w h)
    (hp : ¬BoundaryAligned (W:=200007) (H:=198068) dx dy p) :
    p.1.val=0 ∨p.1.val+1=w ∨p.2.val=0 ∨p.2.val+1=h := by
  by_contra he
  apply hp
  dsimp only [BoundaryAligned]
  tauto

theorem safe_iff (C : TranslatedAxisChart 200007 198068) (p : Cell C.width C.height) :
    (shape C).Safe (p.1.val,p.2.val) ↔BoundaryAligned (W:=200007) (H:=198068) C.dx C.dy p := by
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  dsimp only [Shape.Safe,shape,BoundaryAligned]
  omega

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
