/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Checked
public import PushFS.Reduction.FullGateStatics.Endpoints

/-! Every actual full-gate displacement is classified by the verified finite primitive and exterior charts. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Gadgets.Wires.Catalog
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

theorem safe_owner (g : GateTileState) (c : ChartIndex g) (p : Cell (chart g c).width (chart g c).height)
    (ha : (chart g c).classifier.name p≠.outside) :
    ∃d q,BoundaryAligned (W:=200007) (H:=198068) (chart g d).dx (chart g d).dy q ∧
      (chart g d).embedding.cells q=(chart g c).embedding.cells p ∧
      ((chart g c).classifier.name p).level≤((chart g d).classifier.name q).level := by
  by_cases hp : BoundaryAligned (W:=200007) (H:=198068) (chart g c).dx (chart g c).dy p
  · exact ⟨c,p,hp,rfl,le_refl _⟩
  · have hb:=boundary_complete g c p ha hp
    have hall:=coverage_all g
    change (chartIndices g).all (fun c=>(shape (chart g c)).boundary.all
      (endpointTest (chartIndices g) (fun d=>shape (chart g d)) c))=true at hall
    have hc:=List.all_eq_true.mp hall c (mem_chartIndices g c)
    have hu:=List.all_eq_true.mp hc (p.1.val,p.2.val) hb
    have hn : ¬((shape (chart g c)).name (p.1.val,p.2.val)=.outside ∨
        (shape (chart g c)).Safe (p.1.val,p.2.val)) := by
      rintro (hn|hs)
      · exact ha ((shape_name (chart g c) p).symm.trans hn)
      · exact hp ((safe_iff (chart g c) p).mp hs)
    simp only [endpointTest,ite_eq_right hn] at hu
    obtain ⟨d,_,hd⟩:=List.any_eq_true.mp hu
    change decide ((shape (chart g d)).Contains ((shape (chart g c)).global (p.1.val,p.2.val)) ∧
      (shape (chart g d)).Safe ((shape (chart g d)).local ((shape (chart g c)).global (p.1.val,p.2.val))) ∧
      ((shape (chart g c)).name (p.1.val,p.2.val)).level≤
        ((shape (chart g d)).name ((shape (chart g d)).local ((shape (chart g c)).global (p.1.val,p.2.val)))).level)=true at hd
    have hd':=of_decide_eq_true hd
    have hbounds:=hd'.1
    dsimp only [Shape.Contains,shape,Shape.global] at hbounds
    let q : Cell (chart g d).width (chart g d).height :=
      (⟨(chart g c).dx+p.1.val-(chart g d).dx,by omega⟩,
        ⟨(chart g c).dy+p.2.val-(chart g d).dy,by omega⟩)
    refine ⟨d,q,?_,?_,?_⟩
    · apply (safe_iff (chart g d) q).mp
      exact hd'.2.1
    · apply Prod.ext <;> apply Fin.ext
      · change (chart g d).dx+((chart g c).dx+p.1.val-(chart g d).dx)=(chart g c).dx+p.1.val
        omega
      · change (chart g d).dy+((chart g c).dy+p.2.val-(chart g d).dy)=(chart g c).dy+p.2.val
        omega
    · have hl:=hd'.2.2
      change ((shape (chart g c)).name (p.1.val,p.2.val)).level≤((shape (chart g d)).name (q.1.val,q.2.val)).level at hl
      rw [shape_name (chart g c) p,shape_name (chart g d) q] at hl
      exact hl

def mosaic (g : GateTileState) : Mosaic (W:=200007) (H:=198068) (fullPuzzle g).board (ChartIndex g) where
  chart:=chart g
  walls:=chart_walls g
  safe:=safe_owner g

/-- Unconditional supported classification of every wall-only displacement of the actual complete gate. -/
noncomputable def classifier (g : GateTileState) : AxisClassifier (fullPuzzle g).board := (mosaic g).classifier

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
