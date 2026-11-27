/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Track
public import PushFS.AxisIsometry

/-! Exact physical identity paths and static target order under the D4 maps needed by routed wires. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


variable {w h W H : ℕ} {Label : Type} [Fintype Label]

def orientLabels (e : GridIsometry w h W H) (S : LabelledState Label w h) : LabelledState Label W H where
  state := e.state S.state
  position i := e.cells (S.position i)
  injective := e.cells.injective.comp S.injective
  boxes_image := by
    change Finset.univ.image (e.cells ∘ S.position)=S.state.boxes.map e.cells.toEmbedding
    rw [← Finset.image_image,S.boxes_image,Finset.map_eq_image]
    rfl

private theorem map_shift (e : GridIsometry w h W H) (src dst p : Cell w h) :
    e.cells (shiftBox src dst p)=shiftBox (e.cells src) (e.cells dst) (e.cells p) := by
  by_cases he : p=src
  · subst p
    simp only [shiftBox_source]
  · simp only [shiftBox_other he,shiftBox_other (fun h => he (e.cells.injective h))]

/-- Every actual walk/push follows exactly the same physical identity through the isometry. -/
theorem orient_step (e : GridIsometry w h W H) {B : Board w h} {S T : LabelledState Label w h}
    (hs : LabelledState.Step B S T) : LabelledState.Step (e.board B) (orientLabels e S) (orientLabels e T) := by
  obtain ⟨d,hm,hupdate⟩ := hs
  have hn := Move.single_iff.mp (e.move (Move.single_iff.mpr hm))
  rcases hupdate with hw|hp
  · refine ⟨e.directions d,hn,Or.inl ⟨?_,?_⟩⟩
    · change T.state.boxes.map e.cells.toEmbedding=S.state.boxes.map e.cells.toEmbedding
      rw [hw.1]
    · funext i
      exact congrArg e.cells (congrFun hw.2 i)
  · obtain ⟨q,hq,ha,he,hb,hpos⟩ := hp
    refine ⟨e.directions d,hn,Or.inr ⟨e.cells q,?_,(e.adjacent d _ _).mpr ha,?_,?_,?_⟩⟩
    · exact (e.mem_boxes S.state _).mpr hq
    · exact fun h => he ((e.mem_boxes S.state q).mp h)
    · change T.state.boxes.map e.cells.toEmbedding=insert (e.cells q)
        (S.state.boxes.map e.cells.toEmbedding |>.erase (e.cells T.state.player))
      rw [hb,Finset.map_insert,Finset.map_erase]
      rfl
    · funext i
      change e.cells (T.position i)=shiftBox (e.cells T.state.player) (e.cells q) (e.cells (S.position i))
      rw [hpos,Function.comp_apply]
      exact map_shift e _ _ _

/-- Every intermediate full player/box state of the physical path is retained. -/
private theorem orient_path (e : GridIsometry w h W H) {B : Board w h}
    {S T : LabelledState Label w h}
    (hr : LabelledState.Reachable B S T) : LabelledState.Reachable (e.board B) (orientLabels e S) (orientLabels e T) :=
  hr.lift (orientLabels e) (fun _ _ hs => orient_step e hs)

variable {I : Instance} (M : SlotMatching I Label)

private theorem orient_initial {W H : ℕ} (e : GridIsometry I.width I.height W H) :
    orientLabels e M.initialLabelled=(M.reorient e).initialLabelled := rfl

/-- The same genuinely successful physical split survives complete-board reorientation. -/
theorem orient_successful {S final : LabelledState Label I.width I.height}
    (hs : Soundness.Successful M S final) {W H : ℕ} (e : GridIsometry I.width I.height W H) :
    Soundness.Successful (M.reorient e) (orientLabels e S) (orientLabels e final) := by
  refine ⟨?_,orient_path e hs.after,?_⟩
  · have hh := orient_path e hs.before
    rw [orient_initial] at hh
    exact hh
  · change final.state.boxes.map e.cells.toEmbedding=I.board.goals.map e.cells.toEmbedding
    rw [hs.solved]

private theorem original_component {W H : ℕ} (e : GridIsometry I.width I.height W H) (i j : Label)
    (hc : component (e.reorientInstance I).board ((M.reorient e).source i)=
      component (e.reorientInstance I).board ((M.reorient e).source j)) :
    component I.board (M.source i)=component I.board (M.source j) :=
  component_eq_iff.mpr ((e.sameComponent_iff I.board _ _).mp (component_eq_iff.mp hc))

/-- Static physical target order is invariant under horizontal reflection, including its reversed x-order. -/
theorem ordered_reflectX (ho : M.Ordered) : (M.reorient (GridIsometry.reflectX I.width I.height)).Ordered where
  horizontal i j hc hij := by
    have hc0 := original_component M (GridIsometry.reflectX I.width I.height) i j hc
    have hi := (M.source i).1.isLt
    have hj := (M.source j).1.isLt
    have hti := (M.target i).1.isLt
    have htj := (M.target j).1.isLt
    change I.width-((M.source i).1.val+1)<I.width-((M.source j).1.val+1) at hij
    have hrev : (M.source j).1.val<(M.source i).1.val := by omega
    have ht := ho.horizontal j i hc0.symm hrev
    change I.width-((M.target i).1.val+1)<I.width-((M.target j).1.val+1)
    omega
  vertical i j hc hij := by
    have hc0 := original_component M (GridIsometry.reflectX I.width I.height) i j hc
    exact ho.vertical i j hc0 hij

/-- A counterclockwise turn of the complete board uses the same actual box identities. -/
def counterclockwise (w h : ℕ) : GridIsometry w h h w :=
  (GridIsometry.reflectX w h).trans (GridIsometry.transpose w h)

def counterclockwiseAxis (w h : ℕ) : AxisIsometry w h h w :=
  (AxisIsometry.reflectX w h).trans (AxisIsometry.transpose w h)

/-- Both coordinate orders transform correctly under the quarter turn used to straighten the outgoing tail. -/
theorem ordered_counterclockwise (ho : M.Ordered) : (M.reorient (counterclockwise I.width I.height)).Ordered where
  horizontal i j hc hij := by
    have hc0 := original_component M (counterclockwise I.width I.height) i j hc
    exact ho.vertical i j hc0 hij
  vertical i j hc hij := by
    have hc0 := original_component M (counterclockwise I.width I.height) i j hc
    have hi := (M.source i).1.isLt
    have hj := (M.source j).1.isLt
    have hti := (M.target i).1.isLt
    have htj := (M.target j).1.isLt
    change I.width-((M.source i).1.val+1)<I.width-((M.source j).1.val+1) at hij
    have hrev : (M.source j).1.val<(M.source i).1.val := by omega
    have ht := ho.horizontal j i hc0.symm hrev
    change I.width-((M.target i).1.val+1)<I.width-((M.target j).1.val+1)
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Polyline
