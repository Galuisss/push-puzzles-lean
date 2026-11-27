/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.PortalWalking
public import PushFS.Gadgets.Wires.Catalog.PhaseMarks
public import PushFS.Gadgets.Wires.Catalog.PlayerPhases
public import PushFS.WallCongruence

/-! Actual corner access in all seven padded ordinary macrocells with arbitrary two-phase neighbor slots. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Reduction
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board Chain.boxes Chain.walls

private theorem native_wall_chart (k : Kind) (a b : Bool) :
    (nativeEmbedding k a b (GridIsometry.refl width height).embedding).WallsAgree (native k a b).board (puzzle k a b).board := by
  intro p
  change (GridEmbedding.translate (dx k) (dy k) (fitsX k a b) (fitsY k a b)).cells
    ((nativeIsometry k a b).cells p)∈(puzzle k a b).board.walls ↔p∈(native k a b).board.walls
  have hp:=placed_walls (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)
    ((nativeIsometry k a b).cells p)
  have he:=congrArg (fun B : Board (base k a b).width (base k a b).height=>
    (nativeIsometry k a b).cells p∈B.walls) (native_board k a b)
  exact hp.trans ((Eq.to_iff he).symm.trans ((nativeIsometry k a b).mem_walls _ p))

private theorem chain_allNeighbors_iff (n : ℕ) (p : Chain.C n) :
    p∈Chain.allNeighbors n ↔p.2.val=10 ∧(p.1.val≤1 ∨n+2≤p.1.val) := by
  constructor
  · exact Chain.allNeighbors_bounds n
  · rintro ⟨hy,hx⟩
    have hb:=p.1.isLt
    have he : p.1.val=0 ∨p.1.val=1 ∨p.1.val=n+2 ∨p.1.val=n+3 ∨p.1.val=n+4 := by omega
    simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton]
    rcases he with he|he|he|he|he
    · exact Or.inl (Prod.ext (Fin.ext he) (Fin.ext hy))
    · exact Or.inr (Or.inl (Prod.ext (Fin.ext he) (Fin.ext hy)))
    · exact Or.inr (Or.inr (Or.inl (Prod.ext (Fin.ext he) (Fin.ext hy))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext (Fin.ext he) (Fin.ext hy)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext (Fin.ext he) (Fin.ext hy)))))

private theorem ident_extend (fixed : Finset Cell) (s : State width height) :
    (GridIsometry.refl width height).embedding.extend fixed s=⟨s.player,s.boxes∪fixed⟩ := by
  apply State.ext
  · rfl
  · exact congrArg (fun xs : Finset Cell=>xs∪fixed) Finset.map_refl

private theorem native_source_fixed (k : Kind) (a b : Bool) (fixed : Finset Cell) :
    (nativeEmbedding k a b (GridIsometry.refl width height).embedding).extend fixed (native k a b).initial=
      ⟨(puzzle k a b).initial.player,(puzzle k a b).initial.boxes∪fixed⟩ :=
  (native_place_initial k a b _ fixed).trans (ident_extend fixed _)

private theorem native_portal_fixed (k : Kind) (a b : Bool) (fixed : Finset Cell) (i : Fin 4) :
    (nativeEmbedding k a b (GridIsometry.refl width height).embedding).extend fixed
      ⟨nativePortal k a b i,(native k a b).initial.boxes⟩=
      ⟨portal k a b i,(puzzle k a b).initial.boxes∪fixed⟩ := by
  apply State.ext
  · rfl
  · have hh:=congrArg (fun s : State width height=>s.boxes) (native_source_fixed k a b fixed)
    exact hh

private theorem chain_portals_foreign {W H : ℕ} (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (n+5) 21 W H) (B : Board W H) (outside : Finset (PushFS.Cell W H))
    (hw : e.WallsAgree (Chain.puzzle n hn a b).board B) (hf : Disjoint outside B.walls)
    (hc : ∀p : Chain.C n,e.cells p∈outside→p∈Chain.allNeighbors n) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (Chain.puzzle n hn a b).initial)
      (e.extend outside ⟨Chain.corner n i,(Chain.puzzle n hn a b).initial.boxes⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨Chain.corner n i,(Chain.puzzle n hn a b).initial.boxes⟩)
      (e.extend outside (Chain.puzzle n hn a b).initial) := by
  have hcollar : Polyline.Frame.fixed e outside⊆Chain.allNeighbors n := by
    intro p hp
    exact hc p ((Polyline.Frame.mem_fixed e outside p).mp hp)
  exact Chain.corners_placed_allNeighbors n hn (Chain.uniform n a) i (Polyline.Frame.fixed e outside)
    hcollar e hw (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf

/-- Every real native portal remains accessible with all possible canonical neighboring endpoint boxes. -/
private theorem portal_corners (k : Kind) (a b : Bool) (fixed : Finset Cell)
    (hm : ∀p∈fixed,WalkingMask k p) (i : Fin 4) :
    Reachable (puzzle k a b).board (some 1)
      ⟨(puzzle k a b).initial.player,(puzzle k a b).initial.boxes∪fixed⟩
      ⟨portal k a b i,(puzzle k a b).initial.boxes∪fixed⟩ ∧
    Reachable (puzzle k a b).board (some 1)
      ⟨portal k a b i,(puzzle k a b).initial.boxes∪fixed⟩
      ⟨(puzzle k a b).initial.player,(puzzle k a b).initial.boxes∪fixed⟩ := by
  let e:=nativeEmbedding k a b (GridIsometry.refl width height).embedding
  have hw:=native_wall_chart k a b
  have hf : Disjoint fixed (puzzle k a b).board.walls :=
    Finset.disjoint_left.mpr (fun p hp=>external_rail_floor k a b (walkingMask_rail k p (hm p hp)))
  have hn : Reachable (puzzle k a b).board (some 1) (e.extend fixed (native k a b).initial)
      (e.extend fixed ⟨nativePortal k a b i,(native k a b).initial.boxes⟩) ∧
    Reachable (puzzle k a b).board (some 1)
      (e.extend fixed ⟨nativePortal k a b i,(native k a b).initial.boxes⟩)
      (e.extend fixed (native k a b).initial) := by
    cases k
    · have hc : ∀p : Chain.C 200000,e.cells p∈fixed→p∈Chain.allNeighbors 200000 := by
        intro p hp
        have hh:=hm (e.cells p) hp
        change 99023+p.2.val=99033 ∧(0+p.1.val≤1 ∨200002≤0+p.1.val) at hh
        apply (chain_allNeighbors_iff 200000 p).mpr
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      exact chain_portals_foreign 200000 (by decide) a b e (puzzle .east a b).board fixed hw hf hc i
    · have hc : ∀p : Chain.C 200000,e.cells p∈fixed→p∈Chain.allNeighbors 200000 := by
        intro p hp
        have hh:=hm (e.cells p) hp
        change 99023+p.2.val=99033 ∧(0+(200005-(p.1.val+1))≤2 ∨200003≤0+(200005-(p.1.val+1))) at hh
        apply (chain_allNeighbors_iff 200000 p).mpr
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      exact chain_portals_foreign 200000 (by decide) a b e (puzzle .west a b).board fixed hw hf hc i
    · have hc : ∀p : Chain.C 198061,e.cells p∈fixed→p∈Chain.allNeighbors 198061 := by
        intro p hp
        have hh:=hm (e.cells p) hp
        change 99992+(21-(p.2.val+1))=100002 ∧(0+p.1.val≤1 ∨198063≤0+p.1.val) at hh
        apply (chain_allNeighbors_iff 198061 p).mpr
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      exact chain_portals_foreign 198061 (by decide) a b e (puzzle .south a b).board fixed hw hf hc i
    · have he : e.WallsAgree (Polyline.L.board 99970 98999 (by decide) (by decide)
          (Polyline.L.boxes 99970 98999 (by decide) (by decide) (Polyline.L.uniform b))) (puzzle .westSouth a b).board := by
        simpa only [native,StorageAtlas.puzzle,Polyline.L.board_eq] using hw
      have hno : ∀p : Turn.C,((Polyline.L.turnRect 99970 98999 (by decide) (by decide)).trans e).cells p∉fixed := by
        intro p hp
        have hh:=hm _ hp
        change WalkingMask .westSouth
          (⟨99992+(0+p.1.val),by dsimp only [width,height]; omega⟩,⟨99023+(1+p.2.val),by dsimp only [width,height]; omega⟩) at hh
        dsimp only [WalkingMask] at hh
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      have ht:=Polyline.L.turn_corners_foreign 99970 98999 (by decide) (by decide)
        (Polyline.L.boxes 99970 98999 (by decide) (by decide) (Polyline.L.uniform b)) (Polyline.L.uniform a)
        e (puzzle .westSouth a b).board fixed he hf hno i
      have hs : (native .westSouth a b).initial=Polyline.L.state 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) :=
        Polyline.L.initial_state 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)
      rw [hs]
      exact ht
    · have he : e.WallsAgree (Out.board 99970 98979 (by decide) (by decide)
          (Out.boxes 99970 98979 (by decide) (by decide) (Out.uniform b))) (puzzle .eastSouth a b).board := by
        simpa only [native,StorageAtlas.puzzle,Out.board_eq] using hw
      have hno : ∀p : Turn.C,((Out.turnRect 99970 98979 (by decide) (by decide)).trans e).cells p∉fixed := by
        intro p hp
        have hh:=hm _ hp
        change WalkingMask .eastSouth
          (⟨0+(100013-((0+p.1.val)+1)),by dsimp only [width,height]; omega⟩,⟨99023+(1+p.2.val),by dsimp only [width,height]; omega⟩) at hh
        dsimp only [WalkingMask] at hh
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      have ht:=Out.turn_corners_foreign 99970 98979 (by decide) (by decide)
        (Out.boxes 99970 98979 (by decide) (by decide) (Out.uniform b)) (Out.uniform a)
        e (puzzle .eastSouth a b).board fixed he hf hno i
      have hs : (native .eastSouth a b).initial=Out.state 99970 98979 (by decide) (by decide) (Out.uniform a) :=
        Out.initial_state 99970 98979 (by decide) (by decide) (Out.uniform a) (Out.uniform b)
      rw [hs]
      exact ht
    · have he : e.WallsAgree (In.board 98981 99969 (by decide) (by decide)
          (In.boxes 98981 99969 (by decide) (by decide) (In.uniform b))) (puzzle .southEast a b).board := by
        simpa only [native,StorageAtlas.puzzle,In.board_eq] using hw
      have hno : ∀p : Turn.C,((In.turnRect 98981 99969 (by decide) (by decide)).trans e).cells p∉fixed := by
        intro p hp
        have hh:=hm _ hp
        change WalkingMask .southEast
          (⟨99992+(1+p.2.val),by dsimp only [width,height]; omega⟩,⟨0+(99044-((0+p.1.val)+1)),by dsimp only [width,height]; omega⟩) at hh
        dsimp only [WalkingMask] at hh
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      have ht:=In.turn_corners_foreign 98981 99969 (by decide) (by decide)
        (In.boxes 98981 99969 (by decide) (by decide) (In.uniform b)) (In.uniform a)
        e (puzzle .southEast a b).board fixed he hf hno i
      have hs : (native .southEast a b).initial=In.state 98981 99969 (by decide) (by decide) (In.uniform a) :=
        In.initial_state 98981 99969 (by decide) (by decide) (In.uniform a) (In.uniform b)
      rw [hs]
      exact ht
    · have he : e.WallsAgree (Polyline.L.board 99001 99969 (by decide) (by decide)
          (Polyline.L.boxes 99001 99969 (by decide) (by decide) (Polyline.L.uniform b))) (puzzle .southWest a b).board := by
        simpa only [native,StorageAtlas.puzzle,Polyline.L.board_eq] using hw
      have hno : ∀p : Turn.C,((Polyline.L.turnRect 99001 99969 (by decide) (by decide)).trans e).cells p∉fixed := by
        intro p hp
        have hh:=hm _ hp
        change WalkingMask .southWest
          (⟨0+(100013-((1+p.2.val)+1)),by dsimp only [width,height]; omega⟩,⟨0+(99044-((0+p.1.val)+1)),by dsimp only [width,height]; omega⟩) at hh
        dsimp only [WalkingMask] at hh
        have hx:=p.1.isLt
        have hy:=p.2.isLt
        omega
      have ht:=Polyline.L.turn_corners_foreign 99001 99969 (by decide) (by decide)
        (Polyline.L.boxes 99001 99969 (by decide) (by decide) (Polyline.L.uniform b)) (Polyline.L.uniform a)
        e (puzzle .southWest a b).board fixed he hf hno i
      have hs : (native .southWest a b).initial=Polyline.L.state 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) :=
        Polyline.L.initial_state 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)
      rw [hs]
      exact ht
  dsimp only [e] at hn
  rw [native_source_fixed,native_portal_fixed] at hn
  exact hn

/-- All four literal rectangle corners communicate with the actual common player. -/
private theorem exterior_corners (k : Kind) (a b : Bool) (fixed : Finset Cell)
    (hm : ∀p∈fixed,WalkingMask k p) (i : Fin 4) :
    Reachable (puzzle k a b).board (some 1)
      ⟨(puzzle k a b).initial.player,(puzzle k a b).initial.boxes∪fixed⟩
      ⟨outerCorner i,(puzzle k a b).initial.boxes∪fixed⟩ ∧
    Reachable (puzzle k a b).board (some 1)
      ⟨outerCorner i,(puzzle k a b).initial.boxes∪fixed⟩
      ⟨(puzzle k a b).initial.player,(puzzle k a b).initial.boxes∪fixed⟩ := by
  obtain ⟨j,hj⟩:=portal_quadrant_exists k a b i
  have hp:=portal_corners k a b fixed hm j
  have hm' : ∀p∈fixed,ExternalRail p:=fun p hp=>walkingMask_rail k p (hm p hp)
  exact ⟨hp.1.trans (quadrant_walk k a b fixed hm' i _ _ hj (outerCorner_quadrant i)),
    (quadrant_walk k a b fixed hm' i _ _ (outerCorner_quadrant i) hj).trans hp.2⟩

/-- Either complete canonical endpoint inventory admits the same actual corner walks. -/
theorem selected_corners (k : Kind) (a b goal : Bool) (fixed : Finset Cell)
    (hm : ∀p∈fixed,WalkingMask k p) (i : Fin 4) :
    let boxes:=(if goal then (puzzle k a b).board.goals else (puzzle k a b).initial.boxes)∪fixed
    Reachable (puzzle k a b).board (some 1) ⟨(puzzle k a b).initial.player,boxes⟩ ⟨outerCorner i,boxes⟩ ∧
    Reachable (puzzle k a b).board (some 1) ⟨outerCorner i,boxes⟩ ⟨(puzzle k a b).initial.player,boxes⟩ := by
  cases goal
  · exact exterior_corners k a b fixed hm i
  · dsimp only [ite_true]
    have hr:=exterior_corners k b b fixed hm i
    have hw:=puzzle_walls_eq k b b a b
    have h₁:=hr.1.reboard hw
    have h₂:=hr.2.reboard hw
    have hp : @Eq Cell (puzzle k b b).initial.player (puzzle k a b).initial.player := player_same k b b a b
    have hb : @Eq (Finset Cell) ((puzzle k b b).initial.boxes∪fixed) ((puzzle k a b).board.goals∪fixed) :=
      congrArg (fun xs : Finset Cell=>xs∪fixed) (goals_canonical k a b).symm
    have hs : (⟨(puzzle k b b).initial.player,(puzzle k b b).initial.boxes∪fixed⟩ : State width height)=
        ⟨(puzzle k a b).initial.player,(puzzle k a b).board.goals∪fixed⟩ := State.ext hp hb
    have ht : (⟨outerCorner i,(puzzle k b b).initial.boxes∪fixed⟩ : State width height)=
        ⟨outerCorner i,(puzzle k a b).board.goals∪fixed⟩ := State.ext rfl hb
    exact ⟨Eq.mp (congrArg₂ (@Reachable width height (puzzle k a b).board (some 1)) hs ht) h₁,
      Eq.mp (congrArg₂ (@Reachable width height (puzzle k a b).board (some 1)) ht hs) h₂⟩

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
