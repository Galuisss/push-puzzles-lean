/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RailHorizontal
public import PushFS.Gadgets.Wires.Soundness.Chain
public import PushFS.Gadgets.Wires.Polyline.Endpoints

/-! Arbitrary physical train signals derived from actual source SCCs and C1–C3, independently of global axis levels. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Soundness

variable {I : Instance} {Label : Type} [Fintype Label]

/-- Exact static all-slot placement of an arbitrary physical 40/59 chain in a larger assembly. -/
structure ChainRailGlyph (M : SlotMatching I Label) (n : ℕ) (hn : 2301 ≤ n) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+(n+5) ≤ I.width
  fit_y : dy+21 ≤ I.height
  initialPhase : Bool
  targetPhase : Bool
  labels : Chain.Label n ↪ Label
  walls : (GridEmbedding.translate dx dy fit_x fit_y).WallsAgree (Chain.board n hn ∅) I.board
  sources : ∀ i, M.source (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (Chain.position n hn (Chain.uniform n initialPhase) i)
  targets : ∀ i, M.target (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (Chain.position n hn (Chain.uniform n targetPhase) i)

namespace ChainRailGlyph

variable {M : SlotMatching I Label} {n : ℕ} {hn : 2301 ≤ n}
    (g : ChainRailGlyph M n hn) {S final : LabelledState Label I.width I.height}

theorem block_fit (i : Chain.Block n) :
    g.dx+Chain.offset n i.val+(ChainGeometry.horizontalKind (Chain.kind n i)).width ≤ I.width := by
  have hh := Chain.fit n hn i
  rw [ChainGeometry.width]
  have hfit := g.fit_x
  omega

theorem block_cell (i : Chain.Block n)
    (p : Cell (ChainGeometry.horizontalKind (Chain.kind n i)).width 21) :
    (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells
        (Chain.embed n hn i (ChainGeometry.cell (Chain.kind n i) p)) =
      (GridEmbedding.translate (g.dx+Chain.offset n i.val) g.dy (g.block_fit i) g.fit_y).cells p := by
  apply Prod.ext <;> apply Fin.ext
  · change g.dx+(Chain.offset n i.val+p.1.val) = g.dx+Chain.offset n i.val+p.1.val
    omega
  · change g.dy+(0+p.2.val) = g.dy+p.2.val
    omega

/-- Every primitive block inherits its actual local walls and exact global physical identities. -/
def block (i : Chain.Block n) : HorizontalRailGlyph M (ChainGeometry.horizontalKind (Chain.kind n i)) where
  dx := g.dx+Chain.offset n i.val
  dy := g.dy
  fit_x := g.block_fit i
  fit_y := g.fit_y
  initialPhase := g.initialPhase
  targetPhase := g.targetPhase
  labels := ⟨fun u => g.labels ⟨i,ChainGeometry.index (Chain.kind n i) u⟩,by
    intro u v he
    have hh := congrArg (fun l : Chain.Label n => l.2.val) (g.labels.injective he)
    exact Fin.ext hh⟩
  walls := by
    intro p
    rw [← g.block_cell i p,g.walls]
    change Chain.embed n hn i (ChainGeometry.cell (Chain.kind n i) p) ∈ Chain.walls n hn ↔
      p ∈ (ChainGeometry.horizontalKind (Chain.kind n i)).template.walls
    rw [Chain.walls_exact,ChainGeometry.walls]
  sources := by
    intro u
    change M.source (g.labels ⟨i,ChainGeometry.index (Chain.kind n i) u⟩) = _
    rw [g.sources]
    have hh := ChainGeometry.position (Chain.kind n i) g.initialPhase u
    apply Prod.ext <;> apply Fin.ext
    · change g.dx+(Chain.offset n i.val+_)=g.dx+Chain.offset n i.val+_
      dsimp only [Chain.uniform]
      rw [hh.1]
      omega
    · change g.dy+(0+_)=g.dy+_
      dsimp only [Chain.uniform]
      rw [hh.2]
      omega
  targets := by
    intro u
    change M.target (g.labels ⟨i,ChainGeometry.index (Chain.kind n i) u⟩) = _
    rw [g.targets]
    have hh := ChainGeometry.position (Chain.kind n i) g.targetPhase u
    apply Prod.ext <;> apply Fin.ext
    · change g.dx+(Chain.offset n i.val+_)=g.dx+Chain.offset n i.val+_
      dsimp only [Chain.uniform]
      rw [hh.1]
      omega
    · change g.dy+(0+_)=g.dy+_
      dsimp only [Chain.uniform]
      rw [hh.2]
      omega

/-- Every true primitive label is connected on the complete physical train rail. -/
theorem component (i j : Chain.Label n) : component I.board (M.source (g.labels i))=component I.board (M.source (g.labels j)) := by
  rw [g.sources,g.sources]
  have hc:=ChainGeometry.slots_component n hn g.initialPhase i j
  exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hc.1,GridEmbedding.staticReach g.walls hc.2⟩

private def rail : SourceRail M true (g.dy+10) where
  anchor:=g.labels (Polyline.ChainEnds.first n hn)
  witness:=M.source (g.labels (Polyline.ChainEnds.last n hn))
  connected:=g.component _ _
  different:=by
    intro he
    rw [g.sources,g.sources] at he
    change g.dx+(Chain.position n hn (Chain.uniform n g.initialPhase) (Polyline.ChainEnds.last n hn)).1.val=
      g.dx+(Chain.position n hn (Chain.uniform n g.initialPhase) (Polyline.ChainEnds.first n hn)).1.val at he
    rw [Polyline.ChainEnds.last_x,Polyline.ChainEnds.first_x] at he
    omega
  anchor_cross:=by
    rw [g.sources]
    change g.dy+(Chain.position n hn (Chain.uniform n g.initialPhase) _).2.val=g.dy+10
    rw [Chain.position_row]

private theorem gap (h : Successful M S final) (cert : Certificate I)
    (i j : Chain.Label n) (ho : (Chain.position n hn (Chain.uniform n g.initialPhase) i).1.val<
      (Chain.position n hn (Chain.uniform n g.initialPhase) j).1.val) :
    (S.position (g.labels i)).1.val+2≤(S.position (g.labels j)).1.val := by
  apply g.rail.gap h cert (g.labels i) (g.labels j) (g.component _ _) (g.component _ _)
  rw [g.sources,g.sources]
  exact Nat.add_lt_add_left ho _

/-- Propagation into every block is derived from its predecessor's true endpoint and the actual seam gap. -/
private theorem block_input (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dx+3 ≤ (S.position (g.labels (ChainGeometry.firstLabel n (Chain.firstBlock n hn)))).1.val)
    (i : Chain.Block n) : g.dx+Chain.offset n i.val+3 ≤
      (S.position (g.labels (ChainGeometry.firstLabel n i))).1.val := by
  suffices hb : ∀ t (ht : t < Chain.blockCount n), g.dx+Chain.offset n t+3 ≤
      (S.position (g.labels (ChainGeometry.firstLabel n ⟨t,ht⟩))).1.val from hb i.val i.isLt
  intro t
  induction t with
  | zero =>
    intro ht
    have hz : Chain.offset n 0 = 0 := Chain.Spans.offset_zero n
    simpa only [Chain.firstBlock,hz,Nat.add_zero] using hin
  | succ t ih =>
    intro ht
    let i : Chain.Block n := ⟨t,by omega⟩
    let j : Chain.Block n := ⟨t+1,ht⟩
    have hp := (g.block i).signal h cert ho (ih i.isLt)
    have hg := g.gap h cert (ChainGeometry.lastLabel n i) (ChainGeometry.firstLabel n j)
      (Chain.position_block_order n hn _ i j (by change t < t+1; omega) _ _)
    have hoff := Chain.offset_next n t
    rw [← ChainGeometry.span] at hoff
    change g.dx+Chain.offset n t+(ChainGeometry.horizontalKind (Chain.kind n i)).span+1 ≤
      (S.position (g.labels (ChainGeometry.lastLabel n i))).1.val at hp
    change Chain.offset n (t+1) = Chain.offset n t+
      (ChainGeometry.horizontalKind (Chain.kind n i)).span at hoff
    change g.dx+Chain.offset n (t+1)+3 ≤ (S.position (g.labels (ChainGeometry.firstLabel n j))).1.val
    omega

/-- At every point of any real successful path, the far endpoint obeys the full-chain threshold. -/
theorem signal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dx+3 ≤ (S.position (g.labels (ChainGeometry.firstLabel n (Chain.firstBlock n hn)))).1.val) :
    g.dx+n+1 ≤ (S.position (g.labels (ChainGeometry.lastLabel n (Chain.lastBlock n hn)))).1.val := by
  have hp := (g.block (Chain.lastBlock n hn)).signal h cert ho (g.block_input h cert ho hin _)
  have hf := Chain.last_finish n hn
  rw [← ChainGeometry.span] at hf
  change g.dx+Chain.offset n (Chain.lastBlock n hn).val+
    (ChainGeometry.horizontalKind (Chain.kind n (Chain.lastBlock n hn))).span+1 ≤
      (S.position (g.labels (ChainGeometry.lastLabel n (Chain.lastBlock n hn)))).1.val at hp
  omega

end ChainRailGlyph
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
