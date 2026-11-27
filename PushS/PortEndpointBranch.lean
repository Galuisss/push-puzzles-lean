/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointFStock
public import PushS.EmptyFreeze
public import PushS.PortWalkBudget
public import PushS.PortReaderFreeze
public import PushS.PortDeeperBudget
import all PushS.PortWalkBudget
import all PushS.PortDeeperBudget
import all PushS.PortEndpointFStock
import all PushS.PortEndpointRWall
import all PushS.PortEndpointWide
import all PushS.PortEndpointCounts
import all PushS.PortEndpointSeparation
import all PushS.PortCentralStrip
import all PushS.PortStreetSeparation
import all PushS.PortBackground
import all PushS.PortPageBackground
import all PushS.PortSegments

/-!
# Permanent public branches of the last-level ordinary endpoints

The branch's open interval contains no column of its own page. Its vertical boundary is
therefore frozen page background. Its f end joins the established empty f corridor, and its
axis end is guarded by the actual inward r wall. The resulting empty-boundary argument
certifies the complete last-level reader region before any midpoint distance argument.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The actual open long branch between the f corridor and the ordinary axis. -/
@[expose] noncomputable def endpointLongBranch (p : Scales.Parameters) (e : Endpoint) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q =>
    q.2.val = (if e.side = .upper then readDepth p e.level + 2
      else p.H - (readDepth p e.level + 2)) ∧
    (if e.inward then EndpointStreet.f.column p e < q.1.val ∧ q.1.val < p.x e.port
      else p.x e.port < q.1.val ∧ q.1.val < EndpointStreet.f.column p e)

private theorem mem_endpointLongBranch (p : Scales.Parameters) (e : Endpoint)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointLongBranch p e ↔
      q.2.val = (if e.side = .upper then readDepth p e.level + 2
        else p.H - (readDepth p e.level + 2)) ∧
      (if e.inward then EndpointStreet.f.column p e < q.1.val ∧ q.1.val < p.x e.port
        else p.x e.port < q.1.val ∧ q.1.val < EndpointStreet.f.column p e) := by
  classical
  simp only [endpointLongBranch, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The f corridor together with its public long branch. -/
@[expose] noncomputable def endpointPublicWalk (p : Scales.Parameters) (e : Endpoint) :
    Finset (Cell (p.W + 1) (p.H + 1)) := endpointFWalk p e ∪ endpointLongBranch p e

private theorem longBranch_contains_iff (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (q : Cell (p.W + 1) (p.H + 1)) :
    (segment (inward (EndpointStreet.f.column p e) e.inward 1)
      (onSide (coordinates p) e.side (readDepth p e.level + 2))
      (outward (p.x e.port) e.inward 1)
      (onSide (coordinates p) e.side (readDepth p e.level + 2))).Contains (q.1.val, q.2.val) ↔
      q ∈ endpointLongBranch p e := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hL := readLength_ge p hj hm
  have hx := readLength_add_lt_x p e.port e.level
  have hH : (coordinates p).H = p.H := rfl
  rw [mem_endpointLongBranch, EndpointStreet.column_f]
  cases hd : e.inward <;> cases hs : e.side <;>
    simp [segment, Segment.Contains, inward, outward, onSide, hH] <;> omega

/-- Every actual long-branch cell is emitted as a hole for all signal bits. -/
theorem endpointLongBranch_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointLongBranch p e ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨_, List.mem_append_left _ (l.endpointFixedSegments_mem_fixed p hl hM e he ?_),
    (longBranch_contains_iff l p hl hM e he q).mpr hq⟩
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

private theorem branch_not_pageColumn (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointLongBranch p e) :
    q.1 ∉ l.pageColumnSet p e.side := by
  have hb := (mem_endpointLongBranch p e q).mp hq
  rw [EndpointStreet.column_f] at hb
  have hL := readLength_le_last p e.level
  have hnear : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 12 := by
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb <;>
      simp only [Nat.dist] <;> omega
  intro hc
  have hcols := nearby_page_columns l p hl ha he hc hnear
  have hx : (coordinates p).x e.port = p.x e.port := rfl
  have hlength : (coordinates p).length e.level = readLength p e.level := rfl
  cases hd : e.inward <;>
    simp only [auxiliary, inward, outward, hd, Bool.false_eq_true, ite_true, ite_false, hx, hlength] at hcols hb <;>
    omega

private theorem branch_vertical_blocker (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {q a : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointLongBranch p e) {d : Direction}
    (hd : d = .north ∨ d = .south) (hadj : Adjacent d a q) : a ∈ l.pageFrozenBlockers p hl := by
  have hcol := branch_not_pageColumn l p hl ha he hq
  have hr := (mem_endpointLongBranch p e q).mp hq
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  have hYeven := readDepth_even p e.level
  have hHeven := H_even p
  apply off_page_blocker l p hl
  intro hp
  have hside : if e.side = .upper then a.2.val < p.D else p.D < a.2.val := by
    rcases hd with rfl | rfl <;> cases hs : e.side <;>
      simp only [hs, reduceCtorEq, ite_true, ite_false, Adjacent] at hadj hr ⊢ <;> omega
  rcases (l.page_support_iff_side p hl e.side a hside).mp hp with hy | hc
  · have heven := l.workingRowSet_even p hy
    rcases hd with rfl | rfl <;> cases hs : e.side <;>
      simp only [hs, reduceCtorEq, ite_true, ite_false, Adjacent] at hadj hr <;> omega
  · rcases hd with rfl | rfl <;> exact hcol (hadj.1.symm ▸ hc)

private theorem branch_horizontal_back_coordinates (p : Scales.Parameters) (e : Endpoint)
    {q a b : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointLongBranch p e)
    (haP : a ∉ endpointPublicWalk p e) {d : Direction} (hd : d = .east ∨ d = .west)
    (ha : Adjacent d a q) (hb : Adjacent d b a) :
    b.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) ∧
      b.2.val = (if e.side = .upper then readDepth p e.level + 2 else p.H - (readDepth p e.level + 2)) := by
  have hq' := (mem_endpointLongBranch p e q).mp hq
  have hay : a.2 = q.2 := by rcases hd with rfl | rfl <;> exact ha.2.symm
  have hby : b.2 = q.2 := by rcases hd with rfl | rfl <;> exact hb.2.symm.trans hay
  have haNot : ¬(if e.inward then EndpointStreet.f.column p e < a.1.val ∧ a.1.val < p.x e.port
      else p.x e.port < a.1.val ∧ a.1.val < EndpointStreet.f.column p e) := by
    intro h
    exact haP (Finset.mem_union_right _ ((mem_endpointLongBranch p e a).mpr
      ⟨(congrArg Fin.val hay).trans hq'.1, h⟩))
  have hane : a.1.val ≠ EndpointStreet.f.column p e := by
    intro h
    exact haP (Finset.mem_union_left _ ((mem_endpointFWalk p e a).mpr
      ⟨h, readDepth p e.level + 2, le_rfl, (congrArg Fin.val hay).trans hq'.1⟩))
  have hbx : b.1.val = if e.inward then p.x e.port + 1 else p.x e.port - 1 := by
    rcases hd with rfl | rfl <;> cases hi : e.inward <;>
      simp only [hi, Bool.false_eq_true, ite_true, ite_false, Adjacent] at ha hb hq' haNot ⊢ <;> omega
  exact ⟨hbx, (congrArg Fin.val hby).trans hq'.1⟩

private theorem branch_horizontal_back (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (e : Endpoint) (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)
    {q a b : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointLongBranch p e)
    (haP : a ∉ endpointPublicWalk p e) {d : Direction} (hd : d = .east ∨ d = .west)
    (ha : Adjacent d a q) (hb : Adjacent d b a) :
    b ∈ l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g := by
  obtain ⟨hbx, hby⟩ := branch_horizontal_back_coordinates p e hq haP hd ha hb
  have hrow : InwardRow p e g.cell b := by
    constructor
    · apply Fin.ext
      have hd : readDepth p e.level = p.Y p.levels := by rw [heM, readDepth_eq p p.levels_pos le_rfl]
      rw [hby, g.row]
      simp only [hd]
    · have hforward := g.forward
      have hx := readLength_add_lt_x p e.port 0
      cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hbx hforward ⊢ <;> omega
  exact (r_wall_row_point l p hl e g b hrow).elim (Finset.mem_union_right _)
    (Finset.mem_union_left _)

/-- A fixed f-side background and the actual axis-side back neighbours protect the complete
public f walk and long branch at any level. -/
theorem endpointPublicWalk_emptyBoundary_of_back (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hback : ∀ b : Cell (p.W + 1) (p.H + 1),
      b.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) →
      b.2.val = (if e.side = .upper then readDepth p e.level + 2
        else p.H - (readDepth p e.level + 2)) → b ∈ G) :
    Freeze.EmptyBoundary (endpointPublicWalk p e) (endpointFWalk p e) G := by
  constructor
  intro d q a b hq hqH hadj haP hadj'
  have hbranch : q ∈ endpointLongBranch p e := (Finset.mem_union.mp hq).resolve_left hqH
  cases d with
  | north => exact Or.inl (hpage (branch_vertical_blocker l p hl ha he hbranch (Or.inl rfl) hadj))
  | south => exact Or.inl (hpage (branch_vertical_blocker l p hl ha he hbranch (Or.inr rfl) hadj))
  | east =>
    obtain ⟨hx, hy⟩ := branch_horizontal_back_coordinates p e hbranch haP (Or.inl rfl) hadj hadj'
    exact Or.inr (hback b hx hy)
  | west =>
    obtain ⟨hx, hy⟩ := branch_horizontal_back_coordinates p e hbranch haP (Or.inr rfl) hadj hadj'
    exact Or.inr (hback b hx hy)

/-- The actual long branch joins the established empty f walk at one end and the frozen
r wall at the other; its vertical boundary lies outside the page support. -/
theorem endpointPublicWalk_emptyBoundary (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels) :
    Freeze.EmptyBoundary (endpointPublicWalk p e) (endpointFWalk p e)
      (l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g) := by
  refine ⟨?_⟩
  intro d q a b hq hqH hadj haP hback
  have hbranch : q ∈ endpointLongBranch p e := (Finset.mem_union.mp hq).resolve_left hqH
  cases d with
  | north => exact Or.inl (Finset.mem_union_left _ (branch_vertical_blocker l p hl ha he hbranch (Or.inl rfl) hadj))
  | south => exact Or.inl (Finset.mem_union_left _ (branch_vertical_blocker l p hl ha he hbranch (Or.inr rfl) hadj))
  | east => exact Or.inr (branch_horizontal_back l p hl e g heM hbranch haP (Or.inl rfl) hadj hback)
  | west => exact Or.inr (branch_horizontal_back l p hl e g heM hbranch haP (Or.inr rfl) hadj hback)

/-- Both components of an endpoint's public walk are holes of every actual encoding. -/
theorem endpointPublicWalk_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointPublicWalk p e ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  exact (Finset.mem_union.mp hq).elim
    (fun h => l.endpointFWalk_subset_encoded p hl hM ha state e he h)
    (fun h => l.endpointLongBranch_subset_encoded p hl hM state e he h)

/-- A guarded actual prefix preserves the public long branch once the f corridor is empty
throughout the same successful suffix. -/
theorem physicalInstance_endpoint_publicWalk_empty_of_avoiding (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (G : Finset (Cell (p.W + 1) (p.H + 1)))
    (hboundary : Freeze.EmptyBoundary (endpointPublicWalk p e) (endpointFWalk p e) G)
    {u t : State (p.W + 1) (p.H + 1)}
    (hr : Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none G)
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (hF : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t → endpointFWalk p e ⊆ holes s) :
    endpointPublicWalk p e ⊆ holes u := by
  apply hboundary.reachable_holes
  · apply enrich_path hr
    intro a b hsa hm hbu
    refine ⟨hm, hF b ?_ ?_⟩
    · exact Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ (hsa.tail hm)
    · exact (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbu).trans hut
  · change endpointPublicWalk p e ⊆
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ
    rw [compl_compl]
    exact l.endpointPublicWalk_subset_encoded p hl hM ha initial e he

/-- The complete public walk of a last-level ordinary endpoint stays empty throughout
every successful actual physical play. -/
theorem physicalInstance_endpoint_publicWalk_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    endpointPublicWalk p e ⊆ holes u := by
  obtain ⟨g⟩ := l.endpointWideSeparator_nonempty p hl ha he
  have hr := l.physicalInstance_endpoint_rwall_avoiding p hl hM ha initial target e he g heM hsu hut ht
  exact l.physicalInstance_endpoint_publicWalk_empty_of_avoiding p hl hM ha initial target e he
    (l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g)
    (l.endpointPublicWalk_emptyBoundary p hl ha e he g heM) hr hut
    (fun _ hs ht' => l.physicalInstance_endpoint_fwalk_empty p hl hM ha initial target e he heM hs ht' ht)

private theorem reader_piece_public (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    {j : ℕ} (heq : e.level = j) {s : Segment} {k : ℕ}
    (hk : (s, k) ∈ ((endpointFixedSegments l (coordinates p) e).take 3).zipIdx)
    (hsel : if k = 1 then j < e.level else j ≤ e.level)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : s.Contains (q.1.val, q.2.val)) :
    q ∈ endpointPublicWalk p e := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hk3 : k < 3 := by
    have hb := List.snd_lt_of_mem_zipIdx hk
    rw [List.length_take] at hb
    omega
  have hk1 : k ≠ 1 := by intro h; simp only [h, ite_true, heq, lt_self_iff_false] at hsel
  have hread := List.mem_zipIdx_iff_getElem?.mp hk
  rw [List.getElem?_take_of_lt hk3] at hread
  rcases (show k = 0 ∨ k = 2 by omega) with rfl | rfl
  · simp only [endpointFixedSegments, List.cons_append, List.getElem?_cons_zero,
      Option.some.injEq] at hread
    subst s
    have hc := vertical_coordinates hq
    apply Finset.mem_union_left
    apply (mem_endpointFWalk_iff p e q).mpr
    refine ⟨hc.1, ?_⟩
    have hlow := readDepth_ge p hj hm
    have hhigh := readDepth_add_lt_H p e.level
    have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
    have hH : (coordinates p).H = p.H := rfl
    cases hs : e.side <;>
      simp only [onSide, hs, reduceCtorEq, ite_true, ite_false, hd, hH] at hc ⊢ <;> omega
  · simp only [endpointFixedSegments, List.cons_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at hread
    subst s
    exact Finset.mem_union_right _ ((longBranch_contains_iff l p hl hM e he q).mp hq)

private theorem last_reader_piece (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    {s : Segment} {k : ℕ}
    (hk : (s, k) ∈ ((endpointFixedSegments l (coordinates p) e).take 3).zipIdx)
    (hsel : if k = 1 then p.levels < e.level else p.levels ≤ e.level)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : s.Contains (q.1.val, q.2.val)) :
    e.level = p.levels ∧ q ∈ endpointPublicWalk p e := by
  have hm := (l.endpoints_level_bounds p hl hM he).2
  have heM : e.level = p.levels := by split_ifs at hsel <;> omega
  exact ⟨heM, reader_piece_public l p hl hM he heM hk hsel hq⟩

/-- The actual reader region uses deeper public segments or this level's f walk and long branch. -/
theorem readerWalkHoles_subset_of_deeper_public (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (j : ℕ)
    (R : Finset (Cell (p.W + 1) (p.H + 1))) (hD : l.deeperWalkHoles p j ⊆ R)
    (hC : ∀ e ∈ l.endpoints, e.level = j → endpointPublicWalk p e ⊆ R) :
    l.readerWalkHoles p j ⊆ R := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact hD (Finset.mem_union_left _ hf)
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨⟨seg, k⟩, hk, hs⟩ := List.mem_filterMap.mp hs
  dsimp only at hs
  have hsel : if k = 1 then j < e.level else j ≤ e.level := by
    by_contra h
    rw [ite_eq_right h] at hs
    cases hs
  rw [ite_eq_left hsel] at hs
  have heq : seg = s := Option.some.inj hs
  subst seg
  by_cases hgt : j < e.level
  · apply hD
    apply Finset.mem_union_right
    apply (SegmentRecipe.mem_holes _ q).mpr
    refine ⟨s, List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, ?_⟩,
      List.fst_mem_of_mem_zipIdx hk⟩, hcontains⟩
    exact decide_eq_true hgt
  · have hj : e.level = j := by split_ifs at hsel <;> omega
    exact hC e he hj (reader_piece_public l p hl hM he hj hk hsel hcontains)

/-- At the last allocated level the actual reader region consists only of the frame and
permanent f corridors with their long branches; no r corridor passes the level filter. -/
theorem physicalInstance_readerWalk_last_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.readerWalkHoles p p.levels ⊆ holes u := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · have htf : Disjoint t.boxes Boundary.frame := by
      apply Finset.disjoint_left.mpr
      intro r hr hrf
      have hh := l.encodedSegments_frame_subset p target hrf
      rw [← l.physicalInstance_goal_holes p hl hM ha initial target, ← ht] at hh
      exact (Finset.mem_compl.mp hh) hr
    exact (mem_holes _).mpr fun hb => Finset.disjoint_left.mp (Boundary.reachable_frame_empty hut htf) hb hf
  · obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨⟨z, k⟩, hk, hs⟩ := List.mem_filterMap.mp hs
    dsimp only at hs
    have hsel : if k = 1 then p.levels < e.level else p.levels ≤ e.level := by
      by_contra h
      rw [ite_eq_right h] at hs
      cases hs
    rw [ite_eq_left hsel] at hs
    have heq : z = s := Option.some.inj hs
    subst z
    obtain ⟨heM, hpublic⟩ := last_reader_piece l p hl hM he hk hsel hcontains
    exact l.physicalInstance_endpoint_publicWalk_empty p hl hM ha initial target e he heM hsu hut ht hpublic

/-- Every actual last-level reader midpoint on a selected row stays empty and unvisited. -/
theorem physicalInstance_reader_last_midpoints_excluded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Blocked.Excluded (l.readerMidpointRows p p.levels) u :=
  l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target p.levels hsu hut ht
    (fun _ hs ht' => l.physicalInstance_readerWalk_last_empty p hl hM ha initial target hs ht' ht)

end PushPuzzle.PushS.PortLayout
