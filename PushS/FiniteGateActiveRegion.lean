/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreGuardCoverage
public import PushS.FiniteRoutingPrimitiveGeometry

public import PushS.FiniteGeometrySimp

/-! The concrete region used by actual selected core macros and their two-step external supports. -/

public section
namespace PushPuzzle.PushS.FiniteGateActiveRegion

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteCoreGuardCoverage

attribute [local irreducible] FiniteGeometry.side Line.width Line.height Line.program Line.span

attribute [local finite_core_coords]
  coordinates BeforeColumn portAnchor PortAnnulus.innerDirection corePort coreWorld Line.along origin coreOffset padding spacing orRectangle Outward Line.PerpendicularBand Line.GuardSide coreSide andRectangle

/-- The exact outer support bounds of all core branch programs. -/
@[expose] def Envelope (w : ℕ) (kind : Bool) (p : ℕ × ℕ) : Prop :=
  let o := origin w
  if kind then o-8*w-18 ≤ p.1 ∧ p.1 ≤ o+3*w+14 ∧ o-8*w-33 ≤ p.2 ∧ p.2 ≤ o+2
  else o-2*w-9 ≤ p.1 ∧ p.1 ≤ o+3*w+15 ∧ o-2*w-15 ≤ p.2 ∧ p.2 ≤ o+2

attribute [local finite_core_coords] Envelope

/-- A selected core macro avoids the second low stock slot on either unselected arm. -/
@[expose] def Region (w : ℕ) (kind : Bool) (selected : Fin 3) (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) : Prop :=
  Envelope w kind (coordinates p) ∧ ∀ role : Fin 3,role ≠ selected →
    coreWorld w p ≠ Line.along w (PortAnnulus.innerDirection role) (corePort w kind role) 2

/-- Every point in the core program region is at most two columns outside each literal core port. -/
private theorem envelope_before_two (w : ℕ) (kind : Bool) (role : Fin 3)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : Envelope w kind (coordinates p)) :
    BeforeColumn (PortAnnulus.innerDirection role) (portAnchor w kind role) (coreWorld w p) 2 := by
  cases kind <;> fin_cases role <;>
    simp [finite_core_coords] at hp ⊢ <;> omega

/-- A real outward stock ray meets the core envelope only in its first three scalar cells. -/
theorem envelope_ray_bound (w : ℕ) (kind : Bool) (role : Fin 3) (n : ℕ)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : Envelope w kind (coordinates p))
    (he : Line.along w (PortAnnulus.innerDirection role) (corePort w kind role) n = coreWorld w p) : n ≤ 2 := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  cases kind <;> fin_cases role <;>
    simp [Envelope,coordinates,PortAnnulus.innerDirection,corePort,coreWorld,Line.along,origin,coreOffset,padding,spacing]
      at hp hx hy <;> omega

private def andGuard (role : Fin 3) : Fin 7 := if role = 0 then 5 else if role = 1 then 6 else 0
private def orGuard (role : Fin 3) : Fin 2 := if role = 1 then 1 else 0

attribute [local finite_core_coords] andGuard orGuard

-- Normalize the fixed rectangle cases before their linear arithmetic checks.
set_option maxRecDepth 8192 in
/-- Inside the concrete core envelope, an initial arm's literal guard side is already filled by an actual core wall rectangle. -/
private theorem envelope_guard_wall (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (role : Fin 3)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : Envelope w kind (coordinates p))
    (ho : Outward (PortAnnulus.innerDirection role) (portAnchor w kind role) (coreWorld w p))
    (hb : Line.PerpendicularBand w (PortAnnulus.innerDirection role) (portAnchor w kind role) (coreWorld w p))
    (hg : Line.GuardSide (PortAnnulus.innerDirection role) (coreSide kind role) (portAnchor w kind role) (coreWorld w p)) :
    p ∈ walls w kind := by
  cases kind with
  | false =>
    have hr : p ∈ (orRectangle w (orGuard role)).cells (FiniteGeometry.side w) (FiniteGeometry.side w) := by
      rw [Rectangle.mem_cells]
      fin_cases role <;>
        simp [finite_core_coords] at hp ho hb hg ⊢ <;> omega
    exact Finset.mem_biUnion.mpr ⟨orGuard role,Finset.mem_univ _,hr⟩
  | true =>
    have hr : p ∈ (andRectangle w (andGuard role)).cells (FiniteGeometry.side w) (FiniteGeometry.side w) := by
      rw [Rectangle.mem_cells]
      fin_cases role <;>
        simp [finite_core_coords] at hp ho hb hg ⊢ <;> omega
    exact Finset.mem_biUnion.mpr ⟨andGuard role,Finset.mem_univ _,hr⟩

/-- No initial arm wall covers any core-envelope cell that is actual core floor. -/
private theorem initial_wall_ne_floor (w length : ℕ) (hw : 2 ≤ w) (kind switch : Bool) (role : Fin 3)
    (C : InitialArmPlacement w length kind switch role)
    (a : Cell (Line.width w (Line.program w length switch)) (Line.height w))
    (ha : a ∈ Line.walls w (Line.program w length switch) (coreSide kind role))
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : Envelope w kind (coordinates p))
    (hfloor : p ∉ walls w kind) :
    coordinates ((Line.placement w (Line.program w length switch) (PortAnnulus.innerDirection role)
      (corePort w kind role) C.finish C.travels C.start_fits C.finish_fits).cells a) ≠ coreWorld w p := by
  rcases C with ⟨finish,ht,hs,hf⟩
  intro he
  have ho := (Line.placed_wall_side w (Line.program w length switch) (coreSide kind role)
    _ _ finish ht hs hf a ha).1
  have hb := Line.placed_wall_band w (Line.program w length switch) (coreSide kind role) _ _ finish ht hs hf a ha
  have hx : a.1.val ≤ FiniteTools.radius w+2 :=
    column_le_of_world_limit w (Line.program w length switch) (PortAnnulus.innerDirection role)
      (corePort w kind role) finish ht hs hf a 2 (he.symm ▸ envelope_before_two w kind role p hp)
  have hstart : a.1.val < FiniteTools.radius w+2*Line.buffer w := by unfold Line.buffer; omega
  have hband := Line.program_first_wall_band w length switch (coreSide kind role) a ha hstart
  have hg := placed_stock_band_guard w (Line.program w length switch) (coreSide kind role)
    (PortAnnulus.innerDirection role) (corePort w kind role) finish ht hs hf a hband
  rw [he] at ho hb hg
  exact hfloor (envelope_guard_wall w hw kind role p hp ho hb hg)

/-- The actual oriented first-line instruction leaves the entire core-envelope floor clear. -/
theorem initial_code_wall_ne_floor (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (role : Fin 3)
    (c : LineCode) (hc : LineGood w c.segment)
    (hstart : c.segment.start = corePort w kind role)
    (hdirection : segmentDirection c.segment = PortAnnulus.innerDirection role)
    (habove : c.above = coreSide kind role)
    (a : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (ha : a ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : Envelope w kind (coordinates p))
    (hfloor : p ∉ walls w kind) : (PrimitiveCode.line c).world w hw a ≠ coreWorld w p := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  change a ∈ (Line.walls w atoms c.above).map (Line.rotation w atoms (segmentDirection c.segment)).cells.toEmbedding at ha
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp ha
  have hq' : q ∈ Line.walls w atoms (coreSide kind role) :=
    Eq.mp (congrArg (fun ab => q ∈ Line.walls w atoms ab) habove) hq
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [Line.program_span_of_bound w _ _ hc.2.1]
    exact segment_travels _ hc.1
  have ht' : Travels (PortAnnulus.innerDirection role) (corePort w kind role) c.segment.finish (Line.span w atoms) := by
    simpa only [hdirection,hstart] using ht
  have hs : (corePort w kind role).1 ≤ tileStride w ∧ (corePort w kind role).2 ≤ tileStride w := hstart ▸ hc.2.2.1
  have hw'' : (PrimitiveCode.line c).world w hw ((Line.rotation w atoms (segmentDirection c.segment)).cells q) =
      coordinates ((Line.placement w atoms (PortAnnulus.innerDirection role) (corePort w kind role) c.segment.finish ht' hs hc.2.2.2).cells q) := by
    let f (ds : Direction × (ℕ × ℕ)) : ℕ × ℕ :=
      (Line.offsetX w atoms ds.1 ds.2+((Line.rotation w atoms ds.1).cells q).1.val,
       Line.offsetY w atoms ds.1 ds.2+((Line.rotation w atoms ds.1).cells q).2.val)
    have hds : (segmentDirection c.segment,c.segment.start) =
        (PortAnnulus.innerDirection role,corePort w kind role) := Prod.ext hdirection hstart
    exact congrArg f hds
  intro he
  exact initial_wall_ne_floor w (segmentLength c.segment) hw kind (c.above != c.desiredSide) role
    ⟨c.segment.finish,ht',hs,hc.2.2.2⟩ q hq' p hp hfloor (hw''.symm.trans he)

end PushPuzzle.PushS.FiniteGateActiveRegion
