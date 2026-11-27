/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathOwners
public import PushS.FiniteRoutingGateGeometry

/-! Actual core stencils and first-arm rail stencils own one another's exposed seam cells. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry FiniteGateStencils FiniteGateTracks

attribute [local irreducible] side andWalls orWalls Line.width Line.height Line.walls FiniteTools.side

private theorem and_port_not_exit (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) :
    ¬AndExit w (andCell w false false true (andPortLabel w role)) := by
  fin_cases role <;> dsimp [AndExit,andPortLabel,andCell,andPoint] <;> unfold origin <;> omega

private theorem or_port_not_exit (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) :
    ¬OrExit w (orCell w false false true (orPortLabel w role)) := by
  fin_cases role <;> dsimp [OrExit,orPortLabel,orCell,orPoint] <;> unfold origin <;> omega

private theorem and_port_owner (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) :
    AndOwner w hw (andCell w false false true (andPortLabel w role))
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level := by
  obtain ⟨chart,q,he,htag⟩ := andNormal_represented w hw false false true (andPortLabel w role)
  have hp : (andChart w hw chart).classifier.name q ≠ .outside := by
    intro hn
    rw [hn] at htag
    exact andTrack_active w _ htag.symm
  have hf : (andChart w hw chart).embedding.cells q ∉ andWalls w := by
    rw [he]
    exact andCell_not_wall w hw false false true _
  rcases andChart_owner_or_exit w hw chart q hp hf with hexit | howner
  · exact (and_port_not_exit w hw role (he ▸ hexit)).elim
  · obtain ⟨next,p,hx,hx',hy,hy',hp',hl⟩ := howner
    refine ⟨next,p,hx,hx',hy,hy',hp'.trans he,?_⟩
    have hlev := congrArg AxisTrack.level htag
    simp only [AxisTrack.level_shift] at hlev
    calc
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level =
          (andTrack w (andPortLabel w role)).level := by
        fin_cases role <;> simp [Line.orientedRailName,PortAnnulus.innerDirection,andTrack,andPortLabel,AxisTrack.level]
      _ = ((andChart w hw chart).classifier.name q).level := hlev.symm
      _ ≤ ((andChart w hw next).classifier.name p).level := hl

private theorem or_port_owner (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) :
    OrOwner w (orCell w false false true (orPortLabel w role))
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level := by
  obtain ⟨q,he,htag⟩ := orNormal_represented w hw false false true (orPortLabel w role)
  have hp : (orJunction w).classifier.name q ≠ .outside := by
    intro hn
    rw [hn] at htag
    exact orTrack_active w _ htag.symm
  rcases orJunction_owner_or_exit w q hp with hexit | howner
  · exact (or_port_not_exit w hw role (he ▸ hexit)).elim
  · obtain ⟨p,hx,hx',hy,hy',hp',hl⟩ := howner
    refine ⟨p,hx,hx',hy,hy',hp'.trans he,?_⟩
    have hlev := congrArg AxisTrack.level htag
    simp only [AxisTrack.level_shift] at hlev
    calc
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level =
          (orTrack w (orPortLabel w role)).level := by
        fin_cases role <;> simp [Line.orientedRailName,PortAnnulus.innerDirection,orTrack,orPortLabel,AxisTrack.level]
      _ = ((orJunction w).classifier.name q).level := hlev.symm
      _ ≤ ((orJunction w).classifier.name p).level := hl

theorem arm_code_mem_gateCodes (w : ℕ) (g : GateTileState) (role : Fin 3) (c : PrimitiveCode)
    (hc : c ∈ (armSpec w g role).codes) : c ∈ gateCodes w g := by
  rw [gateCodes_eq_specs]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨role,List.mem_finRange role,hc⟩)

theorem first_line_core_owner (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    WorldOwner w hw (gateCodes w g) (((armSpec w g role).line 0).firstWorld w hw false)
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level := by
  have hphase : portInflow false false true role = false := by simp [portInflow]
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · obtain ⟨q,hx,hx',hy,hy',he,hl⟩ := or_port_owner w hw role
    refine ⟨.core _,List.mem_cons_self,orCell w false false true (orPortLabel w role),?_,?_⟩
    · have h := or_arm_first_shared w hw ⟨⟨false,initial,target⟩,incoming,pattern,rotation⟩ rfl role false false true
      change coreWorld w (orCell w false false true (orPortLabel w role)) = _
      simpa only [hphase] using h.symm
    · exact ⟨(),q,⟨hx,hx',hy,hy'⟩,he,hl⟩
  · obtain ⟨chart,q,hx,hx',hy,hy',he,hl⟩ := and_port_owner w hw role
    refine ⟨.core _,List.mem_cons_self,andCell w false false true (andPortLabel w role),?_,?_⟩
    · have h := and_arm_first_shared w hw ⟨⟨true,initial,target⟩,incoming,pattern,rotation⟩ rfl role false false true
      change coreWorld w (andCell w false false true (andPortLabel w role)) = _
      simpa only [hphase] using h.symm
    · exact ⟨chart,q,⟨hx,hx',hy,hy'⟩,he,hl⟩

def coreExitDistance (w : ℕ) (kind : Bool) (role : Fin 3) : ℕ :=
  if role = 2 then 2*w+11 else if kind = true ∧ role = 0 then 2 else 2*w+10

def coreExitPoint (w : ℕ) (kind : Bool) (role : Fin 3) : ℕ × ℕ :=
  if kind then
    if role = 0 then (origin w-8*w-18,origin w-6*w-21)
    else if role = 1 then (origin w+3,origin w-10*w-41) else (origin w+5*w+23,origin w)
  else if role = 0 then (origin w-4*w-17,origin w)
    else if role = 1 then (origin w+4,origin w-4*w-23) else (origin w+5*w+24,origin w)

private theorem coreExitDistance_bounds (w length : ℕ) (kind : Bool) (role : Fin 3)
    (hl : 17*w+61 ≤ length) : 0 < coreExitDistance w kind role ∧ coreExitDistance w kind role ≤ length := by
  cases kind <;> fin_cases role <;> dsimp [coreExitDistance] <;> omega

set_option maxRecDepth 65536 in
private theorem coreExitPoint_along (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (role : Fin 3) :
    (padding w+coreOffset w+(coreExitPoint w kind role).1,
      padding w+coreOffset w+(coreExitPoint w kind role).2) =
      Line.along w (PortAnnulus.innerDirection role) (corePort w kind role) (coreExitDistance w kind role) := by
  cases kind <;> fin_cases role <;> apply Prod.ext <;>
    simp [coreExitPoint,coreExitDistance,Line.along,PortAnnulus.innerDirection,corePort,
      origin,coreOffset,padding,spacing] <;> omega

private theorem core_exit_position (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (p : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hp : (PrimitiveCode.core g).Exit w hw p) :
    ∃ role : Fin 3, (PrimitiveCode.core g).world w hw p =
      Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role)
        (coreExitDistance w g.core.isAND role) := by
  have hpoint : ∃ role : Fin 3, (p.1.val,p.2.val) = coreExitPoint w g.core.isAND role := by
    rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
    cases kind
    · change OrExit w p at hp
      rcases hp with h | h | h
      · exact ⟨0,Prod.ext h.1 h.2⟩
      · exact ⟨1,Prod.ext h.1 h.2⟩
      · exact ⟨2,Prod.ext h.1 h.2⟩
    · change AndExit w p at hp
      rcases hp with h | h | h
      · exact ⟨0,Prod.ext h.1 h.2⟩
      · exact ⟨1,Prod.ext h.1 h.2⟩
      · exact ⟨2,Prod.ext h.1 h.2⟩
  obtain ⟨role,he⟩ := hpoint
  refine ⟨role,?_⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp only at hx hy
  change (padding w+coreOffset w+p.1.val,padding w+coreOffset w+p.2.val) = _
  rw [hx,hy]
  exact coreExitPoint_along w hw g.core.isAND role

private theorem arm_first_rail_owner (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (n : ℕ)
    (hn0 : 0 < n) (hn : n ≤ segmentLength ((armSpec w g role).line 0).segment) :
    WorldOwner w hw (gateCodes w g)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) n)
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level := by
  have hi : 0 < (armSpec w g role).segments.length := by
    change 0 < (armRoute w g role).length
    rw [armRoute_length,route_length]
    omega
  have hc := (armSpec w g role).line_good w (armSpec_geometry w g role) 0 hi
  refine ⟨.line ((armSpec w g role).line 0),
    arm_code_mem_gateCodes w g role _ ((armSpec w g role).line_mem_codes 0 hi),
    ((armSpec w g role).line 0).railPoint w hw hc n hn,?_,?_⟩
  · rw [LineCode.railPoint_world,armSpec_first_direction,armSpec_first_start]
  · rw [←armSpec_first_direction w g role]
    exact LineCode.railPoint_owner w hw _ hc n hn0 hn

set_option maxRecDepth 65536 in
/-- The source chart's exact exit level is preserved when its literal point enters the first arm. -/
theorem core_chart_exit_owner (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (chart : (PrimitiveCode.core g).Charts)
    (q : Cell ((PrimitiveCode.core g).chart w hw chart).width ((PrimitiveCode.core g).chart w hw chart).height)
    (he : (PrimitiveCode.core g).Exit w hw (((PrimitiveCode.core g).chart w hw chart).embedding.cells q)) :
    WorldOwner w hw (gateCodes w g)
      ((PrimitiveCode.core g).world w hw (((PrimitiveCode.core g).chart w hw chart).embedding.cells q))
      (((PrimitiveCode.core g).chart w hw chart).classifier.name q).level := by
  let point := ((PrimitiveCode.core g).chart w hw chart).embedding.cells q
  obtain ⟨role,hrole⟩ := core_exit_position w hw g point he
  have hlevel : (((PrimitiveCode.core g).chart w hw chart).classifier.name q).level =
      (Line.orientedRailName w (PortAnnulus.innerDirection role)).level := by
    have hx := congrArg Prod.fst hrole
    change padding w+coreOffset w+point.1.val =
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role)
        (coreExitDistance w g.core.isAND role)).1 at hx
    rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
    cases kind
    · change ((orJunction w).classifier.name q).level = _
      rw [orJunction_exit_level w q he]
      change padding w+coreOffset w+((orJunction w).embedding.cells q).1.val = _ at hx
      fin_cases role <;> dsimp [Line.along,PortAnnulus.innerDirection,corePort,coreExitDistance,
        Line.orientedRailName,AxisTrack.level] at hx ⊢ <;>
        split_ifs <;> simp only [origin,coreOffset,padding,spacing] at * <;> omega
    · change ((andChart w hw chart).classifier.name q).level = _
      rw [andChart_exit_level w hw chart q he]
      change padding w+coreOffset w+((andChart w hw chart).embedding.cells q).1.val = _ at hx
      fin_cases role <;> dsimp [Line.along,PortAnnulus.innerDirection,corePort,coreExitDistance,
        Line.orientedRailName,AxisTrack.level] at hx ⊢ <;>
        split_ifs <;> simp only [origin,coreOffset,padding,spacing] at * <;> omega
  have hi : 0 < (armSpec w g role).segments.length := by
    change 0 < (armRoute w g role).length
    rw [armRoute_length,route_length]
    omega
  have hb := coreExitDistance_bounds w (segmentLength ((armSpec w g role).line 0).segment) g.core.isAND role
    ((armSpec w g role).line_good w (armSpec_geometry w g role) 0 hi).2.1
  change WorldOwner w hw (gateCodes w g) ((PrimitiveCode.core g).world w hw point) _
  rw [hlevel,hrole]
  exact arm_first_rail_owner w hw g role _ hb.1 hb.2

end PushPuzzle.PushS.FiniteRouting
