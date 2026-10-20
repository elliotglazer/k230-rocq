(** Actual source proof transport between representation points from
    two actual source implications between their relativized matrices. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceNumeralLift
 SourceEnvironmentCarrierClosure SourceRepresentationRecipe SourceIffGraphs SourceRepresentationDifferenceProgram SourcePropositionalTemplates SourceFunctionalityShells
 SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms SourceDescriptorUniversalMap.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition RPE_iff a b:=SPTAnd(SPTImpl a b)(SPTImpl b a).
Definition RPE_body index:=SPTImpl(SPTSlot 0)(RPE_iff(SPTSlot 1)(SPTSlot index)).
Lemma RPE_program:source_prop_program[SPTImpl(SPTSlot 2)(SPTSlot 3);SPTImpl(SPTSlot 3)(SPTSlot 2)](SPTImpl(RPE_body 2)(RPE_body 3)).
Proof.
 unfold RPE_body,RPE_iff. do 2 apply SPTII. apply SPTCI.
 - apply SPTII. eapply SPTIE with(a:=SPTSlot 2);[apply SPTCtx;cbn;auto 12|].
   eapply SPTIE with(a:=SPTSlot 1);[|apply SPTCtx;cbn;auto 12].
   apply SPTCE1 with(b:=SPTImpl(SPTSlot 2)(SPTSlot 1)).
   eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 12.
 - apply SPTII. eapply SPTIE with(a:=SPTSlot 2).
   + apply SPTCE2 with(a:=SPTImpl(SPTSlot 1)(SPTSlot 2)).
     eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 12.
   + eapply SPTIE with(a:=SPTSlot 3);apply SPTCtx;cbn;auto 12.
Qed.
Lemma RPE_body_graph M rho index environment matrix body:
 rho 0=environment->rho 1=code_numeral M(sf_make SFMember 0 1)->rho index=matrix->
 code_relation M rho(source_prop_expression(RPE_body index))body->
 code_relation M(representation_point_environment environment matrix)
  (E_sf SFImpl(CEvar 0)(E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1)))body.
Proof.
 intros HE HM HX HBody.
 set(member:=code_numeral M(sf_make SFMember 0 1)).
 destruct(source_iff_total M member matrix)as(iff&HIff).
 destruct(source_iff_parts M member matrix iff HIff)as(lr&rl&HLR&HRL&HI).
 destruct(sf_relation_total M SFImpl environment iff)as(result&HResult).
 assert(GMember:code_relation M rho(CEvar 1)member)by(exact(eq_sym HM)).
 assert(GMatrix:code_relation M rho(CEvar index)matrix)by(exact(eq_sym HX)).
 assert(GEnv:code_relation M rho(CEvar 0)environment)by(exact(eq_sym HE)).
 assert(GLR:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot index)))lr).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot index)member matrix lr GMember GMatrix HLR). }
 assert(GRL:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot index)(SPTSlot 1)))rl).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot index)(SPTSlot 1)matrix member rl GMatrix GMember HRL). }
 assert(GI:code_relation M rho(source_prop_expression(RPE_iff(SPTSlot 1)(SPTSlot index)))iff).
 { exact(source_prop_template_join M rho SFAnd(SPTImpl(SPTSlot 1)(SPTSlot index))(SPTImpl(SPTSlot index)(SPTSlot 1))lr rl iff GLR GRL HI). }
 assert(GResult:code_relation M rho(source_prop_expression(RPE_body index))result).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(RPE_iff(SPTSlot 1)(SPTSlot index))environment iff result GEnv GI HResult). }
 rewrite(code_relation_functional M _ rho body result HBody GResult).
 set(env:=representation_point_environment environment matrix).
 assert(GM:code_relation M env(E_sf SFMember(CEconst 0)(CEconst 1))member).
 { exact(proj2(schema_expression_graph M env SFMember(CEconst 0)(CEconst 1)(zeroM M)(code_numeral M 1)member eq_refl eq_refl)(sf_make_numeral M SFMember 0 1)). }
 assert(GIFF:code_relation M env(E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1))iff).
 { unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HI].
   - eapply environment_carrier_code_join;[exact GM|reflexivity|exact HLR].
   - eapply environment_carrier_code_join;[reflexivity|exact GM|exact HRL]. }
 exact(environment_carrier_code_join M env SFImpl(CEvar 0)_ environment iff result eq_refl GIFF HResult).
Qed.
Theorem source_descriptor_representation_point_equivalence M T environment left right pointLeft pointRight forward reverse out k:
 source_bounded M environment k->source_bounded M left k->source_bounded M right k->
 coding_lt M(zeroM M)k->coding_lt M(code_numeral M 1)k->
 code_relation M(representation_point_environment environment left)(E_representation_point(CEvar 0)(CEvar 1))pointLeft->
 code_relation M(representation_point_environment environment right)(E_representation_point(CEvar 0)(CEvar 1))pointRight->
 sf_relation M SFImpl left right forward->sf_relation M SFImpl right left reverse->
 source_descriptor_provable M T forward->source_descriptor_provable M T reverse->
 sf_relation M SFImpl pointLeft pointRight out->source_descriptor_provable M T out.
Proof.
 intros BE BL BR H0 H1 HPL HPR HF HR PF PR HO.
 set(member:=code_numeral M(sf_make SFMember 0 1)).
 set(rho:=fun i=>match i with 0=>environment|1=>member|2=>left|_=>right end).
 assert(BMember:source_bounded M member k).
 { exact(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 1)member k(or_introl eq_refl)(sf_make_numeral M SFMember 0 1))(conj H0 H1)). }
 destruct(code_relation_total M(source_prop_expression(RPE_body 2))rho)as(bodyLeft&HBodyLeft).
 destruct(code_relation_total M(source_prop_expression(RPE_body 3))rho)as(bodyRight&HBodyRight).
 assert(GLeft:code_relation M(representation_point_environment environment left)
  (E_sf SFImpl(CEvar 0)(E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1)))bodyLeft).
 { exact(RPE_body_graph M rho 2 environment left bodyLeft eq_refl eq_refl eq_refl HBodyLeft). }
 assert(GRight:code_relation M(representation_point_environment environment right)
  (E_sf SFImpl(CEvar 0)(E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1)))bodyRight).
 { exact(RPE_body_graph M rho 3 environment right bodyRight eq_refl eq_refl eq_refl HBodyRight). }
 assert(HAllL:sf_relation M SFAll bodyLeft(zeroM M)pointLeft).
 { exact(proj1(schema_expression_graph M _ SFAll _ (CEconst 0)bodyLeft(zeroM M)pointLeft GLeft eq_refl)HPL). }
 assert(HAllR:sf_relation M SFAll bodyRight(zeroM M)pointRight).
 { exact(proj1(schema_expression_graph M _ SFAll _ (CEconst 0)bodyRight(zeroM M)pointRight GRight eq_refl)HPR). }
 assert(BAll:forall i,source_bounded M(rho i)k).
 { intros[|[|[|i]]];cbn[rho];assumption. }
 pose proof(source_prop_template_bound M rho(RPE_body 2)k BAll bodyLeft HBodyLeft)as BBodyLeft.
 pose proof(source_prop_template_bound M rho(RPE_body 3)k BAll bodyRight HBodyRight)as BBodyRight.
 destruct(code_relation_total M(source_prop_expression(SPTImpl(RPE_body 2)(RPE_body 3)))rho)as(point&HPoint).
 pose proof(proj1(schema_expression_graph M rho SFImpl _ _ bodyLeft bodyRight point HBodyLeft HBodyRight)HPoint)as HPointRel.
 assert(PPoint:source_descriptor_provable M T point).
 { apply(source_descriptor_prop_program M T _ _ RPE_program rho k point BAll);[|exact HPoint].
   intros p[<-|[<-|[]]]value HG.
   - rewrite(code_relation_functional M _ rho value forward HG(proj2(schema_expression_graph M rho SFImpl(CEvar 2)(CEvar 3)left right forward eq_refl eq_refl)HF)). exact PF.
   - rewrite(code_relation_functional M _ rho value reverse HG(proj2(schema_expression_graph M rho SFImpl(CEvar 3)(CEvar 2)right left reverse eq_refl eq_refl)HR)). exact PR. }
 exact(source_descriptor_universal_map M T bodyLeft bodyRight point pointLeft pointRight out k BBodyLeft BBodyRight HPointRel HAllL HAllR HO PPoint).
Qed.
Print Assumptions source_descriptor_representation_point_equivalence.
