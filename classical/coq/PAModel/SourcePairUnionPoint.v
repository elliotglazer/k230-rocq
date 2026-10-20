(** The actual ZFR disjunction point law, with both operation laws discharged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 SourceBounded SourcePropositionalTemplates SourcePairUnionFrame SourcePairUnionUniversal SourcePairUnionProgram
 SourceRepresentationDifferencePoints SourceRepresentationPointBounds SourceFiniteTelescope
 SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition PU_pair_law:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition PU_macro_law:=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))).
Definition PU_point_goal:=SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))).
Ltac pup_ctx:=apply SPTCtx;cbn;auto 12.
Lemma pair_union_point_program:source_prop_program[PU_pair_law;PU_macro_law]PU_point_goal.
Proof.
 unfold PU_pair_law,PU_macro_law,PU_point_goal. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 4);[|pup_ctx].
 eapply SPTIE with(a:=SPTSlot 3);[|pup_ctx].
 eapply SPTIE with(a:=SPTSlot 2);[pup_ctx|].
 eapply SPTIE with(a:=SPTSlot 1).
 - eapply SPTIE with(a:=SPTSlot 0);[pup_ctx|]. apply SPTCE1 with(b:=SPTSlot 1). pup_ctx.
 - apply SPTCE2 with(a:=SPTSlot 0). pup_ctx.
Qed.
Theorem source_zfr_pair_union_point_law M rho k pair union condition point1 point2 target inner point law:
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->
 code_relation M rho E_pair_union_pair pair ->code_relation M rho E_pair_union_union union ->
 code_relation M rho(E_double_difference_all pair_union_left_template)point1 ->
 code_relation M rho(E_double_difference_all pair_union_right_template)point2 ->
 code_relation M rho(E_double_difference_all pair_union_conclusion)target ->
 sf_relation M SFAnd pair union condition ->sf_relation M SFImpl point2 target inner ->
 sf_relation M SFImpl point1 inner point ->sf_relation M SFImpl condition point law ->source_zfr_provable M law.
Proof.
 intros HNames B4 B5 B6 HPair HUnion HP1 HP2 HT HCond HInner HPoint HLaw.
 destruct(code_relation_total M(E_double_difference_all pair_union_profile_template)rho)as(profile&HProfile).
 destruct(sf_relation_total M SFImpl union profile)as(upi&HUPI).
 destruct(sf_relation_total M SFImpl pair upi)as(pairlaw&HPairLaw).
 pose proof(source_zfr_pair_union_profile_shell M rho pair union profile upi pairlaw HPair HUnion HProfile HUPI HPairLaw)as PPair.
 destruct(sf_relation_total M SFImpl profile point)as(macro&HMacro).
 assert(HTelescope:source_finite_telescope M[profile;point1;point2]target macro).
 { exists point. split;[|exact HMacro]. exists inner. split;[|exact HPoint].
   exists target. split;[reflexivity|exact HInner]. }
 pose proof(source_empty_pair_union_universal M rho k profile point1 point2 target macro
  HNames B4 B5 B6 HProfile HP1 HP2 HT HTelescope)as PMacro.
 set(env:=fun i=>match i with 0=>pair|1=>union|2=>profile|3=>point1|4=>point2|5=>target|_=>zeroM M end).
 assert(BAll:forall i,source_bounded M(env i)k).
 { intros[|[|[|[|[|[|i]]]]]];cbn[env].
   - exact(pair_union_parameter_bound M pair_union_pair_source rho k pair pair_union_pair_bound HNames HPair).
   - exact(pair_union_parameter_bound M pair_union_union_source rho k union pair_union_union_bound HNames HUnion).
   - exact(double_difference_all_expression_bound M rho k pair_union_profile_template HNames B4 B5 B6 profile HProfile).
   - exact(double_difference_all_expression_bound M rho k pair_union_left_template HNames B4 B5 B6 point1 HP1).
   - exact(double_difference_all_expression_bound M rho k pair_union_right_template HNames B4 B5 B6 point2 HP2).
   - exact(double_difference_all_expression_bound M rho k pair_union_conclusion HNames B4 B5 B6 target HT).
   - apply source_bounded_accept_falsity. }
 assert(GPair:code_relation M env(source_prop_expression PU_pair_law)pairlaw).
 { unfold PU_pair_law. apply(source_prop_template_join M env SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))pair upi pairlaw eq_refl);[|exact HPairLaw].
   exact(source_prop_template_join M env SFImpl(SPTSlot 1)(SPTSlot 2)union profile upi eq_refl eq_refl HUPI). }
 assert(GMacro:code_relation M env(source_prop_expression PU_macro_law)macro).
 { unfold PU_macro_law. apply(source_prop_template_join M env SFImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5)))profile point macro eq_refl);[|exact HMacro].
   apply(source_prop_template_join M env SFImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))point1 inner point eq_refl);[|exact HPoint].
   exact(source_prop_template_join M env SFImpl(SPTSlot 4)(SPTSlot 5)point2 target inner eq_refl eq_refl HInner). }
 assert(GGoal:code_relation M env(source_prop_expression PU_point_goal)law).
 { unfold PU_point_goal. apply(source_prop_template_join M env SFImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))
    (SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5)))condition point law);[| |exact HLaw].
   - exact(source_prop_template_join M env SFAnd(SPTSlot 0)(SPTSlot 1)pair union condition eq_refl eq_refl HCond).
   - apply(source_prop_template_join M env SFImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))point1 inner point eq_refl);[|exact HPoint].
     exact(source_prop_template_join M env SFImpl(SPTSlot 4)(SPTSlot 5)point2 target inner eq_refl eq_refl HInner). }
 apply(proj1(source_zfr_descriptor_provable M law)).
 apply(source_descriptor_prop_program M ZFRSourceDescriptor[PU_pair_law;PU_macro_law]PU_point_goal
  pair_union_point_program env k law BAll);[|exact GGoal].
 intros p[<-|[<-|[]]]f HF.
 - rewrite(code_relation_functional M _ env f pairlaw HF GPair). exact(proj2(source_zfr_descriptor_provable M pairlaw)PPair).
 - rewrite(code_relation_functional M _ env f macro HF GMacro). exact(source_descriptor_provable_from_empty M ZFRSourceDescriptor macro PMacro).
Qed.
Print Assumptions pair_union_point_program.
Print Assumptions source_zfr_pair_union_point_law.
