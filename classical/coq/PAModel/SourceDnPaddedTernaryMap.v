(** Actual three-premise Dn transport with an exterior condition. This
    uses the proved binary map and one further implication distribution. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceDn SourceDnBounds SourceDnPaddedBinaryMap SourceRepresentationPadding SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition DPT_first:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))).
Definition DPT_second:=SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5)).
Definition DPT_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5)))).
Ltac dpt_ctx:=apply SPTCtx;cbn;auto 14.
Lemma DPT_program:source_prop_program[DPT_first;DPT_second]DPT_result.
Proof.
 unfold DPT_first,DPT_second,DPT_result. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 4);[|dpt_ctx].
 eapply SPTIE with(a:=SPTSlot 3);[dpt_ctx|].
 eapply SPTIE with(a:=SPTSlot 2);[|dpt_ctx].
 eapply SPTIE with(a:=SPTSlot 1);[|dpt_ctx].
 eapply SPTIE with(a:=SPTSlot 0);dpt_ctx.
Qed.
Theorem source_descriptor_dn_padded_ternary_map M T count condition padded a b c d da db dc dd
 cd bcd abcd proof dcd dbcd dabcd result k:
 source_bounded M condition(succM M(succM M k)) ->
 source_bounded M a(addM M count(succM M(succM M k))) ->
 source_bounded M b(addM M count(succM M(succM M k))) ->
 source_bounded M c(addM M count(succM M(succM M k))) ->
 source_bounded M d(addM M count(succM M(succM M k))) ->
 source_representation_padding M count condition padded ->
 source_dn M count a da ->source_dn M count b db ->source_dn M count c dc ->source_dn M count d dd ->
 sf_relation M SFImpl c d cd ->sf_relation M SFImpl b cd bcd ->sf_relation M SFImpl a bcd abcd ->
 sf_relation M SFImpl padded abcd proof ->sf_relation M SFImpl dc dd dcd ->sf_relation M SFImpl db dcd dbcd ->
 sf_relation M SFImpl da dbcd dabcd ->sf_relation M SFImpl condition dabcd result ->
 source_descriptor_provable M T proof ->source_descriptor_provable M T result.
Proof.
 intros BCond BA BB BC BD HPad HDA HDB HDC HDD HCD HBCD HABCD HProof HDCD HDBCD HDABCD HResult PProof.
 assert(BCD:source_bounded M cd(addM M count(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl c d cd _ (or_intror(or_intror eq_refl))HCD)(conj BC BD)). }
 destruct(source_dn_total M count cd)as(aux&HAux).
 destruct(sf_relation_total M SFImpl db aux)as(tail1&HTail1).
 destruct(sf_relation_total M SFImpl da tail1)as(body1&HBody1).
 destruct(sf_relation_total M SFImpl condition body1)as(first&HFirst).
 pose proof(source_descriptor_dn_padded_binary_map M T count condition padded a b cd da db aux
  bcd abcd proof tail1 body1 first k BCond BA BB BCD HPad HDA HDB HAux HBCD HABCD HProof HTail1 HBody1 HFirst PProof)as PFirst.
 destruct(sf_relation_total M SFImpl aux dcd)as(second&HSecond).
 pose proof(source_descriptor_dn_distribution M T count c d cd dc dd aux dcd second k BC BD HCD HDC HDD HAux HDCD HSecond)as PSecond.
 set(rho:=fun i=>match i with 0=>condition|1=>da|2=>db|3=>aux|4=>dc|_=>dd end).
 assert(BAll:forall i,source_bounded M(rho i)(succM M(succM M k))).
 { intros[|[|[|[|[|i]]]]];cbn[rho];try assumption;eapply source_dn_bounded;eassumption. }
 assert(GTail1:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 2)(SPTSlot 3)))tail1).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 2)(SPTSlot 3)db aux tail1 eq_refl eq_refl HTail1). }
 assert(GBody1:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))))body1).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))da tail1 body1 eq_refl GTail1 HBody1). }
 assert(GFirst:code_relation M rho(source_prop_expression DPT_first)first).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3)))
   condition body1 first eq_refl GBody1 HFirst). }
 assert(GCD:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 4)(SPTSlot 5)))dcd).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 4)(SPTSlot 5)dc dd dcd eq_refl eq_refl HDCD). }
 assert(GSecond:code_relation M rho(source_prop_expression DPT_second)second).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))aux dcd second eq_refl GCD HSecond). }
 assert(GBCD:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5))))dbcd).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5))db dcd dbcd eq_refl GCD HDBCD). }
 assert(GABCD:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5)))))dabcd).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5)))da dbcd dabcd eq_refl GBCD HDABCD). }
 assert(GResult:code_relation M rho(source_prop_expression DPT_result)result).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5))))
   condition dabcd result eq_refl GABCD HResult). }
 apply(source_descriptor_prop_program M T _ _ DPT_program rho(succM M(succM M k))result BAll);[|exact GResult].
 intros p[<-|[<-|[]]]f HF.
 - rewrite(code_relation_functional M _ rho f first HF GFirst). exact PFirst.
 - rewrite(code_relation_functional M _ rho f second HF GSecond). exact PSecond.
Qed.
Print Assumptions DPT_program.
Print Assumptions source_descriptor_dn_padded_ternary_map.
