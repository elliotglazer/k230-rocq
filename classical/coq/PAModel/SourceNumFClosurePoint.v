(** Two actual source ExI steps carry membership through NumF succession.
 All formula codes, witnesses and constructor graphs may be nonstandard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalInstantiation SourceDescriptorProvability SourceDescriptorExIntroduction
 SourcePropositionalTemplates SourceDescriptorPrograms SourceNumFClosurePrograms.
Unset Implicit Arguments.
Theorem source_descriptor_numf_closure_point M T f s member nextbody next targetbody target
 pairinst sbody targetinst first second inner result u v k :
 source_bounded M f k ->source_bounded M s k ->source_bounded M member k ->
 source_bounded M next k ->source_bounded M target k ->
 sf_relation M SFEx nextbody(zeroM M)next ->numerical_instantiation M nextbody u pairinst ->
 sf_relation M SFEx targetbody(zeroM M)target ->numerical_instantiation M targetbody v targetinst ->
 sf_relation M SFAnd f s pairinst ->sf_relation M SFAnd s member sbody ->
 sf_relation M SFAnd next member targetinst ->
 sf_relation M SFImpl pairinst next first ->sf_relation M SFImpl targetinst target second ->
 sf_relation M SFImpl f target inner ->sf_relation M SFImpl sbody inner result ->
 source_descriptor_provable M T result.
Proof.
 intros BF BS BM BN BT HN HNI HT HTI HP HS HB HI HJ HInner HResult.
 assert(BP:source_bounded M pairinst k).
 { exact(proj2(source_bounded_accept_binary M SFAnd f s pairinst k(or_introl eq_refl) HP)(conj BF BS)). }
 assert(BBody:source_bounded M targetinst k).
 { exact(proj2(source_bounded_accept_binary M SFAnd next member targetinst k(or_introl eq_refl) HB)(conj BN BM)). }
 pose proof(source_descriptor_ex_introduction M T nextbody next u pairinst first k BN BP HN HNI HI)as PFirst.
 pose proof(source_descriptor_ex_introduction M T targetbody target v targetinst second k BT BBody HT HTI HJ)as PSecond.
 set(env:=fun idx:nat=>match idx with 0=>f|1=>s|2=>member|3=>next|_=>target end).
 assert(GP:code_relation M env(source_prop_expression nc_point_pair)pairinst).
 { unfold nc_point_pair. eapply source_prop_template_join;[reflexivity|reflexivity|exact HP]. }
 assert(GB:code_relation M env(source_prop_expression nc_point_body)sbody).
 { unfold nc_point_body. eapply source_prop_template_join;[reflexivity|reflexivity|exact HS]. }
 assert(GT:code_relation M env(source_prop_expression nc_point_target)targetinst).
 { unfold nc_point_target. eapply source_prop_template_join;[reflexivity|reflexivity|exact HB]. }
 assert(GF:code_relation M env(source_prop_expression(SPTImpl nc_point_pair(SPTSlot 3)))first).
 { eapply source_prop_template_join;[exact GP|reflexivity|exact HI]. }
 assert(GS:code_relation M env(source_prop_expression(SPTImpl nc_point_target(SPTSlot 4)))second).
 { eapply source_prop_template_join;[exact GT|reflexivity|exact HJ]. }
 assert(GI:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 0)(SPTSlot 4)))inner).
 { eapply source_prop_template_join;[reflexivity|reflexivity|exact HInner]. }
 assert(GR:code_relation M env(source_prop_expression(SPTImpl nc_point_body(SPTImpl(SPTSlot 0)(SPTSlot 4))))result).
 { eapply source_prop_template_join;[exact GB|exact GI|exact HResult]. }
 apply(source_descriptor_prop_program M T _ _ source_numf_closure_point_program env k result).
 - intros[|[|[|[|idx]]]];cbn[env];assumption.
 - intros p[<-|[<-|[]]] a HA.
   + rewrite(code_relation_functional M _ env a first HA GF). exact PFirst.
   + rewrite(code_relation_functional M _ env a second HA GS). exact PSecond.
 - exact GR.
Qed.
Print Assumptions source_descriptor_numf_closure_point.
