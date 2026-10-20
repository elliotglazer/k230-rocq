(** The falsity representative can be chosen in the actual closure
    container. The fixed closure-empty certificate is discharged here;
    all displayed premises are exact syntax graphs or variable bounds. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
 SourceBounded SourceBoundMonotone SourceNumeralLift SourceRepresentationRecipe SourceRepresentationFalsity
 SourceDefinabilityPrimitives SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms
 SourceDescriptorExistentialMap SourcePropositionalTemplates SchemaConstructorBounds
 SourceClosureNumeralsFixed SourceZFRProvability SourceSetTheoryDescriptors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition representation_member_code M :=code_numeral M(sf_make SFMember 0 3).

Theorem source_descriptor_falsity_pair_point M T n rep rawbody targetbody point :
 source_representation_recipe M n(zeroM M) rep ->
 sf_relation M SFAnd(code_numeral M(sf_encode source_def_empty))(representation_member_code M) rawbody ->
 sf_relation M SFAnd(representation_member_code M) rep targetbody ->
 sf_relation M SFImpl rawbody targetbody point ->source_descriptor_provable M T point.
Proof.
 intros HR HRaw HTarget HPoint.
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode source_def_empty)) rep)as(imp&HI).
 set(rho:=schema_env3(code_numeral M(sf_encode source_def_empty)) rep(representation_member_code M)).
 assert(BRep:source_bounded M rep(code_numeral M 4)).
 { apply(source_bounded_monotone M rep(code_numeral M 2)(code_numeral M 4)
   (source_representation_recipe_bounded M n(zeroM M) rep(source_bounded_accept_falsity M n) HR)).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BEmpty:source_bounded M(code_numeral M(sf_encode source_def_empty))(code_numeral M 4)).
 { apply(source_bounded_monotone M _(code_numeral M 1)(code_numeral M 4)(numerical_def_empty_bound M)).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(BMember:source_bounded M(representation_member_code M)(code_numeral M 4)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)
    (representation_member_code M)(code_numeral M 4)(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 assert(P:source_prop_program [SPTImpl(SPTSlot 0)(SPTSlot 1)]
   (SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 2))(SPTAnd(SPTSlot 2)(SPTSlot 1)))).
 { apply SPTII,SPTCI.
   - apply SPTCE2 with(a:=SPTSlot 0). apply SPTCtx. cbn;auto.
   - eapply SPTIE;[apply SPTCtx;cbn;auto|].
     apply SPTCE1 with(b:=SPTSlot 2). apply SPTCtx. cbn;auto. }
 apply(source_descriptor_prop_program M T _ _ P rho(code_numeral M 4) point).
 - intros[|[|i]];cbn[rho schema_env3];assumption.
 - intros p[<-|[]] f HF.
   assert(HImp:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTSlot 1))) imp).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(CEvar 1) _ _ imp eq_refl eq_refl) HI). }
   rewrite(code_relation_functional M _ rho f imp HF HImp).
   exact(source_descriptor_representation_falsity M T n rep imp HR HI).
 - assert(HRawGraph:code_relation M rho(source_prop_expression(SPTAnd(SPTSlot 0)(SPTSlot 2))) rawbody).
   { exact(proj2(schema_expression_graph M rho SFAnd(CEvar 0)(CEvar 2) _ _ rawbody eq_refl eq_refl) HRaw). }
   assert(HTargetGraph:code_relation M rho(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 1))) targetbody).
   { exact(proj2(schema_expression_graph M rho SFAnd(CEvar 2)(CEvar 1) _ _ targetbody eq_refl eq_refl) HTarget). }
   exact(proj2(schema_expression_graph M rho SFImpl _ _ rawbody targetbody point HRawGraph HTargetGraph) HPoint).
Qed.

Theorem source_zfr_representation_falsity_closure M n rep rho succ closure rawbody rawex middle law
 targetbody targetex targetmiddle result :
 source_representation_recipe M n(zeroM M) rep ->
 code_relation M rho source_closure_empty_expression law ->
 source_bounded M succ(code_numeral M 3) ->source_bounded M closure(code_numeral M 3) ->
 sf_relation M SFAnd(code_numeral M(sf_encode source_def_empty))(representation_member_code M) rawbody ->
 sf_relation M SFEx rawbody(zeroM M) rawex ->sf_relation M SFImpl closure rawex middle ->
 sf_relation M SFImpl succ middle law ->
 sf_relation M SFAnd(representation_member_code M) rep targetbody ->
 sf_relation M SFEx targetbody(zeroM M) targetex ->sf_relation M SFImpl closure targetex targetmiddle ->
 sf_relation M SFImpl succ targetmiddle result ->source_zfr_provable M result.
Proof.
 intros HR HLaw BS BC HRaw HRawEx HMiddle HOuter HTarget HTargetEx HTargetMiddle HResult.
 destruct(sf_relation_total M SFImpl rawbody targetbody)as(point&HPoint).
 destruct(sf_relation_total M SFImpl rawex targetex)as(map&HMap).
 assert(BR:source_bounded M rep(code_numeral M 4)).
 { apply(source_bounded_monotone M rep(code_numeral M 2)(code_numeral M 4)
   (source_representation_recipe_bounded M n(zeroM M) rep(source_bounded_accept_falsity M n) HR)).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BE:source_bounded M(code_numeral M(sf_encode source_def_empty))(code_numeral M 4)).
 { apply(source_bounded_monotone M _(code_numeral M 1)(code_numeral M 4)(numerical_def_empty_bound M)).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(BM:source_bounded M(representation_member_code M)(code_numeral M 4)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)
    (representation_member_code M)(code_numeral M 4)(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 pose proof(proj2(source_bounded_accept_binary M SFAnd _ _ rawbody(code_numeral M 4)
   (or_introl eq_refl) HRaw)(conj BE BM))as BRaw.
 pose proof(proj2(source_bounded_accept_binary M SFAnd _ _ targetbody(code_numeral M 4)
   (or_introl eq_refl) HTarget)(conj BM BR))as BTarget.
 pose proof(source_descriptor_exists_map M ZFRSourceDescriptor rawbody targetbody rawex targetex point map
   (code_numeral M 3) BRaw BTarget HRawEx HTargetEx HPoint HMap
   (source_descriptor_falsity_pair_point M ZFRSourceDescriptor n rep rawbody targetbody point HR HRaw HTarget HPoint))as PMap.
 pose proof(proj2(source_zfr_descriptor_provable M law)(source_zfr_closure_empty M rho law HLaw))as PLaw.
 set(env:=fun i=>match i with 0=>succ|1=>closure|2=>rawex|_=>targetex end).
 assert(BRawEx:source_bounded M rawex(code_numeral M 3)).
 { exact(proj2(source_bounded_accept_unary M SFEx rawbody rawex(code_numeral M 3)(or_intror eq_refl) HRawEx) BRaw). }
 assert(BTargetEx:source_bounded M targetex(code_numeral M 3)).
 { exact(proj2(source_bounded_accept_unary M SFEx targetbody targetex(code_numeral M 3)(or_intror eq_refl) HTargetEx) BTarget). }
 assert(P:source_prop_program
   [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2));SPTImpl(SPTSlot 2)(SPTSlot 3)]
   (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3)))).
 { apply SPTII,SPTII. eapply SPTIE;[apply SPTCtx;cbn;auto|].
   eapply SPTIE;[eapply SPTIE;apply SPTCtx;cbn;auto|apply SPTCtx;cbn;auto]. }
 apply(proj1(source_zfr_descriptor_provable M result)).
 apply(source_descriptor_prop_program M ZFRSourceDescriptor _ _ P env(code_numeral M 3) result).
 - intros[|[|[|i]]];cbn[env];assumption.
 - intros p[<-|[<-|[]]] f HF.
   + assert(HMiddleGraph:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 2))) middle).
     { exact(proj2(schema_expression_graph M env SFImpl(CEvar 1)(CEvar 2) _ _ middle eq_refl eq_refl) HMiddle). }
     assert(HGraph:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))) law).
     { exact(proj2(schema_expression_graph M env SFImpl(CEvar 0) _ _ _ law eq_refl HMiddleGraph) HOuter). }
     rewrite(code_relation_functional M _ env f law HF HGraph). exact PLaw.
   + assert(HGraph:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 2)(SPTSlot 3))) map).
     { exact(proj2(schema_expression_graph M env SFImpl(CEvar 2)(CEvar 3) _ _ map eq_refl eq_refl) HMap). }
     rewrite(code_relation_functional M _ env f map HF HGraph). exact PMap.
 - assert(HMiddleGraph:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 3))) targetmiddle).
   { exact(proj2(schema_expression_graph M env SFImpl(CEvar 1)(CEvar 3) _ _ targetmiddle eq_refl eq_refl) HTargetMiddle). }
   exact(proj2(schema_expression_graph M env SFImpl(CEvar 0) _ _ _ result eq_refl HMiddleGraph) HResult).
Qed.
Print Assumptions source_descriptor_falsity_pair_point.
Print Assumptions source_zfr_representation_falsity_closure.
