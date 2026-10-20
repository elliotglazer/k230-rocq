(** Binary Dn proof transport with an arbitrary exterior condition. The
    condition is padded above all assignment slots, so extra representative
    witnesses are retained outside the guarded quantifiers. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceDn SourceDnBounds
 SourceDnBinaryProofMap SourceRepresentationPadding SourceRepresentationPaddedDn
 SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_descriptor_dn_distribution M T count a b implication da db dimp inner result k :
 source_bounded M a(addM M count(succM M(succM M k))) ->
 source_bounded M b(addM M count(succM M(succM M k))) ->
 sf_relation M SFImpl a b implication ->source_dn M count a da ->source_dn M count b db ->
 source_dn M count implication dimp ->sf_relation M SFImpl da db inner ->
 sf_relation M SFImpl dimp inner result ->source_descriptor_provable M T result.
Proof.
 intros BA BB HImp HDA HDB HDI HInner HResult.
 assert(BImp:source_bounded M implication(addM M count(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl a b implication _
    (or_intror(or_intror eq_refl)) HImp)(conj BA BB)). }
 destruct(sf_relation_total M SFImpl implication implication)as(identity&HIdentity).
 assert(PIdentity:source_descriptor_provable M T identity).
 { assert(P:source_prop_program[](SPTImpl(SPTSlot 0)(SPTSlot 0))).
   { apply SPTII,SPTCtx. now left. }
   apply(source_descriptor_prop_program M T _ _ P(fun _=>implication)
      (addM M count(succM M(succM M k))) identity).
   - intro i. exact BImp.
   - intros p H. contradiction.
   - exact(proj2(schema_expression_graph M(fun _=>implication) SFImpl(CEvar 0)(CEvar 0)
       implication implication identity eq_refl eq_refl) HIdentity). }
 exact(source_descriptor_dn_binary_map M T count implication a b dimp da db k implication identity
   inner result BImp BA BB HDI HDA HDB HImp HIdentity HInner HResult PIdentity).
Qed.

Theorem source_descriptor_dn_padded_binary_map M T count condition padded a b c da db dc
 bc point proof targetbc targetbody result k :
 source_bounded M condition(succM M(succM M k)) ->
 source_bounded M a(addM M count(succM M(succM M k))) ->
 source_bounded M b(addM M count(succM M(succM M k))) ->
 source_bounded M c(addM M count(succM M(succM M k))) ->
 source_representation_padding M count condition padded ->
 source_dn M count a da ->source_dn M count b db ->source_dn M count c dc ->
 sf_relation M SFImpl b c bc ->sf_relation M SFImpl a bc point ->
 sf_relation M SFImpl padded point proof ->sf_relation M SFImpl db dc targetbc ->
 sf_relation M SFImpl da targetbc targetbody ->sf_relation M SFImpl condition targetbody result ->
 source_descriptor_provable M T proof ->source_descriptor_provable M T result.
Proof.
 intros BCond BA BB BC HPad HDA HDB HDC HBC HP HProof HTBC HTBody HResult PProof.
 assert(BBC:source_bounded M bc(addM M count(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl b c bc _
   (or_intror(or_intror eq_refl)) HBC)(conj BB BC)). }
 assert(BPoint:source_bounded M point(addM M count(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl a bc point _
   (or_intror(or_intror eq_refl)) HP)(conj BA BBC)). }
 destruct(source_dn_total M count bc)as(dbc&HDBC).
 destruct(source_dn_total M count point)as(dp&HDP).
 destruct(sf_relation_total M SFImpl condition dp)as(condProof&HCondProof).
 pose proof(source_descriptor_dn_padded_intro M T count condition padded point dp k proof condProof
   BCond BPoint HPad HDP HProof HCondProof PProof)as PCond.
 destruct(sf_relation_total M SFImpl da dbc)as(daImp&HDAImp).
 destruct(sf_relation_total M SFImpl dp daImp)as(first&HFirst).
 pose proof(source_descriptor_dn_distribution M T count a bc point da dbc dp daImp first k
   BA BBC HP HDA HDBC HDP HDAImp HFirst)as PFirst.
 destruct(sf_relation_total M SFImpl dbc targetbc)as(second&HSecond).
 pose proof(source_descriptor_dn_distribution M T count b c bc db dc dbc targetbc second k
   BB BC HBC HDB HDC HDBC HTBC HSecond)as PSecond.
 set(rho:=fun i=>match i with 0=>condition|1=>dp|2=>da|3=>dbc|4=>db|_=>dc end).
 assert(P:source_prop_program
  [SPTImpl(SPTSlot 0)(SPTSlot 1);SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3));
   SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))]
  (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5))))).
 { apply SPTII,SPTII,SPTII.
   eapply SPTIE with(a:=SPTSlot 4);[|apply SPTCtx;cbn;auto 12].
   eapply SPTIE with(a:=SPTSlot 3);[apply SPTCtx;cbn;auto 12|].
   eapply SPTIE with(a:=SPTSlot 2);[|apply SPTCtx;cbn;auto 12].
   eapply SPTIE with(a:=SPTSlot 1);[apply SPTCtx;cbn;auto 12|].
   eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 12. }
 assert(GCond:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTSlot 1)))condProof).
 { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(CEvar 1) condition dp condProof eq_refl eq_refl) HCondProof). }
 assert(GDA:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 2)(SPTSlot 3)))daImp).
 { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 2)(CEvar 3) da dbc daImp eq_refl eq_refl) HDAImp). }
 assert(GFirst:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))))first).
 { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 1) _ dp daImp first eq_refl GDA) HFirst). }
 assert(GTBC:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 4)(SPTSlot 5)))targetbc).
 { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 4)(CEvar 5) db dc targetbc eq_refl eq_refl) HTBC). }
 assert(GSecond:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))))second).
 { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 3) _ dbc targetbc second eq_refl GTBC) HSecond). }
 apply(source_descriptor_prop_program M T _ _ P rho(succM M(succM M k))result).
 - intros[|[|[|[|[|i]]]]];cbn[rho];try assumption;eapply source_dn_bounded;eassumption.
 - intros p[<-|[<-|[<-|[]]]] f HF.
   + rewrite(code_relation_functional M _ rho f condProof HF GCond). exact PCond.
   + rewrite(code_relation_functional M _ rho f first HF GFirst). exact PFirst.
   + rewrite(code_relation_functional M _ rho f second HF GSecond). exact PSecond.
 - assert(GBody:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 5))))targetbody).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 2) _ da targetbc targetbody eq_refl GTBC) HTBody). }
   exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0) _ condition targetbody result eq_refl GBody) HResult).
Qed.
Print Assumptions source_descriptor_dn_distribution.
Print Assumptions source_descriptor_dn_padded_binary_map.
