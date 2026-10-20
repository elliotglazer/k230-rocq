(** Actual two-premise universal proof maps, used when combining two
    representations under the same assignment guard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
 SourceBounded SchemaConstructorBounds SourceDescriptorProvability SourceDescriptorClosure
 SourceDescriptorUniversalMap SourceUniversalDistribution SourceDescriptorPrograms SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_descriptor_implication_transitive M T a b c ab bc ac k :
 source_bounded M a k ->source_bounded M b k ->source_bounded M c k ->
 sf_relation M SFImpl a b ab ->sf_relation M SFImpl b c bc ->sf_relation M SFImpl a c ac ->
 source_descriptor_provable M T ab ->source_descriptor_provable M T bc ->source_descriptor_provable M T ac.
Proof.
 intros BA BB BC HAB HBC HAC PAB PBC. set(rho:=schema_env3 a b c).
 assert(P:source_prop_program [SPTImpl(SPTSlot 0)(SPTSlot 1);SPTImpl(SPTSlot 1)(SPTSlot 2)]
   (SPTImpl(SPTSlot 0)(SPTSlot 2))).
 { apply SPTII. eapply SPTIE;[apply SPTCtx;cbn;auto|]. eapply SPTIE;apply SPTCtx;cbn;auto. }
 apply(source_descriptor_prop_program M T _ _ P rho k ac).
 - intros[|[|i]];cbn[rho schema_env3];assumption.
 - intros p[<-|[<-|[]]] f HF.
   + assert(HG:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTSlot 1))) ab).
     { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(CEvar 1) a b ab eq_refl eq_refl) HAB). }
     now rewrite(code_relation_functional M _ rho f ab HF HG).
   + assert(HG:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 2))) bc).
     { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 1)(CEvar 2) b c bc eq_refl eq_refl) HBC). }
     now rewrite(code_relation_functional M _ rho f bc HF HG).
 - exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(CEvar 2) a c ac eq_refl eq_refl) HAC).
Qed.

Theorem source_descriptor_binary_universal_map M T a b c bc point qa qb qc qbc first second result k :
 source_bounded M a k ->source_bounded M b k ->source_bounded M c k ->
 sf_relation M SFImpl b c bc ->sf_relation M SFImpl a bc point ->
 sf_relation M SFAll a(zeroM M) qa ->sf_relation M SFAll b(zeroM M) qb ->
 sf_relation M SFAll c(zeroM M) qc ->sf_relation M SFAll bc(zeroM M) qbc ->
 sf_relation M SFImpl qa qbc first ->sf_relation M SFImpl qb qc second ->
 sf_relation M SFImpl qa second result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
 intros BA BB BC HBC HP HQA HQB HQC HQBC HFirst HSecond HResult PP.
 pose proof(proj2(source_bounded_accept_binary M SFImpl b c bc k(or_intror(or_intror eq_refl)) HBC)
   (conj BB BC))as BBC.
 pose proof(source_descriptor_universal_map M T a bc point qa qbc first k BA BBC HP HQA HQBC HFirst PP)as PFirst.
 destruct(sf_relation_total M SFImpl qbc second)as(distribution&HDistribution).
 pose proof(source_descriptor_provable_from_empty M T distribution
   (source_universal_distribution M b c bc qb qc qbc second distribution k BB BC HBC HQB HQC HQBC HSecond HDistribution))as PDistribution.
 apply(source_descriptor_implication_transitive M T qa qbc second first distribution result k
   (source_bounded_universal_from_matrix M a qa k BA HQA)
   (source_bounded_universal_from_matrix M bc qbc k BBC HQBC));try assumption.
 exact(proj2(source_bounded_accept_binary M SFImpl qb qc second k(or_intror(or_intror eq_refl)) HSecond)
   (conj(source_bounded_universal_from_matrix M b qb k BB HQB)(source_bounded_universal_from_matrix M c qc k BC HQC))).
Qed.

Theorem source_descriptor_binary_guard_map M T a b c guard bc point ga gb gc gbc result k :
 source_bounded M a k ->source_bounded M b k ->source_bounded M c k ->source_bounded M guard k ->
 sf_relation M SFImpl b c bc ->sf_relation M SFImpl a bc point ->
 sf_relation M SFImpl guard a ga ->sf_relation M SFImpl guard b gb ->sf_relation M SFImpl guard c gc ->
 sf_relation M SFImpl gb gc gbc ->sf_relation M SFImpl ga gbc result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
 intros BA BB BC BG HBC HP HGA HGB HGC HGBC HResult PP.
 set(rho:=fun i=>match i with 0=>a|1=>b|2=>c|_=>guard end).
 assert(P:source_prop_program [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))]
   (SPTImpl(SPTImpl(SPTSlot 3)(SPTSlot 0))
    (SPTImpl(SPTImpl(SPTSlot 3)(SPTSlot 1))(SPTImpl(SPTSlot 3)(SPTSlot 2))))).
 { apply SPTII,SPTII,SPTII. eapply SPTIE.
   - eapply SPTIE;[apply SPTCtx;cbn;auto|]. eapply SPTIE;apply SPTCtx;cbn;auto.
   - eapply SPTIE;apply SPTCtx;cbn;auto. }
 apply(source_descriptor_prop_program M T _ _ P rho k result).
 - intros[|[|[|i]]];cbn[rho];assumption.
 - intros p[<-|[]] f HF.
   assert(HBCG:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 2))) bc).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 1)(CEvar 2) b c bc eq_refl eq_refl) HBC). }
   assert(HG:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))) point).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0) _ a bc point eq_refl HBCG) HP). }
   now rewrite(code_relation_functional M _ rho f point HF HG).
 - assert(GA:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 3)(SPTSlot 0))) ga).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 3)(CEvar 0) guard a ga eq_refl eq_refl) HGA). }
   assert(GB:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 3)(SPTSlot 1))) gb).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 3)(CEvar 1) guard b gb eq_refl eq_refl) HGB). }
   assert(GC:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 3)(SPTSlot 2))) gc).
   { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 3)(CEvar 2) guard c gc eq_refl eq_refl) HGC). }
   pose proof(proj2(schema_expression_graph M rho SFImpl _ _ gb gc gbc GB GC) HGBC)as GBC.
   exact(proj2(schema_expression_graph M rho SFImpl _ _ ga gbc result GA GBC) HResult).
Qed.
Print Assumptions source_descriptor_implication_transitive.
Print Assumptions source_descriptor_binary_universal_map.
Print Assumptions source_descriptor_binary_guard_map.
