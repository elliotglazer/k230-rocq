(** A single-premise Dn map retaining a condition above every assignment
    slot. All proof operations are actual numerical source operations. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SchemaConstructorBounds SourceBounded
 SourceDn SourceDnBounds SourceRepresentationPadding SourceRepresentationPaddedDn SourceDnPaddedBinaryMap
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourcePropositionalTemplates SourceWitnessProofComposition.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_dn_padded_unary_map M count condition padded a b da db implication point inner result k:
 source_bounded M condition(succM M(succM M k))->
 source_bounded M a(addM M count(succM M(succM M k)))->source_bounded M b(addM M count(succM M(succM M k)))->
 source_representation_padding M count condition padded->source_dn M count a da->source_dn M count b db->
 sf_relation M SFImpl a b implication->sf_relation M SFImpl padded implication point->
 sf_relation M SFImpl da db inner->sf_relation M SFImpl condition inner result->
 source_zfr_provable M point->source_zfr_provable M result.
Proof.
 intros BC BA BB HPad HDA HDB HI HP HInner HResult PPoint.
 assert(BI:source_bounded M implication(addM M count(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl a b implication _(or_intror(or_intror eq_refl))HI)(conj BA BB)). }
 destruct(source_dn_total M count implication)as(di&HDI).
 destruct(sf_relation_total M SFImpl condition di)as(condProof&HCondProof).
 pose proof(source_descriptor_dn_padded_intro M ZFRSourceDescriptor count condition padded implication di k point condProof
  BC BI HPad HDI HP HCondProof(proj2(source_zfr_descriptor_provable M point)PPoint))as PCond.
 destruct(sf_relation_total M SFImpl di inner)as(distribution&HDistribution).
 pose proof(source_descriptor_dn_distribution M ZFRSourceDescriptor count a b implication da db di inner distribution k
  BA BB HI HDA HDB HDI HInner HDistribution)as PDistribution.
 assert(Program:source_prop_program[SPTImpl(SPTSlot 0)(SPTSlot 1);SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))]
  (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 3)))).
 { apply SPTII,SPTII. eapply SPTIE;[eapply SPTIE;[apply SPTCtx;cbn;auto|eapply SPTIE;apply SPTCtx;cbn;auto]|apply SPTCtx;now left]. }
 set(rho:=fun i:nat=>match i with 0=>condition|1=>di|2=>da|_=>db end).
 apply(source_zfr_prop_two M _ _ _ Program rho(succM M(succM M k))condProof distribution result).
 - intros[|[|[|i]]].
   + exact BC.
   + exact(source_dn_bounded M count implication di k HDI BI).
   + exact(source_dn_bounded M count a da k HDA BA).
   + exact(source_dn_bounded M count b db k HDB BB).
 - exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(CEvar 1)condition di condProof eq_refl eq_refl)HCondProof).
 - exact(proj2(schema_expression_graph M rho SFImpl(CEvar 1)(source_prop_expression(SPTImpl(SPTSlot 2)(SPTSlot 3)))di inner distribution eq_refl
   (proj2(schema_expression_graph M rho SFImpl(CEvar 2)(CEvar 3)da db inner eq_refl eq_refl)HInner))HDistribution).
 - exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(source_prop_expression(SPTImpl(SPTSlot 2)(SPTSlot 3)))condition inner result eq_refl
   (proj2(schema_expression_graph M rho SFImpl(CEvar 2)(CEvar 3)da db inner eq_refl eq_refl)HInner))HResult).
 - exact(proj1(source_zfr_descriptor_provable M condProof)PCond).
 - exact(proj1(source_zfr_descriptor_provable M distribution)PDistribution).
Qed.
Print Assumptions source_zfr_dn_padded_unary_map.
