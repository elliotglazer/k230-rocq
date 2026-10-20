(** Actual open-proof relativization with an internally finite domain table.
 The target axiom context is collected by PA induction; its length need not be standard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalTheories NumericalContexts NumericalSourceFull ContextCombination
 SourceBounded SourceAxiomContexts SourceDescriptorProvability SourceDescriptorRelativeTransfer SourceRelativization
 SourceImageContextWitnesses SourceContextImages SourceRelativeFullTranslation SourceRelativeContexts SourceDomainContexts
 SourceContextTransport SourceProofWeakening SourceHypothesisTransport SourceClosedContextShift SourceTraceBounds.
Unset Implicit Arguments.
Theorem source_descriptor_open_relative_proof_transfer M S T domain f relative:
 source_bounded M domain(code_numeral M 1) ->source_descriptor_relative_axiom_images M S T domain ->
 source_relativization M domain f relative ->source_descriptor_provable M S f ->
 exists bound tb tc tn,source_axiom_context M T tb tc tn /\
 forall k db dc ub uc un,coding_lt M bound(succM M k) ->source_domain_context M domain k db dc ->
 context_union M tb tc tn db dc k ub uc un ->source_full_prv M ub uc un relative.
Proof.
 intros HD HImages HRel(sb&sc&sn&HC&PSource).
 destruct(source_axiom_image_context_collect_from_witnesses M T domain sb sc sn)as(tb&tc&tn&HT&HCompiled).
 { intros f0 HF. destruct(HImages f0(proj2 HC f0 HF)(proj1 HC f0 HF))as(g&HG&gb&gc&gn&HGC&PG).
   exists g,gb,gc,gn. auto. }
 destruct(source_full_relativized_proof M domain HD sb sc sn f PSource)as(bound&HTranslate).
 exists bound,tb,tc,tn. split;[exact HT|]. intros k db dc ub uc un HK HTable HUnion.
 assert(BUnion:context_bounded M ub uc un k).
 { apply(source_context_union_bounded M tb tc tn db dc k ub uc un k HUnion).
   - exact(context_bounded_monotone M tb tc tn(zeroM M)k(proj1 HT)(coding_zero_lt_succ M k)).
   - exact(source_domain_context_bounded M domain k db dc HD HTable). }
 destruct(source_relative_context_total M domain sb sc sn k)as(rb&rc&rn&HRelative).
 pose proof(HTranslate k rb rc rn relative HK HRelative HRel)as PRelative.
 apply(source_full_prv_replace_hypotheses M ub uc un(ex_intro _ k BUnion)rn rb rc relative PRelative).
 intros h HH. apply(proj1(source_relative_context_member_iff M domain sb sc sn k rb rc rn h HRelative))in HH.
 destruct HH as[(f0&HF&HR)|HDom].
 - exact(source_full_prv_weaken_bounded M tb tc tn ub uc un h k(HCompiled f0 h HF HR)
    (context_union_left M tb tc tn db dc k ub uc un HUnion)BUnion).
 - assert(HMember:context_member M ub uc un h).
   { apply(context_union_right M tb tc tn db dc k ub uc un HUnion).
     exact(proj2(source_domain_context_member_iff M domain k db dc h HTable)HDom). }
   apply full_source_Ctx;[|exact HMember]. exists k. split;[exact(BUnion h HMember)|exact BUnion].
Qed.
Print Assumptions source_descriptor_open_relative_proof_transfer.
