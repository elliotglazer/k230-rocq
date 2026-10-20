(** Quantifier instantiation in the combined context.  Its D(t) premise is
    proved by Ctx from the actual domain table, whenever t is below k. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalContexts SourceBounded SourceSequents NumericalInstantiation NumericalSourceFull
  SourceDomainInstances SourceRelativeContexts SourceRelativization
  SourceRelativizedInstantiation.
Unset Implicit Arguments.

Theorem source_relative_domain_hyp M domain b c n k u v l t dt :
  source_bounded M domain (code_numeral M 1) -> context_bounded M b c n k ->
  source_relative_context M domain b c n k u v l ->
  coding_lt M t k -> numerical_instantiation M domain t dt ->
  source_full_prv M u v l dt.
Proof.
  intros HD HC HR HT HInst. apply full_source_Ctx.
  - exists k. split.
    + exact (source_domain_instance_bound M domain t dt k HD HT HInst).
    + exact (source_relative_context_bounded M domain b c n k u v l HD HC HR).
  - apply (proj2 (source_relative_context_member_iff M domain b c n k u v l dt HR)).
    right. exists t. auto.
Qed.

Theorem source_relative_AllE M domain b c n k u v l a f t g rf rg :
  source_bounded M domain (code_numeral M 1) -> context_bounded M b c n k ->
  source_relative_context M domain b c n k u v l -> coding_lt M t k ->
  sf_relation M SFAll a (zeroM M) f -> numerical_instantiation M a t g ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  source_full_prv M u v l rf -> source_full_prv M u v l rg.
Proof.
  intros HD HC HR HT HF HG HRF HRG PF.
  destruct (numerical_instantiation_total M domain t) as [dt HDT].
  exact (source_relativized_AllE M domain a f t g rf rg dt u v l HD HF HG HRF HRG HDT PF
    (source_relative_domain_hyp M domain b c n k u v l t dt HD HC HR HT HDT)).
Qed.

Theorem source_relative_ExI M domain b c n k u v l a f t g rf rg :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M f k -> context_bounded M b c n k ->
  source_relative_context M domain b c n k u v l -> coding_lt M t k ->
  sf_relation M SFEx a (zeroM M) f -> numerical_instantiation M a t g ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  source_full_prv M u v l rg -> source_full_prv M u v l rf.
Proof.
  intros HD HB HC HR HT HF HG HRF HRG PG.
  destruct (numerical_instantiation_total M domain t) as [dt HDT].
  exact (source_relativized_ExI M domain a f t g rf rg dt u v l k HD HB
    (source_relative_context_bounded M domain b c n k u v l HD HC HR)
    HF HG HRF HRG HDT PG
    (source_relative_domain_hyp M domain b c n k u v l t dt HD HC HR HT HDT)).
Qed.

Print Assumptions source_relative_domain_hyp.
Print Assumptions source_relative_AllE.
Print Assumptions source_relative_ExI.
